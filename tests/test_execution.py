"""Exercise watchdog deadlines, job trees and effective resource controls on Linux."""

from __future__ import annotations

import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

from k3batch.execution import JobResult, LocalBackend, LocalJob
from k3batch.memory import CgroupGuard, MemoryGuard, PollingGuard, choose_guard
from k3batch.model import Limits

from .test_cli import still_runs


@unittest.skipUnless(sys.platform == "linux", "requires the Linux job watchdog")
class LocalExecution(unittest.TestCase):
    guard_class: type[MemoryGuard] = PollingGuard

    def setUp(self) -> None:
        self.directory = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.backend = self.enterContext(LocalBackend(self.guard_class(), 128, 2))
        self.log = self.directory / "job.log"

    def run_job(self, program: str, *, timeout: float = 5) -> tuple[LocalJob, JobResult]:
        job = self.backend.start([sys.executable, "-c", program], Limits(timeout, 96), self.log)
        self.addCleanup(self.backend.cancel, job)
        deadline = time.monotonic() + 10
        while (outcome := self.backend.observe(job)) is None:
            self.assertLess(time.monotonic(), deadline, "watchdog never completed")
            time.sleep(0.02)
        return job, outcome

    def test_job_tree_is_cleaned_when_the_leader_finishes(self) -> None:
        job, result = self.run_job(
            "import subprocess,sys; print(subprocess.Popen([sys.executable, '-c',"
            " 'import time; time.sleep(20)']).pid, flush=True)"
        )
        self.assertEqual(result.returncode, 0)
        self.assertFalse(still_runs(int(self.log.read_text())))
        self.assertFalse(Path(job.temporary.name).exists())
        control = result.data["effective"]
        if isinstance(self.backend.guard, CgroupGuard):
            self.assertEqual(control, {"memory_bytes": 96 * 1024**2, "swap_bytes": 0, "cpu_cores": 2})
            self.assertEqual(result.data["effective_run"]["memory_bytes"], 128 * 1024**2)
            self.assertEqual(result.data["cgroup_memory_events"]["oom"], 0)
            self.assertGreater(result.data["cgroup_memory_peak_bytes"], 0)
        else:
            self.assertIsNone(control)
            self.assertIn("peak_sampled_bytes", result.data)

    def test_wall_deadline_runs_while_the_coordinator_does_other_work(self) -> None:
        program = (
            "import subprocess,sys,time; print(subprocess.Popen([sys.executable, '-c',"
            " 'import time; time.sleep(20)']).pid, flush=True); time.sleep(20)"
        )
        job = self.backend.start([sys.executable, "-c", program], Limits(0.8, 96), self.log)
        self.addCleanup(self.backend.cancel, job)
        # The watchdog finishes without an observe call, as when the scheduler is syncing a record.
        job.process.wait(timeout=4)
        time.sleep(0.2)
        result = self.backend.observe(job)
        assert result is not None
        self.assertEqual(result.verdict, "timeout")
        self.assertEqual(result.returncode, -signal.SIGKILL)
        self.assertLess(result.wall_seconds, time.monotonic() - job.started - 0.1)
        self.assertFalse(still_runs(int(self.log.read_text())))

    def test_owner_death_cancels_the_job_tree(self) -> None:
        runner = (
            "import os,subprocess,sys,time; print(os.getpid(), "
            "subprocess.Popen([sys.executable,'-c','import time; time.sleep(20)']).pid, "
            "flush=True); time.sleep(20)"
        )
        owner_script = """
import sys, time
from pathlib import Path
from k3batch.execution import LocalBackend
from k3batch.memory import choose_guard
from k3batch.model import Limits

with LocalBackend(choose_guard(sys.argv[1]), 128, 2) as backend:
    job = backend.start([sys.executable, "-c", sys.argv[3]], Limits(5, 96), Path(sys.argv[2]))
    while backend.observe(job) is None:
        time.sleep(0.02)
"""
        with subprocess.Popen(
            [sys.executable, "-c", owner_script, self.backend.guard.name, str(self.log), runner]
        ) as owner:
            try:
                ready_by = time.monotonic() + 5
                while not self.log.is_file() or not self.log.stat().st_size:
                    self.assertIsNone(owner.poll(), "coordinator exited before the job started")
                    self.assertLess(time.monotonic(), ready_by, "job failed to start")
                    time.sleep(0.02)
                pids = [int(pid) for pid in self.log.read_text().split()]
                self.assertEqual(len(pids), 2)
            finally:
                owner.kill()
                owner.wait(timeout=3)
        stopped_by = time.monotonic() + 3
        while any(still_runs(pid) for pid in pids):
            self.assertLess(time.monotonic(), stopped_by, "a job process outlived its coordinator")
            time.sleep(0.02)

    def test_planner_stderr_is_separate_and_output_files_are_bounded(self) -> None:
        command = [
            sys.executable,
            "-c",
            "import sys; print('metadata'); print('diagnostic', file=sys.stderr)",
        ]
        result = self.backend.execute(command, 5)
        self.assertEqual((result.stdout, result.stderr), ("metadata\n", "diagnostic\n"))
        with patch("k3batch.execution.FILE_BYTES", 4096):
            result = self.backend.execute(["/usr/bin/head", "-c", "8192", "/dev/zero"], 5)
        self.assertNotEqual(result.returncode, 0)
        self.assertLessEqual(len(result.stdout), 4096)

    def test_scratch_sampling_stops_writes_across_multiple_small_files(self) -> None:
        with patch("k3batch.execution.SCRATCH_BYTES", 8192):
            _, result = self.run_job(
                "import pathlib,tempfile,time; root = pathlib.Path(tempfile.gettempdir()); "
                "[(root / str(i)).write_bytes(b'1' * 4096) for i in range(3)]; time.sleep(20)"
            )
        self.assertEqual(result.verdict, "scratch")

    def test_nonfinite_deadline_is_refused(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "finite positive"):
            self.backend.execute(["/bin/echo", "example"], float("nan"))

    def test_external_signal_has_no_confirmed_cgroup_oom(self) -> None:
        _, result = self.run_job("import os,signal; os.kill(os.getpid(), signal.SIGKILL)")
        self.assertEqual(result.returncode, -signal.SIGKILL)
        self.assertIsNone(result.verdict)


@unittest.skipUnless(CgroupGuard.available(), "needs a capable systemd user cgroup manager")
class CgroupExecution(LocalExecution):
    guard_class = CgroupGuard

    def test_cgroup_oom_has_local_and_process_kill_evidence(self) -> None:
        _, result = self.run_job("import time; buffer = bytearray(180 * 1024**2); time.sleep(5)")
        self.assertEqual(result.verdict, "memory")
        self.assertGreater(result.data["cgroup_memory_events"]["oom"], 0)
        self.assertGreater(result.data["cgroup_memory_events"]["oom_kill"], 0)
        self.assertLessEqual(result.data["cgroup_memory_peak_bytes"], 96 * 1024**2)


class GuardSelection(unittest.TestCase):
    def test_explicit_cgroup_mode_fails_without_required_controllers(self) -> None:
        with patch.object(CgroupGuard, "available", return_value=False):
            with self.assertRaisesRegex(RuntimeError, "delegated cgroup v2"):
                choose_guard("cgroup")
            self.assertIsInstance(choose_guard("auto"), PollingGuard)
