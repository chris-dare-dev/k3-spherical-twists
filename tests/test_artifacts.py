"""Artifact registry recovery and fresh-process reconstruction in Macaulay2."""

from __future__ import annotations

import json
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
from unittest.mock import patch

from k3batch.artifacts import ArtifactError, ArtifactStore, read_artifact_json

MODEL = {
    "version": 1,
    "kind": "k3-model",
    "payload": {"parameters": {}, "coordinates": [], "grading": [], "equations": [], "markings": {}},
}


def body(data: dict) -> bytes:
    return (json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n").encode()


class ArtifactRegistry(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.store = ArtifactStore(Path(temporary.name))

    def test_interruption_and_concurrent_publication(self) -> None:
        expected = sha256(body(MODEL)).hexdigest()
        self.store.objects.mkdir()
        (self.store.objects / ".part-crash").write_bytes(b"partial")
        with (
            patch("k3batch.artifacts.os.link", side_effect=OSError("link interrupted")),
            self.assertRaisesRegex(OSError, "link interrupted"),
        ):
            self.store.publish(MODEL, "interrupted-before-link")
        self.assertFalse((self.store.objects / f"{expected}.json").exists())
        publish_file = self.store._publish_file

        def stop_after_link(digest: str, content: bytes) -> None:
            publish_file(digest, content)
            raise KeyboardInterrupt

        with (
            patch.object(self.store, "_publish_file", side_effect=stop_after_link),
            self.assertRaises(KeyboardInterrupt),
        ):
            self.store.publish(MODEL, "interrupted-before-registration")
        self.assertEqual((self.store.objects / f"{expected}.json").read_bytes(), body(MODEL))
        with self.assertRaisesRegex(ArtifactError, "not registered"):
            self.store.read(expected)

        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(lambda attempt: self.store.publish(MODEL, attempt), ("first", "second")))
        self.assertEqual(results, [expected, expected])
        self.assertEqual(self.store.publish(MODEL, "first"), expected)
        self.assertEqual(self.store.read(expected), body(MODEL))
        connection = sqlite3.connect(self.store.database)
        try:
            self.assertEqual(
                connection.execute("SELECT * FROM artifact").fetchall(),
                [(expected, len(body(MODEL)), 1, "k3-model", None)],
            )
            self.assertEqual(
                connection.execute("SELECT attempt FROM producer ORDER BY attempt").fetchall(),
                [("first",), ("second",)],
            )
        finally:
            connection.close()
        self.assertEqual(
            sorted(p.name for p in self.store.objects.iterdir()), [".part-crash", f"{expected}.json"]
        )

    def test_damaged_model_and_wrong_parent_kind(self) -> None:
        digest = self.store.publish(MODEL, "run")
        presentation = {
            "version": 1,
            "kind": "graded-presentation",
            "payload": {"model_digest": digest, "source": [], "target": [], "matrix": []},
        }
        presentation_digest = self.store.publish(presentation, "run")
        self.assertEqual(self.store.read(presentation_digest), body(presentation))
        presentation["payload"]["model_digest"] = presentation_digest
        with self.assertRaisesRegex(ArtifactError, "not a K3 model"):
            self.store.publish(presentation, "run")
        (self.store.objects / f"{digest}.json").write_bytes(body(MODEL).replace(b"markings", b"markingX"))
        with self.assertRaisesRegex(ArtifactError, "failed digest verification"):
            self.store.read(presentation_digest)
        with self.assertRaisesRegex(ArtifactError, "failed digest verification"):
            self.store.publish(MODEL, "run")

    def test_cli_publishes_and_reads_canonical_bytes(self) -> None:
        directory = self.store.database.parent
        raw = directory / "model.json"
        raw.write_text(json.dumps(MODEL, indent=2), encoding="utf-8")

        def invoke(*args: str) -> bytes:
            return subprocess.check_output([sys.executable, "-m", "k3batch", *args], timeout=15)

        digest = invoke("publish-artifact", str(directory), str(raw), "--producer", "run-1").decode().strip()
        self.assertEqual(invoke("read-artifact", str(directory), digest), body(MODEL))

    def test_version_two_is_specific_to_complexes(self) -> None:
        model = self.store.publish(MODEL, "model")
        presentation = {
            "version": 2,
            "kind": "graded-presentation",
            "payload": {"model_digest": model, "source": [], "target": [], "matrix": []},
        }
        with self.assertRaisesRegex(ArtifactError, "unknown artifact version"):
            self.store.publish(MODEL | {"version": 2}, "model")
        with self.assertRaisesRegex(ArtifactError, "unknown artifact version"):
            self.store.publish(presentation, "presentation")


@unittest.skipUnless(shutil.which("M2"), "Macaulay2 is not installed")
class Macaulay2ArtifactRoundTrip(unittest.TestCase):
    def test_marked_model_kernel_bundle_and_cones(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        store = ArtifactStore(directory / "store")

        def run_m2(name: str, code: str) -> None:
            script = directory / f"{name}.m2"
            script.write_text(
                'path = prepend("./", path); needsPackage "K3Twists"; needsPackage "JSON"; '
                'needsPackage "Complexes";\n'
                f"outDir = {json.dumps(str(directory) + '/')};\n"
                'emitData = (name, D) -> (outDir | name | ".json") << toJSON D << close;\n'
                'readData = name -> fromJSON get(outDir | name | ".json");\n' + code,
                encoding="utf-8",
            )
            finished = subprocess.run(
                ["M2", "--script", str(script)], capture_output=True, text=True, timeout=40
            )
            self.assertEqual(finished.returncode, 0, finished.stdout + finished.stderr)

        run_m2(
            "write-model",
            """
            K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_conic"};
            emitData("raw-model", k3ModelArtifact K);
            """,
        )

        def register(name: str) -> str:
            data = read_artifact_json((directory / f"raw-{name}.json").read_bytes())
            digest = store.publish(data, f"compute-{name}")
            (directory / f"{name}.json").write_bytes(store.read(digest))
            return digest

        model = register("model")
        run_m2(
            "write-presentation-and-complex",
            f"""
            portable = readData "model";
            K = realizeK3Surface k3Recipe hashTable {{"family" => "quartic_with_conic"}};
            bindK3ModelArtifact(K, portable, "{model}");
            assert(divisorPairing(K#"polarization", markedCurveClass K) === 2);
            assert(k3ModelArtifact K === readData "model");
            R = K#"ring";
            emitData("raw-presentation", gradedPresentationArtifact(K, module kernelBundle K, "{model}"));
            C = complex({{map(R^{{1}}, R^4, vars R)}}, Base => -2);
            emitData("raw-complex", gradedComplexArtifact(K, C, "{model}"));
            E = complex {{map(R^1, R^1, 1), map(R^1, R^1, 0)}};
            emitData("raw-three-term", gradedComplexArtifact(K, E, "{model}"));
            W = twistWord {{twistStep(sphericalObject structureObject K, 1)}};
            P = realizeTwistImage applyWord(W, catalogueObject(K, "O_x"));
            assert(P#"status" === "realized");
            assert(not isFreeModule (P#"complex")_0);
            emitData("raw-point-cone", gradedComplexArtifact(K, P#"complex", "{model}"));
            """,
        )
        register("presentation")
        register("complex")
        register("three-term")
        register("point-cone")
        run_m2(
            "reload",
            f"""
            K = loadK3ModelArtifact(readData "model", "{model}");
            P = readData "presentation";
            F = sheaf loadGradedPresentation(K, P);
            assert({{rank F, cohomologyDims F}} === {{3,{{0,0,4}}}});
            Q = readData "complex";
            assert(Q#"version" === 1 and Q#"payload"#"terms" === {{{{-1}},{{0,0,0,0}}}});
            C = loadGradedComplex(K, Q);
            assert(concentration C === (-2,-1));
            assert(HH_(-2) C != 0 and sheaf HH_(-2) C == 0);
            assert(cohomologyDims sheaf HH_(-1) C === {{0,0,4}});
            R = K#"ring";
            assert(sheaf HH_(-1) C == kernelBundle K);
            assert(gradedComplexArtifact(K, C, "{model}") === Q);
            other = loadK3ModelArtifact(readData "model", concatenate toList(64:"f"));
            assert(try (loadGradedPresentation(other, P); false) else true);
            assert(try (gradedPresentationArtifact(other, module F, "{model}"); false) else true);
            editPayload = (envelope, key, item) -> merge(envelope, hashTable {{
                "payload" => merge(envelope#"payload", hashTable {{key => item}}, (a,b) -> b)
                }}, (a,b) -> b);
            assert(try (loadGradedComplex(K, editPayload(Q, "differentials", {{}})); false) else true);
            wrongShifts = {{{{0}},{{0,0,0,0}}}};
            assert(try (loadGradedComplex(K, editPayload(Q, "terms", wrongShifts)); false) else true);
            T = readData "three-term";
            assert(isWellDefined loadGradedComplex(K, T));
            nonzero = first select(T#"payload"#"differentials", a -> a#0#0 =!= {{}});
            assert(try (loadGradedComplex(K, editPayload(T, "differentials", {{nonzero,nonzero}})); false)
                else true);

            pointData = readData "point-cone";
            assert(pointData#"version" === 2);
            pointCone = loadGradedComplex(K, pointData);
            assert(concentration pointCone === (0,1) and isWellDefined pointCone);
            assert(degrees pointCone_0 === {{{{0}}}} and degrees pointCone_1 === {{{{0}}}});
            assert(pointCone_0 == module pointSheaf K and isFreeModule pointCone_1);
            assert(degree (pointCone.dd)_1 === {{0}} and ((pointCone.dd)_1)_(0,0) == 1_R);
            shiftedIdeal = complex(module pointIdealSheaf K, Base => 1);
            assert(HH_1 pointCone == HH_1 shiftedIdeal and HH_0 pointCone == 0);
            assert(sheaf HH_1 pointCone == pointIdealSheaf K and sheaf HH_0 pointCone == 0);
            assert(cohomologyDims sheaf HH_1 pointCone === {{0,0,1}});
            assert(gradedComplexArtifact(K, pointCone, "{model}") === pointData);
            assert(try (loadGradedComplex(other, pointData); false) else true);

            x0 = (vars R)_(0,0);
            x1 = (vars R)_(0,1);
            A = coker map(R^1, R^{{-1}}, {{{{x1}}}});
            B = coker map(R^1, R^{{-2}}, {{{{x0*x1}}}});
            ontoA = map(A, B, {{{{1_R}}}});
            intoB = map(B, R^{{-1}}, {{{{x1}}}});
            E = complex({{ontoA, intoB}}, Base => -1);
            data = gradedComplexArtifact(K, E, "{model}");
            loaded = loadGradedComplex(K, data);
            assert(concentration loaded === (-1,1) and isWellDefined loaded);
            -- The lifts compose to x1. The composition is zero in the target quotient.
            assert(matrix ((loaded.dd)_0) * matrix ((loaded.dd)_1) != 0);
            diffs = data#"payload"#"differentials";
            linear = {{{{{{1,0,0,0}}, 1}}}};
            linearMap = {{{{linear}}}};
            badDegree = editPayload(data, "differentials", {{linearMap, last diffs}});
            badSquare = editPayload(data, "differentials", {{first diffs, linearMap}});
            termData = data#"payload"#"terms";
            x0Term = hashTable {{"source" => {{1}}, "target" => {{0}}, "matrix" => linearMap}};
            badDescent = editPayload(data, "terms", {{first termData, x0Term, last termData}});
            scan({{badDegree, badSquare, badDescent}}, bad ->
                assert(try (loadGradedComplex(K, bad); false) else true));
            """,
        )
