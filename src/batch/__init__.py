"""Runs the computations of the Macaulay2 package in batches, and keeps the evidence.

One Macaulay2 process per task, under time and memory limits; one record per attempt; the claim tables
from the records that are committed.  The mathematics lives in src/macaulay2.  This package knows only
that its runner script can expand a batch description into tasks and compute one task.

Its boxes, lowest first; each imports only boxes above it in this list, through their __init__.py
(.github/check_boxes.py checks it):

    tasks       the batch file, the tasks it expands to, the limits they run under
    jobs        one process on Linux under a time and memory limit, watched from outside
    runner      the Macaulay2 end: task-runner.m2 and the request and reply files it exchanges
    records     the record of an attempt, the stores that keep records, the artifacts tasks pass on
    scheduler   what a run computes and in which order, and running it
    reports     the tables of a run, and a run as a bundle that can be verified offline
    claims      the records committed to data/records and the claim tables (python3 -m batch.claims)

cli.py, the command line (python3 -m batch), sits on top of all of them but claims.
"""

__version__ = "0.2"
