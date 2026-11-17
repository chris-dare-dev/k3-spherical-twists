"""Runs batches of Macaulay2 tasks: one process per task, under time and memory limits.

The mathematics lives in the Macaulay2 package and its runner script.  This package knows only that a
runner can expand a batch description into tasks and compute one task; it schedules the tasks, enforces
the limits, and keeps one structured record per task.
"""

__version__ = "0.2"
