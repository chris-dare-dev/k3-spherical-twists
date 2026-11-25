"""What a reader gets from a run: the report's tables, and the run exported as a bundle that
can be verified offline.

In: the records of a run and its manifest. Out: Markdown tables, a bundle directory. It writes
nothing back to a store.
"""

from .bundle import BundleError, export_run, verify_run
from .report import cell, render, select, selected_results, summary, tables

__all__ = [
    "BundleError",
    "cell",
    "export_run",
    "render",
    "select",
    "selected_results",
    "summary",
    "tables",
    "verify_run",
]
