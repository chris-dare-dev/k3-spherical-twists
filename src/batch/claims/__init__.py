"""Which records are committed to data/records, and the claim tables written from them.

In: finished runs under results/, the registry data/claims/claims.toml, the batch files. Out:
data/records/<batch>/, and the generated parts of CLAIMS.md, GUIDE.md and data/claims/RECORDS.md.
`adopt` copies records and refuses those it cannot place in the history; `tables` writes and checks
the tables. Run it as `python3 -m batch.claims`; nothing else in the package imports it.
"""
