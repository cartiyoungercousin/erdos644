# compute/

Search, solver and verification scripts (Python 3 with `pulp`, `highspy` and `python-sat`, plus some Node.js), each with its logs. The notes cite these by path. Results are only claimed with the level stated in `notes/LEDGER.md`.

| Folder | Content |
|---|---|
| `verify/`, `verify96/` | Independent checks behind the verification reports in `notes/verify/` |
| `core*/`, `strip/`, `links/`, `flag/`, `entropy/`, `cover/`, `paircover/`, `spread/` | Core-window analyses. `core12/` holds the exact window searches and certificates |
| `petal*/` | Petal-side strategies and exact replays (PS–PS3, CR, structure search) |
| `redteam/`, `fast/`, `twin/` | Adversary constructions, the exact game solver, and confinement experiments |
| `fableA/`, `fableC/`, `fableD/` | Work of the latest research round (see `notes/FABLE_*.md`) |
| `fresh_*/`, `r1*/`, `r2core/`, `combine/`, `newpaths/`, `roadmap/` | Earlier rounds; superseded but kept for reference |
| `finitek/`, `frontier/` | Finite-$k$ repairs and intermediate-bound work (in progress) |
