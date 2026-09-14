# Instructions for research work

Read `README.md`, `docs/mathematical_collaboration_rules.md`, and the current proof/coverage records before research changes. Preserve the user's goal and explicitly separate mathematical proof, literature novelty, Lean kernel checking, and manuscript correspondence.

The English manuscript tracked by the Lean verification is `paper/weighted_obstruction_norms_en.tex`. Japanese text and PDFs are in the same directory. Preserve stable filenames. A manuscript change can invalidate the recorded semantic correspondence; identify affected claims and recheck them. Do not silently add hypotheses or change the mathematical objective.

Inspect the nearest existing literature before major proof expansion, and revisit it when statements or methods materially change. Formalize stable reusable lemmas incrementally; do not require Lean during every speculative discussion. Follow the detailed project rules.

Use the pinned `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Run `lake exe cache get` when dependencies are needed, and `python3 scripts/verify.py` for the existing project's full build and axiom audit. This script is tailored to the current source layout and fourteen-group coverage schema; adapt and review its coverage if project structure or scope changes. A success flag is not a semantic proof.

Existing audit records describe an earlier execution. Do not represent them as a new run. Verification rewrites current audit files; examine the diff before committing. `scripts/package.py` packages the historical Lean deliverable, not every new repository document or PDF. Use a GitHub release/source archive for a full repository snapshot.

Keep manuscript sources, rendered PDFs, proof code, and meaningful verification evidence. Exclude `.lake` and generated temporary files. Do not add a public license or publish the repository without the user's instruction. Avoid deleting historical evidence or overwriting unrelated changes. Preserve exact source bytes where hash-based audit records depend on them.

Repository layout: detailed formalization documentation is in `docs/LEAN.md` and `docs/FORMALIZATION_STATUS.md`; revision notes are in `docs/history/revisions/`; initial import documents are in `docs/history/import/`. Consult `docs/README.md` for historical path mappings. Preserve historical audit manifests as evidence of their original snapshot, not as a hash inventory of the current repository.
