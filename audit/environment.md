# Verification environment

- Lean: leanprover/lean4:v4.19.0, official release binary, commit 6caaee842e94.
- mathlib: c44e0c8ee63ca166450922a373c7409c5d26b00b (v4.19.0).
- OS: Linux x86_64, managed execution environment; 9 reported CPUs, about 21 GiB RAM.
- `readlink('/proc/<getpid()>/exe')` fails in this runtime, whereas `/proc/self/exe` works.
- Compatibility helper only translates that exact self-executable pathname. Every other call is passed to the original libc function. It does not change any proof, kernel operation, imported Lean module, or mathematical result.

Commands used for the helper and final verification:

```sh
cc -shared -fPIC audit/lean_proc_compat.c -ldl -o /tmp/lean_proc_compat.so
LD_PRELOAD=/tmp/lean_proc_compat.so PATH=/root/.elan/bin:$PATH LEAN_NUM_THREADS=8 python3 scripts/verify.py
```

Some mathlib cache downloads failed with HTTP 502; 211 cached modules were unpacked and the missing dependencies were built from the pinned sources. The build used eight Lean runtime threads. No proof was accepted on the basis of a numerical test or an external prover response. The original Lean binary and mathlib source were not patched. The package's `.lake/packages` paths in this runtime point to the locally built pinned dependency checkouts; those transient directories are excluded from the deliverable.

`audit/verification.json` is the authoritative status for the final included sources. `audit/axioms.log` records all named project theorem/lemma dependency reports.

## Revision 2 verification

The transient toolchain used for revision 1 was no longer present. The same
official Lean 4.19.0 toolchain and pinned mathlib commit were restored under
`/workspace/scratch/a9442e2794a7/lean-runtime/`. Missing dependencies were
compiled from source; the official ProofWidgets release artifact was fetched.
The compatibility helper was rebuilt from the unchanged included C source.
The latest verification was run from the project directory with:

```sh
../lean-runtime/run python3 scripts/verify.py
```

The launcher sets ELAN_HOME to `../lean-runtime/elan`, adds its bin directory
to PATH, sets LEAN_NUM_THREADS=8, and preloads `../lean-runtime/lean_proc_compat.so`.
These local runtime directories are excluded from the source archive.
`audit/history/verification_v1.json` preserves the previous result; the current
`audit/verification.json` and its matching build/axiom logs cover revision 2.

## Revision 3 verification

The workspace-local fixed runtime from revision 2 was reused. Additional
Hahn--Banach and quotient dependencies were built from the same pinned
mathlib sources. The command remains `../lean-runtime/run python3 scripts/verify.py`.
No Lean binary, kernel, or mathlib proof source was modified.
`audit/history/verification_v2.json` preserves the prior 106-declaration report;
the current verification record and logs cover all modules in revision 3.

## Revision 4 verification

The same workspace-local Lean runtime and pinned mathlib sources were reused.
The verification command remains `../lean-runtime/run python3 scripts/verify.py`.
The prior 155-declaration report is retained in `audit/history/verification_v3.json`.
The current report covers 207 declarations, including concrete low-degree
Cech and degree-zero observation-restriction modules. Some linter warnings
concern unused section instances; the build and axiom audit both exit zero.

## Revision 5 verification

The same workspace-local runtime and pinned mathlib sources were reused.
The command is `../lean-runtime/run python3 scripts/verify.py`.
The prior 207-declaration record is retained as `audit/history/verification_v4.json`.
The current verification covers 329 declarations, including all-degree
alternating cancellation and the actual augmented Cech differential.

Revision 6: full-support acyclicity and concrete relative-window construction are kernel checked; see REVISION_6.md.

Revision 7: original primitive-cost identification, affine reciprocal law and rescaled right-hand limit are kernel checked.

## Final revision 12

The final command is `../lean-runtime/run python3 scripts/verify.py`, using the same unmodified official Lean 4.19.0 and pinned mathlib. The completed coverage table names all fourteen manuscript results, including the appendix and actual binary examples. The final audit checks 640 theorem/lemma declarations plus five key definitions. Earlier revision paragraphs are historical; `verification.json` is the authoritative final record. All source modules and the coverage table are hash-checked by the packaging script.
