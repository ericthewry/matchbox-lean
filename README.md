# proofs

This directory contains a Lean 4 project for a cleaned core of the Match Algebra metatheory from `../paper`.

Files:

- `Proofs/Basic.lean`: core syntax, semantics, domain judgment, GFD judgment, and mechanized domain/type soundness proofs for the cleaned base fragment.
- `Proofs/Transformers.lean`: cleaned transformer semantics and proofs for write/projection transformers plus range-action renaming.
- `Proofs/Compiler.lean`: an exact intensional compiler based on ordered rows and first-match tables, with `after`, strict sequential compilation, lexicographic join compilation, symbolic refinement splitting, and correctness/type-preservation theorems.
- `Proofs/Split.lean`: a hardware-oriented refinement layer over a finite valuation space, with abstract hardware guards, an SMT-style greedy split oracle, a proof of split soundness/completeness for single rows, and a parallel compiler `compileSplit` that uses this splitter for refinement.
- `PAPER_FIXES.md`: issues found while trying to align the paper with the mechanization.

Build with:

```bash
cd proofs
lake build
```
