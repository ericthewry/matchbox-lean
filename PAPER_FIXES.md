# Paper Fixes Suggested by the Lean Formalization

The current Lean development surfaced a few places where the paper should be normalized before a full end-to-end mechanization:

1. The paper uses more than one definition of GFD satisfaction.
   The version in `paper/sections/functional-types.tex` is pointwise and deterministic.
   The version in `paper/proofs.tex` is phrased via equivalence classes and singleton denotations.
   These should be merged into one canonical definition.

2. Several appendix proofs swap variables or reference the wrong program.
   Examples:
   `paper/proofs.tex` uses `C_1` where `C_2` is intended in the `FDP-Right` argument, and some `ν_0`/`ν_1` references are inverted.

3. The semantics notation is not fully consistent.
   The paper alternates between `SemTable`/`SemLit`, `override`/`pref`, and a few malformed big-step judgments.
   These should be made uniform before a literal mechanization.

4. The transformer rules need a single precise statement.
   The `FDRange`/`FDDomain` rules rely on auxiliary transformer judgments, but the appendix only sketches these and the write/projection side conditions.
   A full formalization needs these judgments stated once and reused consistently.

5. The compiler section assumes extra invariants that are not fully stated.
   In particular, the join and compilation-correctness arguments need explicit assumptions about how output supports compose and how compiled tables preserve the domain/postcondition side of GFDs.

Current status of the Lean files:

- `Proofs/Basic.lean` contains a cleaned core formalization for the main language fragment:
  literals, variables, refinement, sequencing, join, and preferential composition.
- `domain_overapprox` is fully proved for this cleaned fragment.
- `type_soundness` is now fully proved for this cleaned fragment.
- `Proofs/Transformers.lean` adds cleaned transformer metatheory for write/projection transformers and action renaming.
- `Proofs/Compiler.lean` now gives an intensional compiler for the cleaned fragment using ordered rows and first-match tables, and proves refinement, domain preservation, type preservation, and correctness modulo a GFD for that compiler.

Additional normalization used in the Lean development:

6. The join postcondition needed to be made explicit.
   In the Lean formalization, the postcondition for joins records that the output valuation is a merge of two component valuations satisfying the component postconditions.
   This makes the soundness proof precise without assuming unstated closure properties of refinement formulas under merging.

7. The compiler formalization is now intensional for the cleaned fragment, but not yet hardware-specific.
   The Lean `Compiler` module uses concrete ordered rows and first-match evaluation, matching the paper’s intensional perspective.
   However, because guards are modeled as arbitrary formulas, refinement splitting is represented by direct guard conjunction rather than the hardware-restricted, solver-guided `GreedySplit` algorithm from the paper.

8. The hardware split theorem needs the finite packet space to be explicit.
   In the Lean `Split` module, the greedy SMT-style splitter is proved exact relative to an explicit finite list `space` of relevant valuations.
   This assumption is already implicit in the compiler discussion in `paper/sections/compiler-new.tex`, but the statement of `thm:split-sound` should say whether the equivalence is over all valuations or over the chosen finite relevant packet space.

9. The OMT maximization is not needed for soundness.
   The mechanization proves that any guard returned by the oracle is sound as long as it contains the chosen witness and stays within the current residual region on `space`.
   If the paper wants only semantic correctness, the optimization step can be presented as a compactness heuristic rather than as part of the trusted core argument.

10. The hardware compiler needs an explicit closure assumption for intermediate outputs.
   To prove the split-based compiler for sequencing and joins, Lean needs a finite valuation space that also contains the intermediate/output valuations produced by literal tables, environment tables, and merged join outputs.
   The paper currently motivates finiteness using input packets, but the compiler proof should clarify that the same finite universe is used for the intermediate valuations seen during compilation and execution.
