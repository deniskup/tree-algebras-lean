# Tree algebras and bisimulation-invariant MSO on finite graphs

Lax submission **lax-369799**, targeting the revised manuscript of
13 November 2026. [paper-version.json](paper-version.json) records its hash.
The revised manuscript PDF is retained locally; this repository publishes
the formalization and its validation records.

The requested scope is **Theorem 2, its supporting proof network, and
end-to-end effectivity**. Both implications of Theorem 2 and a total
executable translation are proved in Lean. The final validation results
are recorded in [validation-report.json](validation-report.json): **213 concepts,
566 ground proofs, zero unproved declarations and zero relative proofs**.
The main proofs use only `propext`, `Classical.choice`, and `Quot.sound`.

## Main entry points

Import `Lax369799Proofs.MainTheorems` from the `proofs` package.

- [Theorem 2 and effective theorem](proofs/Lax369799Proofs/MainTheorems.lean):
  `finite_bisimulation_invariant_mso` and
  `effective_finite_bisimulation_invariant_mso`.
- [Executable translation](concepts/Lax369799/EffectiveFiniteTranslation.lean):
  `EffectiveFiniteTranslation.compile`.
- [Compiler correctness](proofs/Lax369799Proofs/EffectiveFiniteTranslation.lean):
  `EffectiveFiniteTranslation.compile_correct`, the helper used by the
  main effective theorem (registered once with the Archive).
- [Statement signatures](concepts/Lax369799/FiniteBisimulationTheorem.lean).

The existence theorem assumes a finite proposition alphabet. The executable
compiler receives an explicitly encoded finite alphabet (`Fintype`,
`Encodable`, and `DecidableEq`), including every vocabulary `Fin n`.
It returns a sentence for every MSO input. Correctness assumes that the
input defines a bisimulation-invariant property over finite reachable
transition systems. The compiler does not decide this promise.

## Effective construction

The construction follows the finite-search argument on page 54 of the
revised paper. It computes bounds from the input syntax, enumerates finite
Boolean modal tables, compiles their sentences, and tests them on all
reachable graph codes within a pair-separation bound. It is an exhaustive
algorithm establishing effectivity; the bounds are intentionally generous.

| Step | Checked implementation |
| --- | --- |
| Recognizing-algebra sort bounds | `QuantitativeRecognition` |
| Small-profile quotient bounds | `QuantitativeProfiles` |
| Safra and parity state/priority bounds | `QuantitativeDeterminization`, `QuantitativeWordConditions` |
| Bounded clone automaton | `QuantitativeAutomata` |
| Finite game simulation and small models | `ParityGameSimulation`, `ModalSmallModels` |
| Model bound under finite invariance | `QuantitativeFiniteTheorem` |
| Executable Boolean model checking | `FiniteModelChecking` |
| Finite modal tables and scalar compilation | `FiniteModalData`, `PriorityCompilation` |
| Bounded graph comparison and selection | `FiniteTesting`, `EffectiveFiniteTranslation` |

The model bound is derived from the bounded modal certificate and positional
strategies: a winning model can use at most one vertex per word state.
Applying this to the MSO translation of the difference of two modal
candidates supplies the finite comparison bound. This uses the proved
finite construction and introduces no assumed small-model theorem.

## Paper interfaces and coverage

`FinitePresentations` retains unreachable vertices during substitution.
`SupportedSystems` and `SupportedAlgebras` implement the output reachability
of Definition 6. `SupportedCompletion` proves the bridge to the intermediate
algebra interface. The algebra-to-automaton and modal theorems state the
revised supported-algebra hypothesis.

[PLAN.md](PLAN.md) maps the proof route to the manuscript.
[paper-coverage.json](paper-coverage.json) retains the broader inventory of
all 62 numbered results. It records 59 matching statements and three partial
alignments: unrestricted Theorem 1 and the separate exact formulations of
Lemmas 42 and 47. The requested Theorem 2 and effectivity use a completely
proved dependency route. Exhaustive coverage of the broader inventory is
not claimed. [PAPER_CHANGES.md](PAPER_CHANGES.md) preserves the revision history.

## Validation

From the repository root:

```sh
PATH=/home/denis/.elan/bin:$PATH lax build . --replay
```

Additional audits:

```sh
cd proofs
lake env lean ../audit/RevisedStructure.lean
lake env lean ../audit/EffectiveFiniteTranslation.lean
```

The executable audit checks reachability, both model checkers, finite table
enumeration, and modal compilation. It also checks that a self-loop MSO
sentence and the infinite-path modal sentence agree on one-vertex models
but are separated by a two-vertex model.

## Attribution

Safra determinization, appearance records, and finite parity-game proofs
are adapted from the ancillary Lean development of Bojańczyk, Casares,
Manthe and Parys, [arXiv:2611.10136v1](https://arxiv.org/abs/2611.10136v1),
with incorporation authorized by the user. [external-proofs.json](external-proofs.json)
records source and destination hashes; [manifest.yaml](manifest.yaml) contains
the citation. The pinned toolchain is Lean 4.33.0 with mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

`lax submit .` sends the committed source as a replaceable draft.
Permanent registration is a separate step with `lax register .`.
