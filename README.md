# Continuum hypothesis independence in Lean 4

This repository adapts the Flypitch proof that the continuum hypothesis and
its negation are both unprovable in Flypitch's explicitly defined first-order
ZFC theory. It reproduces established work; it does not claim a new solution
or a truth value for CH in Lean's ambient universe.

The original formalization is by Jesse Michael Han and Floris van Doorn.
The Lean 4 port is attributed to Ian Klatzco and Claude. This adaptation is
maintained by Alexander (GitHub: AItoBit), with implementation and review by
Codex agents. Original source notices and the Apache-2.0 license are retained.

## Formal statement

`ContinuumIndependence.independence_of_CH` states that neither `CH_f` nor its
object-language negation has a derivation from `ZFC`. The derivability relation
is the existence of a proof tree in an explicitly defined first-order calculus.
The proof constructs Cohen and collapse Boolean-valued models and applies
Boolean-valued soundness.

`Challenge.lean` contains the concrete statement definitions independently of
the forcing library. Its only admitted declaration is the specification theorem
that Comparator must match to the proved declaration imported by `Solution.lean`.
The Challenge imports Mathlib only. `comparator.json` selects the independence
theorem and permits only `propext`, `Classical.choice`, and `Quot.sound`.

The encoded language has membership together with empty-set, ordered-pair,
omega, powerset and union symbols, and the theory uses collection and Zorn's
lemma. A conservative translation to membership-only ZFC is not supplied.
The theorem is about this embedded theory; it does not assert CH or its negation
for the ambient Lean reals. Lean's stronger universe metatheory supports the
model constructions, so the theorem has no explicit consistency hypothesis.

## Provenance and verification status

- Upstream Lean 4 source: <https://github.com/ianklatzco/flypitch>, commit
  `ad649f89e9f3107b7e2ea97a58b2eafdfc80b815`.
- Mathematical account: Han and van Doorn, *A Formal Proof of the Independence
  of the Continuum Hypothesis*, CPP 2020, DOI
  [10.1145/3372885.3373826](https://doi.org/10.1145/3372885.3373826).
- Original project: <https://github.com/flypitch/flypitch>.
- The preceding Lean 4.33.1 compatibility development passed a complete build
  and exact-statement/axiom audit. Its final theorem depended only on the three
  standard axioms listed above.
- This repository is being adapted to Palomar's module-system, current
  toolchain and Challenge/Solution requirements. The preceding verification
  does not certify this newer snapshot. Palomar registration is pending.

The repository includes the substantive proof sources. It does not hide the
forcing development behind an unaudited or assumed theorem. Compatibility edits
and extraction of the statement are reviewed separately from compilation.
No endorsement by the original authors or independent human peer review is
claimed. See `formalization.yaml` for attribution and the AI contribution.

## Reproduction

Use the exact `lean-toolchain` and committed dependency revisions. Build with
`lake build Challenge Solution`, then run the pinned complete Palomar mechanical
workflow in `.github/workflows/palomar-preflight.yml`. A normal Lean build alone
does not establish Comparator or NanoDa success.
