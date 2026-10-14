/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
module

public import Flypitch4.Zfc

@[expose] public section

/-!
# Independence of the continuum hypothesis

This wrapper preserves the `independent` definition and the two-sided theorem
from `Flypitch4.Summary`. Its import includes only the dependency closure needed
for that theorem.
-/

namespace ContinuumIndependence

open Fol bSet

/-- A sentence is independent of a theory if neither it nor its negation is provable. -/
def independent {L : Language} (T : SentTheory L) (f : sentence L) : Prop :=
  (¬ T ⊢ₛ' f) ∧ (¬ T ⊢ₛ' (bd_not f : sentence L))

/-- The embedded first-order sentence for CH is independent of the embedded ZFC theory. -/
theorem independence_of_CH : independent ZFC CH_f :=
  ⟨CH_f_unprovable, neg_CH_f_unprovable⟩

end ContinuumIndependence
