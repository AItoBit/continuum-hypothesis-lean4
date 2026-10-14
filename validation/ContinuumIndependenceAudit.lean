module

public import ContinuumIndependence

@[expose] public section

open Fol bSet

example : ¬ (ZFC ⊢ₛ' CH_f) := CH_f_unprovable

example : ¬ (ZFC ⊢ₛ' (bd_not CH_f : sentence L_ZFC)) := neg_CH_f_unprovable

example : (¬ (ZFC ⊢ₛ' CH_f)) ∧
    (¬ (ZFC ⊢ₛ' (bd_not CH_f : sentence L_ZFC))) :=
  ContinuumIndependence.independence_of_CH

#check ZFC
#check CH_f
#check CH_f_unprovable
#check neg_CH_f_unprovable
#print ContinuumIndependence.independent
#check ContinuumIndependence.independence_of_CH

#print axioms CH_f_unprovable
#print axioms neg_CH_f_unprovable
#print axioms ContinuumIndependence.independence_of_CH
