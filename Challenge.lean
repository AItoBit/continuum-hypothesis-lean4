/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
module

public import Mathlib.Data.Set.Countable

/-!
# Independence of the continuum hypothesis

This statement extracts the concrete syntax, classical derivation rules, axioms,
and CH sentence used by Flypitch. Every definition below has the original
qualified name and value. Challenge and Solution are separate environments;
Solution does not import this file. Comparator checks the statement dependency
closure against the proof development.

`independence_of_CH` states that neither `CH_f` nor its negation has a derivation
from `ZFC` in the explicitly defined calculus. The theory uses membership plus
function symbols for the empty set, ordered pairs, omega, powerset, and union;
its axioms include strong collection and Zorn's lemma. The sentence excludes an
ordinal cardinality strictly between omega and its powerset.

The result is proved in Lean's ambient type theory. A formal conservativity
bridge to the usual pure membership-language presentation of ZFC is not claimed.
This is the existing Flypitch independence theorem, not a new resolution of CH.

Sources: Han and van Doorn, *A Formal Proof of the Independence of the Continuum
Hypothesis*, CPP 2020, DOI 10.1145/3372885.3373826;
https://florisvandoorn.com/papers/flypitch-cpp-2020.pdf.
Extracted from the Lean 4 port at upstream revision
ad649f89e9f3107b7e2ea97a58b2eafdfc80b815, with the compatibility changes
and provenance documented in this repository.
-/

@[expose] public section

universe u v

/-- A vector with exactly `n` entries of type `α`. -/
inductive DVec (α : Type u) : ℕ → Type u
  | nil  : DVec α 0
  | cons : ∀ {n} (x : α) (xs : DVec α n), DVec α (n + 1)

/-- The curried type of an `n`-argument function from `α` to `β`. -/
def Arity' (α β : Type u) : ℕ → Type u
  | 0 => β
  | n + 1 => α → Arity' α β n

namespace Arity'

/-- Curry a function whose argument is a fixed-length vector. -/
@[simp] def of_dvector_map {α β : Type u} : ∀ {l} (f : DVec α l → β), Arity' α β l
  | 0, f => f DVec.nil
  | l + 1, f => fun x => of_dvector_map (fun xs => f (DVec.cons x xs))

end Arity'

namespace Fol

namespace BoundProof

theorem index_lt (i gap n : ℕ) : i < n + (i + gap + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right i gap))
    (Nat.le_add_left (i + gap + 1) n)

theorem cast_lt {n m : ℕ} (h : n ≤ m) (k : Fin n) : k.1 < m :=
  Nat.lt_of_lt_of_le k.2 h

theorem lift_lt {n : ℕ} (k : Fin n) (n' : ℕ) : k.1 + n' < n + n' :=
  Nat.add_lt_add_right k.2 n'

theorem weaken_lt {n : ℕ} (k : Fin n) (n' : ℕ) : k.1 < n + n' :=
  Nat.lt_of_lt_of_le k.2 (Nat.le_add_right n n')

theorem subst_left_lt {n n' : ℕ} (k : Fin (n + n' + 1)) (h : k.1 < n) :
    k.1 < n + n' :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right n n')

theorem subst_right_lt {n n' : ℕ} (k : Fin (n + n' + 1)) (h : n < k.1) :
    k.1 - 1 < n + n' :=
  (Nat.sub_lt_iff_lt_add
    (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n) h))).mpr k.2

theorem add_comm_le (n n' : ℕ) : n' + n ≤ n + n' :=
  Nat.le_of_eq (Nat.add_comm n' n)

theorem subst_refl (n n' : ℕ) : n + n' + 1 = n + n' + 1 := rfl

theorem subst_all_eq (n n' : ℕ) : (n + 1) + n' + 1 = n + n' + 1 + 1 :=
  congrArg (fun k : ℕ => k + 1) (Nat.add_right_comm n 1 n')

theorem subst_zero_eq (n : ℕ) : 0 + n + 1 = n + 1 :=
  congrArg (fun k : ℕ => k + 1) (Nat.zero_add n)

theorem add_right_comm_one (n n' : ℕ) : (n + 1) + n' = n + n' + 1 :=
  Nat.add_right_comm n 1 n'

end BoundProof

/-- Replace entry `n` of a valuation by `x` and shift later entries down one. -/
def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
  if k < n then v k else if n < k then v (k - 1) else x

/-- A first-order signature, specifying function and relation symbols by arity. -/
structure Language : Type (u + 1) where
  functions : ℕ → Type u
  relations : ℕ → Type u

/-- The nullary function symbols of a signature. -/
def Language.constants (L : Language.{u}) := L.functions 0

variable (L : Language.{u})

/-- Partially applied first-order terms with natural-number de Bruijn variables. -/
inductive preterm : ℕ → Type u
  | var : ∀ (k : ℕ), preterm 0
  | func : ∀ {l : ℕ} (f : L.functions l), preterm l
  | app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l

/-- Fully applied first-order terms. -/
@[reducible] def term := preterm L 0

variable {L}

prefix:max "&" => Fol.preterm.var

/-- Raise variables at or above position `m` by `n`. -/
@[simp] def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
  | _, preterm.var k, n, m => &(if m ≤ k then k + n else k)
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, n, m => preterm.app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

/-- Raise all variables of a term by `n`. -/
@[reducible] def lift_term {l} (t : preterm L l) (n : ℕ) : preterm L l := lift_term_at t n 0

/-- Substitute for variable `n`, lowering later de Bruijn indices by one. -/
def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
  | _, preterm.var k, s, n => Fol.subst_realize preterm.var (lift_term s n) n k
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, s, n => preterm.app (subst_term t₁ s n) (subst_term t₂ s n)

/-- First-order formulas, including partially applied relation symbols. -/
inductive preformula : ℕ → Type u
  | falsum : preformula 0
  | equal (t₁ t₂ : term L) : preformula 0
  | rel {l : ℕ} (R : L.relations l) : preformula l
  | apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
  | imp (f₁ f₂ : preformula 0) : preformula 0
  | all (f : preformula 0) : preformula 0

variable (L)

/-- Fully applied first-order formulas with unbounded variable indices. -/
@[reducible] def formula (L : Language.{u}) : Type u := @preformula L 0

variable {L}
notation "⊥'" => Fol.preformula.falsum
scoped infix:88 " ≃ " => Fol.preformula.equal
scoped infixr:62 " ⟹ " => Fol.preformula.imp
scoped prefix:110 "∀'" => Fol.preformula.all

/-- Negation defined as implication to falsity. -/
def not' (f : formula L) : formula L := preformula.imp f preformula.falsum

scoped prefix:max "∼" => Fol.not'

/-- Raise free variables at or above `m`, respecting quantifier binding. -/
@[simp] def lift_formula_at : ∀ {l}, @preformula L l → ℕ → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, n, m => preformula.equal (lift_term_at t₁ n m) (lift_term_at t₂ n m)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, n, m => preformula.apprel (lift_formula_at f n m) (lift_term_at t n m)
  | _, preformula.imp f₁ f₂, n, m => preformula.imp (lift_formula_at f₁ n m) (lift_formula_at f₂ n m)
  | _, preformula.all f, n, m => preformula.all (lift_formula_at f n (m + 1))

/-- Raise all free variables by `n`. -/
@[reducible] def lift_formula {l} (f : @preformula L l) (n : ℕ) : @preformula L l :=
  lift_formula_at f n 0

/-- Raise all free variables by one. -/
@[reducible, simp] def lift_formula1 {l} (f : @preformula L l) : @preformula L l := lift_formula f 1

/-- Substitute a term for variable `n`, respecting quantifier binding. -/
@[simp] def subst_formula : ∀ {l}, @preformula L l → term L → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, s, n =>
      preformula.equal (subst_term t₁ s n) (subst_term t₂ s n)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, s, n =>
      preformula.apprel (subst_formula f s n) (subst_term t s n)
  | _, preformula.imp f₁ f₂, s, n =>
      preformula.imp (subst_formula f₁ s n) (subst_formula f₂ s n)
  | _, preformula.all f, s, n => preformula.all (subst_formula f s (n + 1))

notation:95 f " [" s " // " n "]f" => Fol.subst_formula f s n

/-- Derivations in classical first-order logic with equality: the eight constructors are its rules. -/
inductive prf : Set (formula L) → formula L → Type u
  | axm     {Γ A}   (h : A ∈ Γ) : prf Γ A
  | impI    {Γ : Set (formula L)} {A B}
                    (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
  | impE    {Γ}     (A) {B}
                    (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
  | falsumE {Γ : Set (formula L)} {A}
                    (h : prf (insert (∼A) Γ) ⊥') : prf Γ A
  | allI    {Γ A}   (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
  | allE₂   {Γ}     (A) (t : term L)
                    (h : prf Γ (∀' A)) : prf Γ (A [t // 0]f)
  | ref     (Γ)     (t : term L) : prf Γ (t ≃ t)
  | subst₂  {Γ}     (s t : term L) (f : formula L)
                    (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f [s // 0]f)) : prf Γ (f [t // 0]f)

scoped infix:51 " ⊢ " => Fol.prf

/-- Provability means that the corresponding derivation type is nonempty. -/
def provable (T : Set (formula L)) (f : formula L) := Nonempty (T ⊢ f)

scoped infix:51 " ⊢' " => Fol.provable

variable (L)

/-- Partially applied terms whose free variables are indexed by `Fin n`. -/
inductive bounded_preterm (L : Language.{u}) (n : ℕ) : ℕ → Type u
  | bd_var : ∀ (k : Fin n), bounded_preterm L n 0
  | bd_func : ∀ {l : ℕ} (f : L.functions l), bounded_preterm L n l
  | bd_app : ∀ {l : ℕ} (t : bounded_preterm L n (l + 1)) (s : bounded_preterm L n 0),
      bounded_preterm L n l

export bounded_preterm (bd_var bd_func bd_app)

/-- Fully applied terms with fewer than `n` free variable indices. -/
def bounded_term (n : ℕ) := bounded_preterm L n 0

/-- Partially applied terms with no free variables. -/
def closed_preterm (l : ℕ) := bounded_preterm L 0 l

/-- Fully applied terms with no free variables. -/
def closed_term := closed_preterm L 0

variable {L}

/-- View a constant symbol as a bounded term. -/
def bd_const {n} (c : L.constants) : bounded_term L n := bd_func c

/-- Apply a partially applied term to a vector of all remaining arguments. -/
@[simp] def bd_apps {n} : ∀ {l}, bounded_preterm L n l → DVec (bounded_term L n) l →
    bounded_term L n
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => bd_apps (bd_app t t') ts

namespace bounded_preterm

/-- Forget the variable bound of a term. -/
@[simp] protected def fst {n} : ∀ {l}, bounded_preterm L n l → preterm L l
  | _, bd_var k => &k.1
  | _, bd_func f => preterm.func f
  | _, bd_app t s => preterm.app (bounded_preterm.fst t) (bounded_preterm.fst s)

/-- Weaken the free-variable bound from `n` to `m`. -/
@[simp] protected def cast {n m} (h : n ≤ m) : ∀ {l}, bounded_preterm L n l →
    bounded_preterm L m l
  | _, bd_var k => bd_var ⟨k.1, BoundProof.cast_lt h k⟩
  | _, bd_func f => bd_func f
  | _, bd_app t s => bd_app (t.cast h) (s.cast h)

/-- Transport a term across equality of variable bounds. -/
protected def cast_eq {n m l} (h : n = m) (t : bounded_preterm L n l) : bounded_preterm L m l :=
  t.cast (Nat.le_of_eq h)

end bounded_preterm

/-- Insert new free-variable positions beginning at `m`. -/
@[simp] def lift_bounded_term_at {n} : ∀ {l} (t : bounded_preterm L n l) (n' m : ℕ),
    bounded_preterm L (n + n') l
  | _, bd_var k, n', m =>
      if m ≤ k.1 then bd_var ⟨k.1 + n', BoundProof.lift_lt k n'⟩
      else bd_var ⟨k.1, BoundProof.weaken_lt k n'⟩
  | _, bd_func f, _, _ => bd_func f
  | _, bd_app t₁ t₂, n', m => bd_app (lift_bounded_term_at t₁ n' m) (lift_bounded_term_at t₂ n' m)

notation:90 t " ↑ᵇ' " n " # " m => Fol.lift_bounded_term_at t n m

/-- Insert new free-variable positions beginning at zero. -/
@[reducible] def lift_bounded_term {n l} (t : bounded_preterm L n l) (n' : ℕ) :
    bounded_preterm L (n + n') l := lift_bounded_term_at t n' 0

infixl:100 " ↑ᵇ " => Fol.lift_bounded_term

/-- Substitute at position `n` in a bounded term and remove that position. -/
def subst_bounded_term {n n'} : ∀ {l} (t : bounded_preterm L (n + n' + 1) l)
    (s : bounded_term L n'), bounded_preterm L (n + n') l
  | _, bd_var k, s =>
      if h : k.1 < n then bd_var ⟨k.1, BoundProof.subst_left_lt k h⟩
      else if h' : n < k.1 then
        bd_var ⟨k.1 - 1, BoundProof.subst_right_lt k h'⟩
      else
        (s ↑ᵇ n).cast (BoundProof.add_comm_le n n')
  | _, bd_func f, _ => bd_func f
  | _, bd_app t₁ t₂, s => bd_app (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)

/-- Build a bounded term by applying a signature function symbol. -/
def bounded_term_of_function {l n} (f : L.functions l) :
    Arity' (bounded_term L n) (bounded_term L n) l :=
  Arity'.of_dvector_map (bd_apps (bd_func f))

variable (L)

/-- Formulas with fewer than `n` free variable indices and `l` unapplied arguments. -/
inductive bounded_preformula (L : Language.{u}) : ℕ → ℕ → Type u
  | bd_falsum : ∀ {n}, bounded_preformula L n 0
  | bd_equal : ∀ {n} (t₁ t₂ : bounded_term L n), bounded_preformula L n 0
  | bd_rel : ∀ {n l : ℕ} (R : L.relations l), bounded_preformula L n l
  | bd_apprel : ∀ {n l} (f : bounded_preformula L n (l + 1)) (t : bounded_term L n),
      bounded_preformula L n l
  | bd_imp : ∀ {n} (f₁ f₂ : bounded_preformula L n 0), bounded_preformula L n 0
  | bd_all : ∀ {n} (f : bounded_preformula L (n + 1) 0), bounded_preformula L n 0

export bounded_preformula (bd_falsum bd_equal bd_rel bd_apprel bd_imp bd_all)

/-- Fully applied formulas with fewer than `n` free variable indices. -/
@[reducible] def bounded_formula (n : ℕ) := bounded_preformula L n 0

/-- A formula with no free variables and `l` unapplied arguments. -/
@[reducible] def presentence (l : ℕ) := bounded_preformula L 0 l

/-- A fully applied formula with no free variables. -/
@[reducible] def sentence := presentence L 0

variable {L}

/-- Negation of a bounded formula. -/
def bd_not {n} (f : bounded_formula L n) : bounded_formula L n :=
  bd_imp f bd_falsum

/-- Conjunction of bounded formulas, defined from negation and implication. -/
def bd_and {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_not (bd_imp f₁ (bd_not f₂))

/-- Disjunction of bounded formulas, defined from negation and implication. -/
def bd_or {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_imp (bd_not f₁) f₂

/-- Logical equivalence of bounded formulas. -/
def bd_biimp {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_and (bd_imp f₁ f₂) (bd_imp f₂ f₁)

/-- Existential quantification of the innermost variable. -/
def bd_ex {n} (f : bounded_formula L (n + 1)) : bounded_formula L n :=
  bd_not (bd_all (bd_not f))

/-- Apply a relation preformula to its remaining bounded-term arguments. -/
@[simp] def bd_apps_rel {n} : ∀ {l} (f : bounded_preformula L n l)
    (ts : DVec (bounded_term L n) l), bounded_formula L n
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => bd_apps_rel (bd_apprel f t) ts

namespace bounded_preformula

/-- Forget the free-variable bound of a formula. -/
@[simp] protected def fst : ∀ {n l}, bounded_preformula L n l → @preformula L l
  | _, _, bd_falsum => preformula.falsum
  | _, _, bd_equal t₁ t₂ => preformula.equal t₁.fst t₂.fst
  | _, _, bd_rel R => preformula.rel R
  | _, _, bd_apprel f t => preformula.apprel f.fst t.fst
  | _, _, bd_imp f₁ f₂ => preformula.imp f₁.fst f₂.fst
  | _, _, bd_all f => preformula.all f.fst

/-- Weaken a formula to a larger bound on free variables. -/
@[simp] protected def cast {n m} (h : n ≤ m) : ∀ {l}, bounded_preformula L n l →
    bounded_preformula L m l
  | _, bd_falsum => bd_falsum
  | _, bd_equal t₁ t₂ => bd_equal (t₁.cast h) (t₂.cast h)
  | _, bd_rel R => bd_rel R
  | _, bd_apprel f t => bd_apprel (f.cast h) (t.cast h)
  | _, bd_imp f₁ f₂ => bd_imp (f₁.cast h) (f₂.cast h)
  | _, bd_all f => bd_all (f.cast (Nat.succ_le_succ h))

/-- Transport a formula across equality of free-variable bounds. -/
protected def cast_eq {n m l} (h : n = m) (f : bounded_preformula L n l) :
    bounded_preformula L m l := f.cast (Nat.le_of_eq h)

end bounded_preformula

/-- Build a bounded formula by applying a relation symbol. -/
def bounded_formula_of_relation {l n} (R : L.relations l) :
    Arity' (bounded_term L n) (bounded_formula L n) l :=
  Arity'.of_dvector_map (bd_apps_rel (bd_rel R))

/-- Substitute a bounded term at position `n`, removing that variable. -/
@[simp] def subst_bounded_formula : ∀ {n n' n'' l} (f : bounded_preformula L n'' l)
    (s : bounded_term L n') (h : n + n' + 1 = n''), bounded_preformula L (n + n') l
  | _, _, _, _, bd_falsum, _, _ => bd_falsum
  | _, _, _, _, bd_equal t₁ t₂, s, rfl => bd_equal (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)
  | _, _, _, _, bd_rel R, _, _ => bd_rel R
  | n, n', _, _, bd_apprel f t, s, rfl =>
      bd_apprel (subst_bounded_formula f s (BoundProof.subst_refl n n')) (subst_bounded_term t s)
  | n, n', _, _, bd_imp f₁ f₂, s, rfl =>
      bd_imp (subst_bounded_formula f₁ s (BoundProof.subst_refl n n'))
        (subst_bounded_formula f₂ s (BoundProof.subst_refl n n'))
  | n, n', _, _, bd_all f, s, rfl =>
      -- f : bounded_preformula L (n + n' + 1 + 1) 0
      -- we call subst with n+1, n', giving h : (n+1)+n'+1 = n+n'+1+1
      -- result: bounded_preformula L ((n+1)+n') 0 = bounded_preformula L (n+n'+1) 0
      -- then cast to n+n'+1 = n+n'+1 which is trivially true
      bd_all ((subst_bounded_formula f s (BoundProof.subst_all_eq n n')).cast_eq
        (BoundProof.add_right_comm_one n n'))

/-- Substitute a closed term for the highest free variable. -/
@[simp] def substmax_bounded_formula {n l} (f : bounded_preformula L (n + 1) l)
    (s : closed_term L) : bounded_preformula L n l :=
  subst_bounded_formula f s (BoundProof.subst_refl n (nat_lit 0))

/-- Substitute a term for the innermost free variable. -/
def subst0_bounded_formula {n l} (f : bounded_preformula L (n + 1) l)
    (s : bounded_term L n) : bounded_preformula L n l :=
  -- n + 1 = 0 + n + 1, so we use h : 0 + n + 1 = n + 1
  (subst_bounded_formula f s (BoundProof.subst_zero_eq n)).cast_eq
    (Nat.zero_add n)

/-- Insert free-variable positions, adjusting the cutoff beneath quantifiers. -/
@[simp] def lift_bounded_formula_at : ∀ {n l} (f : bounded_preformula L n l) (n' m : ℕ),
    bounded_preformula L (n + n') l
  | _, _, bd_falsum, _, _ => bd_falsum
  | _, _, bd_equal t₁ t₂, n', m => bd_equal (t₁ ↑ᵇ' n' # m) (t₂ ↑ᵇ' n' # m)
  | _, _, bd_rel R, _, _ => bd_rel R
  | _, _, bd_apprel f t, n', m =>
      bd_apprel (lift_bounded_formula_at f n' m) (t ↑ᵇ' n' # m)
  | _, _, bd_imp f₁ f₂, n', m =>
      bd_imp (lift_bounded_formula_at f₁ n' m) (lift_bounded_formula_at f₂ n' m)
  | n, _, bd_all f, n', m =>
      bd_all ((lift_bounded_formula_at f n' (m + 1)).cast_eq (BoundProof.add_right_comm_one n n'))

notation:90 f " ↑ᶠᵇ' " n " # " m => Fol.lift_bounded_formula_at f n m

/-- Insert free-variable positions beginning at zero. -/
@[reducible] def lift_bounded_formula {n l} (f : bounded_preformula L n l) (n' : ℕ) :
    bounded_preformula L (n + n') l := lift_bounded_formula_at f n' 0

/-- A sentence theory is a set of closed formulas. -/
abbrev SentTheory (L : Language.{u}) := Set (sentence L)

/-- The underlying unbounded formulas of the sentences in a theory. -/
@[reducible] def SentTheory.fst (T : SentTheory L) : Set (formula L) :=
  bounded_preformula.fst '' T

/-- A sentence is provable if its underlying formula has a derivation from the theory. -/
def SentTheory.sprovable (T : SentTheory L) (f : sentence L) : Prop := T.fst ⊢' f.fst

scoped notation:51 T " ⊢ₛ' " f => Fol.SentTheory.sprovable T f

/-- Universally quantify every free variable, producing a sentence. -/
@[simp] def bd_alls : ∀ (n : ℕ), bounded_formula L n → sentence L
  | 0,     f => f
  | n + 1, f => bd_alls n (bd_all f)

end Fol

open Fol

/-- The single binary membership relation of the set-theoretic signature. -/
inductive ZFC_rel : ℕ → Type 1
  | ε : ZFC_rel 2

/-- Function symbols for empty set, ordered pair, omega, powerset, and union. -/
inductive ZFC_func : ℕ → Type 1
  | emptyset : ZFC_func 0
  | pr       : ZFC_func 2
  | ω        : ZFC_func 0
  | P        : ZFC_func 1
  | Union    : ZFC_func 1

/-- The expanded first-order language used by this set-theoretic development. -/
def L_ZFC : Language.{1} :=
  { functions := ZFC_func, relations := ZFC_rel }

/-- The empty-set constant term. -/
def emptyset' {n} : bounded_term L_ZFC n := bd_const ZFC_func.emptyset

/-- The omega constant term. -/
def omega' {n} : bounded_term L_ZFC n := bd_const ZFC_func.ω

/-- The powerset function applied to a term. -/
def Powerset {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.P) t

/-- The membership formula for two terms. -/
def mem' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  @bounded_formula_of_relation L_ZFC 2 n ZFC_rel.ε t₁ t₂

/-- The ordered-pair function applied to two terms. -/
def pair' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  @bounded_term_of_function L_ZFC 2 n ZFC_func.pr t₁ t₂

/-- The union function applied to a term. -/
def union' {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.Union) t

notation "∅'" => emptyset'
notation "ω'" => omega'
notation "P'" => Powerset
notation "⋃'" => union'

/-- Subset inclusion: every member of the first term belongs to the second. -/
def subset'' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₁ ↑ᵇ' 1 # 0))
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₂ ↑ᵇ' 1 # 0)))

/-- The free set is transitive. -/
def is_transitive_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
                 (subset'' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩)))

/-- Any two members of the free set are equal or membership-comparable. -/
def epsilon_trichotomy_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
    (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))
      (bd_or
        (bd_or (bd_equal (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩))
               (mem' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩)))
        (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩))))))

/-- Every nonempty subset of the free set has a membership-minimal element. -/
def epsilon_well_founded_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (subset'' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
    (bd_imp (bd_not (bd_equal (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) ∅'))
      (bd_ex (bd_and (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) (nat_lit 0)⟩))
          (bd_not (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩)))))))))

/-- Membership linearly well-orders the free set. -/
def ewo_f : bounded_formula L_ZFC 1 := bd_and epsilon_trichotomy_f epsilon_well_founded_f

/-- The free set is a transitive set well-ordered by membership, hence an ordinal. -/
def Ord_f : bounded_formula L_ZFC 1 := bd_and ewo_f is_transitive_f

/-- No set belongs to the empty-set constant. -/
def axiom_of_emptyset : sentence L_ZFC :=
  bd_all (bd_not (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩) ∅'))

/-- Two ordered pairs are equal exactly when their respective coordinates are equal. -/
def axiom_of_ordered_pairs : sentence L_ZFC :=
  bd_all (bd_all (bd_all (bd_all
    (bd_biimp
      (bd_equal (pair' (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 0) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) (nat_lit 0)⟩))
                (pair' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩)))
      (bd_and
        (bd_equal (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 0) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩))
        (bd_equal (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩)))))))

/-- Sets with the same members are equal. -/
def axiom_of_extensionality : sentence L_ZFC :=
  bd_all (bd_all
    (bd_imp
      (bd_all (bd_biimp
        (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))
        (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩))))
      (bd_equal (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩))))

/-- Universally closed strong collection schema for the two-variable relation `ϕ` and parameters. -/
def axiom_of_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) : sentence L_ZFC :=
  bd_alls (n + 1) $
    bd_imp
      (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) n⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) n⟩))
        (bd_ex (ϕ ↑ᶠᵇ' 1 # 2))))
      (bd_ex
        (bd_and
          (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) n⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) n⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) n⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) n⟩))
              (ϕ ↑ᶠᵇ' 2 # 2)))))
          (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) n⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) n⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) n⟩) (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 0) n⟩))
              (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) n⟩))))))))

/-- Members of the union of a set are precisely members of its members. -/
def axiom_of_union : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (union' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩)))
      (bd_ex (bd_and
        (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))
        (mem' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩))))))

/-- Members of a powerset are precisely subsets of its argument. -/
def axiom_of_powerset : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (Powerset (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩)))
      (bd_all (bd_imp
        (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩))
        (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))))))

/-- The omega constant is the least limit ordinal, with the displayed infinity conditions. -/
def axiom_of_infinity : sentence L_ZFC :=
  bd_and
    (bd_and
      (bd_and
        (mem' ∅' ω')
        (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩) ω')
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) ω')
            (mem' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩)))))))
      (bd_ex (bd_and Ord_f (bd_equal ω' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩)))))
    (bd_all (bd_imp Ord_f (bd_imp
      (bd_and (mem' ∅' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))
            (mem' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩)))))))
      (subset'' ω' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩)))))

/-- Every nonempty set has a membership-minimal element. -/
def axiom_of_regularity : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩) ∅'))
    (bd_ex (bd_and (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
      (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))
        (bd_not (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩))))))))

/-- A nonempty family closed under unions of inclusion chains has an inclusion-maximal member. -/
def zorns_lemma : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 0) (nat_lit 0)⟩) ∅'))
    (bd_imp
      (bd_all (bd_imp
        (bd_and (subset'' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
          (bd_all (bd_all (bd_imp
            (bd_and (mem' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) (nat_lit 0)⟩))
                    (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) (nat_lit 0)⟩)))
            (bd_or (subset'' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩))
                   (subset'' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩)))))))
        (mem' (union' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩)) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))))
      (bd_ex (bd_and (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 0) (nat_lit 0)⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 0) (nat_lit 0)⟩))
          (bd_imp (subset'' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩))
            (bd_equal (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 2) (nat_lit 0)⟩)))))))))

/-- The eight displayed set-theoretic sentences and every instance of strong collection. -/
def ZFC : SentTheory L_ZFC :=
  {axiom_of_emptyset, axiom_of_ordered_pairs, axiom_of_extensionality, axiom_of_union,
   axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma} ∪
  ⋃ (n : ℕ), axiom_of_collection '' (Set.univ : Set (bounded_formula L_ZFC (n + 2)))

/-- The free relation associates equal outputs to equal inputs. -/
def is_func_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (mem' (pair' (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 3) (nat_lit 0)⟩)) (bd_var ⟨4, BoundProof.index_lt (nat_lit 4) (nat_lit 0) (nat_lit 0)⟩))
        (mem' (pair' (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 4) (nat_lit 0)⟩)) (bd_var ⟨4, BoundProof.index_lt (nat_lit 4) (nat_lit 0) (nat_lit 0)⟩)))
      (bd_imp (bd_equal (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 1) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 2) (nat_lit 0)⟩))
              (bd_equal (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 4) (nat_lit 0)⟩)))))))

/-- With free variables `[f,y,x]`, the relation is total from `y` to `x`. -/
def is_total'_f₂ : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 1) (nat_lit 0)⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 4) (nat_lit 0)⟩) (bd_var ⟨4, BoundProof.index_lt (nat_lit 4) (nat_lit 0) (nat_lit 0)⟩))
      (mem' (pair' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 3) (nat_lit 0)⟩) (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 4) (nat_lit 0)⟩)) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 2) (nat_lit 0)⟩)))))

/-- With free variables `[f,y,x]`, the relation is a total function from `y` to `x`. -/
def is_func'_f₂ : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (Nat.le_add_right (nat_lit 1) (nat_lit 2))) is_total'_f₂

/-- With free variables `[y,x]`, some subset of `x` admits a surjection onto `y`. -/
def at_most_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_ex
    (bd_and
      (bd_and
        (subset'' (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 2) (nat_lit 0)⟩) (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 0) (nat_lit 0)⟩))
        (is_func'_f₂.cast (Nat.le_add_right (nat_lit 3) (nat_lit 1))))
      (bd_all (bd_imp (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 4) (nat_lit 0)⟩) (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 1) (nat_lit 0)⟩))
        (bd_ex (bd_and
          (mem' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 5) (nat_lit 0)⟩) (bd_var ⟨3, BoundProof.index_lt (nat_lit 3) (nat_lit 2) (nat_lit 0)⟩))
          (mem' (pair' (bd_var ⟨0, BoundProof.index_lt (nat_lit 0) (nat_lit 5) (nat_lit 0)⟩) (bd_var ⟨1, BoundProof.index_lt (nat_lit 1) (nat_lit 4) (nat_lit 0)⟩)) (bd_var ⟨2, BoundProof.index_lt (nat_lit 2) (nat_lit 3) (nat_lit 0)⟩))))))))

/-- Every ordinal is a surjective image of a subset of omega, or its subset surjects onto the powerset of omega. -/
def CH_f : sentence L_ZFC :=
  bd_all (bd_imp Ord_f
    (bd_or
      (substmax_bounded_formula at_most_f ω')
      (subst0_bounded_formula at_most_f (Powerset omega'))))

namespace ContinuumIndependence

open Fol

/-- A sentence is independent when neither it nor its negation is derivable from the theory. -/
def independent {L : Language} (T : SentTheory L) (f : sentence L) : Prop :=
  (¬ T ⊢ₛ' f) ∧ (¬ T ⊢ₛ' (bd_not f : sentence L))

/-- Neither the concrete CH sentence nor its negation is derivable from the concrete expanded ZFC theory. -/
theorem independence_of_CH : independent ZFC CH_f := by
  sorry

end ContinuumIndependence
