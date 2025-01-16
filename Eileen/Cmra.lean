/-
Authors: Markus de Medeiros

Based on https://gitlab.mpi-sws.org/adamAndMath/iris/tree/fossacs-2025?ref_type=tags
-/

import Eileen.Ofe
import Mathlib.Algebra.Group.Defs

abbrev Pred (T : Sort*) :=
  T -> Prop

abbrev IPred (T : Sort*) :=
  ℕ -> T -> Prop

-- This is different to the Op class from
abbrev Op (α : Type*) := Mul α

abbrev op [Op α] : α -> α -> α := Mul.mul

-- \cdot
-- Alternate notation
notation:60 l:50 " ⬝ " r:50 => l * r

@[simp]
def included [Op α] [Rel α] : Relation α :=
  fun x y => ∃ z, y ≈ x ⬝ z

-- \lessapprox
notation:50 l:50 " ≲ " r:50 => included l r

@[simp]
def iincluded [Op α] [IRel α] : IRelation α :=
  fun n x y => ∃ z, y ≈[ n ] x ⬝ z

notation:50 l:50 " ≲[ " n:50 " ] " r:50 => iincluded n l r


@[simp]
def opM [Op α] (x : α) : Option α -> α
| some y => x ⬝ y
| none => x

-- TODO opM notation


class Valid (α : Sort*) where
  valid : Pred α

export Valid (valid)

-- \checkmark
notation:50 "✓ " r:50 => valid r

class IValid (α : Sort*) where
  ivalid : IPred α

export IValid (ivalid)

notation:50 "✓[ " n:50 " ] " r:50 => ivalid n r

@[simp]
def iidempotent [Op α] [IRel α] : IPred α :=
  fun n x => (x ⬝ x) ≈[n] x

-- Porting: AKA CoreID
@[simp]
def idempotent [Op α] [Rel α] : Pred α :=
  fun x => (x ⬝ x) ≈ x

@[simp]
def exclusive [Op α] [IValid α] : Pred α :=
  fun x => ∀ y, ¬ ✓[0] (x ⬝ y)

@[simp]
def icancelable [Op α] [IRel α] [IValid α] (n : ℕ) (y z : α) : Pred α :=
  fun x => ✓[n] (x ⬝ y) -> (x ⬝ y) ≈[n] (x ⬝ z) -> y ≈[n] z

@[simp]
def cancelable [Op α] [IRel α] [IValid α] : Pred α :=
  fun x => ∀ n y z, icancelable n y z x

@[simp]
def id_free [Op α] [IRel α] [IValid α] : Pred α :=
  fun x => ∀ y, ¬ (✓[0] x ∧ (x ⬝ y) ≈[0] x)

abbrev is_iidempotent_lb [Op α] [IRel α] (x : α) : IPred α :=
  fun n y => y ≲[n] x ∧ iidempotent n y

abbrev is_maximal_iidempotent_lb [IRel α] [CommSemigroup α] (x : α) (n : ℕ) (cx : α)  : Prop :=
  is_iidempotent_lb x n cx ∧ ∀ m y, m ≤ n -> is_iidempotent_lb x m y -> y ≲[m] cx

abbrev no_maximal_iidempotent [IRel α] [CommSemigroup α] (x : α) : Prop :=
  ∀ y, ¬ is_iidempotent_lb y 0 x

-- Note: Defined as a Type so that the choice of cx is relevant
inductive MI.{u} {α : Type u} [OFE α] [IValid α] [CommSemigroup α] : α -> ℕ -> Type (u + 1)
| HasMI (x : α) (n : ℕ) (cx : α) (_ : is_maximal_iidempotent_lb x n cx) : MI x n
| NoMI (x : α) (_ : no_maximal_iidempotent x) : MI x n

class CMRA (α : Type*) extends OFE α, CommSemigroup α, Valid α, IValid α where
  op_nonexpansive (x : α) : nonexpansive (op x) -- Q: Interesting that its not nonexpansive2, why?
  valid_irel_imp_proper n : is_proper1 (irel n) (fun x y => x -> y) (ivalid n)
  valid_iff_forall_ivalid (x : α) : ✓ x <-> ∀ n, ✓[n] x
  valid_of_validS (x : α) (n : ℕ) : ✓[n + 1] x -> ✓[n] x
  ivalid_op_left (x y : α) (n : ℕ) : ✓[n] (x ⬝ y) -> ✓[n] x
  ivalid_irel_prod (x y1 y2 : α) n :
    ✓[n] x -> (x ≈[n] y1 ⬝ y2) -> ∃ (x1 x2 : α), x ≈ x1 ⬝ x2 ∧ x1 ≈[n] y1 ∧ x2 ≈[n] y2
  maximal_idempotent_axiom (x : α) (n : ℕ) (_ : ✓[n] x) : MI x n

export CMRA (op_nonexpansive valid_irel_imp_proper valid_iff_forall_ivalid
             ivalid_op_left valid_of_validS ivalid_irel_prod maximal_idempotent_axiom)

class TotalCMRA (α : Type*) extends CMRA α where
  cmra_total (x : α) : ∃ cx, ∀ n, is_iidempotent_lb x n cx

export TotalCMRA (cmra_total)

class UCMRA (α : Type*) extends CMRA α, MulOneClass α where
  valid_one: ✓ one

abbrev ε {α : Type*} [UCMRA α] := (One.one : α)

export UCMRA (valid_one)


section CMRAUnbundled

namespace CMRA

variable (α β γ : Type*) [CMRA α] [CMRA β] [CMRA γ]

-- TODO Setoid lemmas

lemma valid_of_forall_ivalid (x : α) : (∀ n, ✓[n] x) -> ✓ x := by
  apply (valid_iff_forall_ivalid _).mpr

lemma ivalid_of_forall_valid (x : α) : ✓ x -> (∀ n, ✓[n] x) := by
  apply (valid_iff_forall_ivalid _).mp

lemma op_opM_assoc (x y : α) (z : Option α) : opM (x ⬝ y) z = x ⬝ (opM y z) := by
  cases z <;> simp [opM, mul_assoc]

lemma ivalid_le (x : α) (m n : ℕ) : ✓[n] x -> m ≤ n -> ✓[m] x := by
  intros _ Hle
  induction Hle using Nat.decreasingInduction
  · apply valid_of_validS; trivial
  · trivial

lemma ivalid_op_right (x y : α) (n : ℕ) : ✓[n] (x ⬝ y) -> ✓[n] y := by
  rw [mul_comm]
  apply ivalid_op_left

lemma valid_op_left (x y : α) : ✓(x ⬝ y) -> ✓x := by
  intro
  apply valid_of_forall_ivalid
  intro
  apply ivalid_op_left
  apply ivalid_of_forall_valid
  trivial

lemma valid_op_right (x y : α) : ✓(x ⬝ y) -> ✓y := by
  rw [mul_comm]
  apply valid_op_left


-- def exclusive [Op α] [IValid α] : Pred α :=
--   fun x => ∀ y, ¬ ✓[0] (x ⬝ y)

lemma exclusive_0_left (x y : α) (H : exclusive x) : ¬ ✓[0] (x ⬝ y) := by
  apply H

lemma exclusive_0_right (x y : α) (H : exclusive y) : ¬ ✓[0] (x ⬝ y) := by
  rw [mul_comm]
  apply H

lemma exclusive_left (x y : α) (H : exclusive x) : ¬ ✓(x ⬝ y) := by
  intro H'
  apply H
  apply ivalid_of_forall_valid
  apply H'

lemma exclusive_right (x y : α) (H : exclusive y) : ¬ ✓(x ⬝ y) := by
  rw [mul_comm]
  apply exclusive_left
  apply H

lemma exclusive_opM n (x : α) (H : exclusive x) my (H' : ✓[n] (opM x my)) : my = none := by
  cases my
  · rfl
  simp_all
  apply H
  apply ivalid_le
  · apply H'
  · apply Nat.zero_le

lemma exclusive_includedN n (x y : α) (H : exclusive x) (H' : x ≲[n] y) : ¬ ✓[n] y := by
  -- Do the proper instances
  rcases H' with ⟨ w, _ ⟩
  -- exclusive_left
  sorry

lemma exclusive_included (x y : α) (H : exclusive x) (H' : x ≲ y) : ¬ ✓y := by
  -- Do the proper instances
  sorry

end CMRA

end CMRAUnbundled


-- CMRA Hierarchy



section CMRABundled
/-! ### The category of CMRAs plus Camera morphisms -/

/-- Objects in the category of CMRA's -/
def CMRACat := CategoryTheory.Bundled CMRA

instance : CoeSort CMRACat Type where
  coe := CategoryTheory.Bundled.α

-- attribute [coe] CategoryTheory.Bundled.α
-- attribute [instance] CategoryTheory.Bundled.str

namespace CMRACat

-- TODO: Camera morphisms, and the category CMRA

end CMRACat

end CMRABundled
