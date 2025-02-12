/-
Ported by: Markus de Medeiros

Based on ...

TODO items:
-/

import Eileen.Cmra

inductive Excl (A : Type*) where
| Ex (a : A) : Excl A
| Bot : Excl A

abbrev Excl' (A : Type*) := Option (Excl A)
abbrev Excl'.Ex {A : Type*} (x : A) : Excl' A := some (Excl.Ex x)
abbrev Excl'.Bot {A : Type*} (x : A) : Excl' A := some (Excl.Ex x)

namespace Excl

variable (A : Type*) [OFE A]

inductive rel : Excl A -> Excl A -> Prop where
| ExRel vx vy : vx ≈ vy -> rel (Ex vx) (Ex vy)
| BotRel : rel Bot Bot

inductive irel : ℕ -> Excl A -> Excl A -> Prop where
| ExRel n vx vy : vx ≈[n] vy -> irel n (Ex vx) (Ex vy)
| BotRel n : irel n Bot Bot

-- TODO: I'm not sure if I like this yet

@[simp]
lemma ExRel (vx vy : A) : (rel A (Ex vx) (Ex vy)) = (vx ≈ vy) := by
  apply propext; apply Iff.intro
  · intro X; rcases X; trivial
  · intro _; constructor; trivial

@[simp]
lemma BotRel : (rel A Bot Bot) = True := by
  apply propext; apply Iff.intro
  · intro; trivial
  · intro; constructor

@[simp]
lemma ExBotNoRel (v : A) : (rel A (Ex v) Bot) = False := by
  apply propext; apply Iff.intro
  · intro X; rcases X
  · intro _; trivial

@[simp]
lemma BotExNoRel (v : A) : (rel A Bot (Ex v) ) = False := by
  apply propext; apply Iff.intro
  · intro X; rcases X
  · intro _; trivial

@[simp]
lemma ExIrel n (vx vy : A) : (irel A n (Ex vx) (Ex vy)) = (vx ≈[n] vy) := by
  apply propext; apply Iff.intro
  · intro X; rcases X; trivial
  · intro _; constructor; trivial

@[simp]
lemma BotIRel n : (irel A n Bot Bot) = True := by
  apply propext; apply Iff.intro
  · intro; trivial
  · intro; constructor

@[simp]
lemma ExBotNoIrel n (v : A) : (irel A n (Ex v) Bot) = False := by
  apply propext; apply Iff.intro
  · intro X; rcases X
  · intro _; trivial

@[simp]
lemma BotExNoOIrel n (v : A) : (irel A n Bot (Ex v)) = False := by
  apply propext; apply Iff.intro
  · intro X; rcases X
  · intro _; trivial

instance : OFE (Excl A) where
  r := rel A
  ir := irel A
  iseqv := by
    apply Equivalence.mk
    · intro x
      cases x <;> simp
      apply refl
    · intro x y
      cases x <;> cases y <;> simp
      apply symm
    · intro x y z
      cases x <;> cases y <;> cases z <;> simp
      apply _root_.trans
  isieqv := by
    apply IEquivalence.mk
    · intro x _
      cases x <;> simp
      apply refl
    · intro x y _
      cases x <;> cases y <;> simp
      apply symm
    · intro x y z _
      cases x <;> cases y <;> cases z <;> simp
      apply _root_.trans
  mono_index := by
    intros _ _ x y H
    cases x <;> cases y <;> simp_all [_root_.irel, IRel.ir]
    apply OFE.mono_index H
  refines := by
    simp [_root_.rel, _root_.irel]
    intros x y
    cases x <;> cases y <;> simp_all
    apply OFE.refines

lemma Ex_nonexpansive : nonexpansive (Ex : A -> Excl A) := by
  simp [nonexpansive, _root_.irel, IRel.ir]

-- Injectivity

-- COFE: COFE Iso from Option
instance [COFE B] : COFE (Excl B) where
  lim := sorry
  completeness := sorry

instance [DiscreteOFE B] : DiscreteOFE (Excl B) where
  discrete := sorry

-- Leibniz?

lemma Ex_discrete (a : A) (H : discrete a) : discrete (Ex a) := by
  intro y
  rcases y <;> simp [_root_.irel, IRel.ir]
  intro H'
  constructor
  apply H
  apply H'

lemma Bot_discrete : discrete (@Bot A) := by
  intro y
  rcases y <;> simp [_root_.irel, IRel.ir]
  constructor

instance : Valid (Excl A) where
  valid z :=
    match z with
    | Ex _ => True
    | Bot => False

instance : IValid (Excl A) where
  ivalid _ z :=
    match z with
    | Ex _ => True
    | Bot => False

instance : Mul (Excl A) where
  mul _ _ := Bot

instance : CommSemigroup (Excl A) where
  mul_assoc := by simp [HMul.hMul, Mul.mul]
  mul_comm  := by simp [HMul.hMul, Mul.mul]

instance : CMRA (Excl A) where
  op_nonexpansive := by
    intros _ _ _ _ _
    simp [HMul.hMul, Mul.mul]
    apply refl
  valid_irel_imp_proper := by
    intros _ x y _
    cases x <;> cases y <;> simp_all [IValid.ivalid, _root_.irel, IRel.ir]
  valid_iff_forall_ivalid := by
    intro x
    cases x <;> simp [Valid.valid, IValid.ivalid]
  valid_of_validS := by
    intro x _
    cases x <;> simp [Valid.valid, IValid.ivalid]
  ivalid_op_left := by
    intros x y
    cases x <;> cases y <;> simp_all [IValid.ivalid]
  ivalid_irel_prod := by
    intros x y z _
    cases x <;> cases y <;> cases z <;> simp_all [IValid.ivalid, _root_.irel, IRel.ir, HMul.hMul, Mul.mul]
  maximal_idempotent_axiom := by
    intro x n
    cases x <;> simp_all [IValid.ivalid]
    · rename_i x
      intro _
      apply MI.NoMI
      simp [no_maximal_iidempotent, is_iidempotent_lb]
      intro w z
      simp [HMul.hMul, Mul.mul, _root_.irel, IRel.ir]
    · intro F; cases F

end Excl
