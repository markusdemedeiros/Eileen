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

instance : OFE (Excl A) where
  r x y :=
    match (x, y) with
    | (Ex vx, Ex vy) => vx ≈ vy
    | (Bot, Bot) => True
    | _ => False
  ir n x y :=
    match (x, y) with
    | (Ex vx, Ex vy) => vx ≈[n] vy
    | (Bot, Bot) => True
    | _ => False
  iseqv := by
    apply Equivalence.mk
    · intro x
      cases x <;> simp
      apply refl
    · intro x y
      cases x <;> cases y <;> simp
      intro H
      apply symm
      apply H
    · intro x y z _ _
      cases x <;> cases y <;> cases z <;> simp_all
      apply _root_.trans
      · trivial
      · trivial
  isieqv := by
    apply IEquivalence.mk
    · intro x _
      cases x <;> simp
      apply refl
    · intro x y _
      cases x <;> cases y <;> simp
      intro H
      apply symm
      apply H
    · intro x y z _ _ _
      cases x <;> cases y <;> cases z <;> simp_all
      apply _root_.trans
      · trivial
      · trivial
  mono_index := by
    intros _ _ x y H
    cases x <;> cases y <;> simp_all [irel, IRel.ir]
    apply OFE.mono_index H
  refines := by
    simp [rel, irel]
    intros x y
    cases x <;> cases y <;> simp_all
    apply OFE.refines




end Excl
