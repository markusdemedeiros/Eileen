/-
Ported by: Markus de Medeiros

Based on https://gitlab.mpi-sws.org/iris/iris/blob/master/iris/base_logic/upred.v

TODO items:
-/

import Eileen.Cmra

def UPred (M : Type) [UCMRA M] : Type :=
  { pred : ℕ -> M -> Prop // ∀ n1 n2 x1 x2, pred n1 x1 -> x1 ≲[n1] x2 -> n1 ≤ n2 -> pred n2 x2 }

namespace UPred

variable {M : Type} [UCMRA M]

@[simp, reducible]
def rel : Relation (UPred M) := fun p q => ∀ x n, ✓[n] x -> (p.val n x <-> q.val n x)

@[simp, reducible]
def irel : IRelation (UPred M) := fun n p q => ∀ x n', n' ≤ n -> ✓[n'] x -> (p.val n' x <-> q.val n' x)

instance : OFE (UPred M) where
  r := rel
  ir := irel
  iseqv := by
    apply Equivalence.mk
    · intros _ _ _ _
      exact Eq.to_iff rfl
    · unfold rel
      intros _ _ H _ _ _
      apply iff_comm.mp
      apply H; trivial
    · intros _ _ _ H1 H2
      intro _ _ _
      apply Iff.trans
      · apply H1; trivial
      · apply H2; trivial
  isieqv := by
    apply IEquivalence.mk
    · intros _ _ _ _ _ _
      exact Eq.to_iff rfl
    · unfold irel
      intros _ _ _ H _ _ _ _
      apply iff_comm.mp
      apply H <;> trivial
    · intros _ _ _ _ H1 H2 _ _ _  _
      apply Iff.trans
      · apply H1 <;> trivial
      · apply H2 <;> trivial
  mono_index := by
    intros n1 n2 x y Hn1n2 H _ _ H1 _
    apply H
    · apply LE.le.trans H1
      exact Nat.le_of_succ_le Hn1n2
    · trivial
  refines := by
    intros n y
    apply Iff.intro
    · intro P _ n' _
      apply P n'
      · apply le_refl
      · trivial
    · intro P _ _ _ _ _
      apply P
      trivial

end UPred
