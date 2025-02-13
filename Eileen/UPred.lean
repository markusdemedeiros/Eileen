/-
Ported by: Markus de Medeiros

Based on https://gitlab.mpi-sws.org/iris/iris/blob/master/iris/base_logic/upred.v

TODO items:
-/

import Eileen.Cmra

def UPred (M : Type) [UCMRA M] : Type :=
  { pred : ℕ -> M -> Prop // ∀ n1 n2 x1 x2, pred n1 x1 -> x1 ≲[n2] x2 -> n2 ≤ n1 -> pred n2 x2 }

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

-- TODO: Cleanup
instance : COFE (UPred M) where
  lim c :=
    Subtype.mk
      (fun n x => ∀n', n' ≤ n -> ✓[n'] x -> (c n').val n' x)
      (by
        simp only []
        intro n1 n2
        intros x1 x2 H H1 H2 n' H3 H4
        apply (c.car n').property
        · apply H
          · exact Nat.le_trans H3 H2
          · apply CMRA.ivalid_iincluded_ivalid _ _ _ _ H4
            apply CMRA.iincluded_le_mono _ _ _ _ _ H1
            exact H3
        · exact CMRA.iincluded_le_mono M n2 n' x1 x2 H1 H3
        · apply le_refl)
  completeness n c := by
    intro i n' Hin Hv
    simp []
    rcases c with ⟨ c, Hc ⟩
    have H : (c n').val n' i <-> (c n).val n' i := by
      simp_all []
      apply symm
      apply (Hc Hin i n' _ Hv)
      apply Nat.le_refl
    apply (Iff.trans _ H)
    apply Iff.intro
    · intro H3 ; apply H3 <;> trivial
    intro A B C D
    simp []
    apply (Hc C i _ _ D).mp
    · apply (c n').property
      · apply A
      · apply CMRA.iincluded_le_mono _ n'
        · unfold iincluded
          exists 1
          rw [MulOneClass.mul_one]
          apply refl
        · apply C
      · apply C
    · apply le_refl


end UPred
