/-
Authors: Markus de Medeiros
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Basic
import Eileen.Proper
import Mathlib.Util.WhatsNew

/-!
This file defines ordered families of equivalences (OFE's).

## Main definitions

## Main statements

## Implementation Notes
- Because we have bundled OFE's, it's easier to defined nonexpansive functions as between
  OFE's instead of IRels, even though the latter is more general.
- FIX: Setoid rewrites
- FIX: Why is ``_root_.trans`` necessary but ``_root_.symm`` and ``_root_.refl`` are not?

## References
[Iris: ofe.v](https://gitlab.mpi-sws.org/iris/iris/blob/master/iris/algebra/ofe.v)

-/

-- TODO: Is this not somewhere already??
instance : FunLike (A → B) A B where
  coe f := f
  coe_injective' := by simp [Function.Injective]

/-- A binary relation over T -/
abbrev Relation (T : Sort*) :=
  T -> T -> Prop

/-- A binary relation over T, indexed by ℕ -/
abbrev IRelation (T : Sort*) :=
  ℕ -> T -> T -> Prop

/-- The later constructions on an IRelation -/
@[simp]
def later {T : Sort*} (R : IRelation T) : IRelation T :=
  fun n x y => ∀ m, m < n -> R m x y

/-- The uniform construction on an IRelation -/
@[simp]
def unif {T : Sort*} (R : IRelation T) : Relation T :=
  fun (x y : T) => ∀ i, R i x y

/-- An indexed relation is monotone with respect to index -/
@[simp]
def irelation_mono_index {T : Sort*} (R : IRelation T) : Prop :=
  ∀ {m n}, ∀ {x y : T}, m < n -> R n x y -> R m x y

/-- An indexed relation refines a relation -/
@[simp]
def irelation_refines_relation {T : Sort*} (R : IRelation T) (R' : Relation T) : Prop :=
  ∀ {x y : T}, (∀ n, R n x y) <-> R' x y


/-- An element in an indexed relation is discrete -/
@[simp]
def is_discrete {T : Sort*} (e : T) (R : IRelation T) (R' : Relation T) : Prop :=
  ∀ {y}, (R 0 e y) -> R' e y

/-- An indexed relation is discrete -/
@[simp]
def irelation_discrete {T : Sort*} (R : IRelation T) (R' : Relation T) : Prop :=
  ∀ {x}, is_discrete x R R'


/-- An element in a relation is leibniz -/
@[simp]
def is_leibniz {T : Sort*} (e : T) (R' : Relation T) : Prop :=
  ∀ {y}, (R' e y) -> e = y


/-- An indexed relation is leibniz -/
@[simp]
def relation_leibniz {T : Sort*} (R' : Relation T) : Prop :=
  ∀ {x : T}, is_leibniz x R'



section Relation

/-! ### Declarations about step-indexed relations -/

/-- A type has a distinguished equivalence relation.
Renamed for pairity with IRel.
The equivalence relation has a ``HasEquiv`` instance, so has access to the notation ``(_ ≈ _)``. -/
abbrev Rel := Setoid

/-- The distinguished relation of a Rel. -/
abbrev rel {T : Sort*} [Rel T] : Relation T := Setoid.r

/--
Mathlib relations instace for Rel.
This gives us access to the refl, trans, and symm terms.
-/
instance {T : Sort*} [Rel T] : IsEquiv T rel where
  refl  := Setoid.refl
  symm  := @Setoid.symm _ _
  trans := @Setoid.trans _ _


/-- An indexed relation is an equivalence relation, at each index. -/
structure IEquivalence {T : Sort*} (r : IRelation T) : Prop where
  /-- An indexed equivalence relation is reflexive at each index. -/
  irefl  : ∀ x {n}, r n x x
  /-- An indexed equivalence relation is symmetric at each index. -/
  isymm  : ∀ {x y n}, r n x y → r n y x
  /-- An indexed equivalence relation is transitive at each index. -/
  itrans : ∀ {x y z n}, r n x y → r n y z → r n x z

/-
An indexed setoid is a type with a distinguished indexed equivalence relation,
denoted ``_ ≈[ _ ] _``.
-/
class IRel (T : Sort*) where
  /-- `x ≈[n] y` is the distinguished indexed equivalence relation of an indexed setoid. -/
  ir : IRelation T
  /-- The relation `x ≈[n] y` is an indexed equivalence relation. -/
  isieqv : IEquivalence ir

/-- The distinguished indexed equivalence relation of an indexed setoid -/
abbrev irel {T : Sort*} [IRel T] : IRelation T :=
  IRel.ir

@[inherit_doc] notation:50 l:50 " ≈[" n:50 "] " r:50 => irel n l r

/-- The later construction for an irel. -/
abbrev ilater {T : Sort*} [IRel T] : IRelation T :=
  later irel

@[inherit_doc] notation:50 l:50 " ≈l[" n:50 "] " r:50 => ilater n l r


/-- Mathlib relations instace for IRel at each index. -/
instance {T : Sort*} [IRel T] (n : ℕ) : IsEquiv T (irel n) where
  refl _      := by apply IRel.isieqv.irefl
  symm _ _    := by apply IRel.isieqv.isymm
  trans _ _ _ := by apply IRel.isieqv.itrans

end Relation



section OFEDef

/-! ### Properties of relations and indexed relations which define OFE's -/

variable (T : Sort*)

/-- An indexed relation is monotone with respect to the step index -/
class IRelMono extends IRel T where
  mono_index : @irelation_mono_index T irel

lemma irel_mono {T : Sort*} [IRelMono T] : ∀ {m n}, ∀ {x y : T}, m < n -> x ≈[n] y -> x ≈[m] y := by
  apply IRelMono.mono_index

lemma irel_le_mono {T : Sort*} [IRelMono T] : ∀ {m n}, ∀ {x y : T}, m ≤ n -> x ≈[n] y -> x ≈[m] y := by
  intros _ _ _ _ H
  cases (Nat.eq_or_lt_of_le H)
  · simp_all
  · rename_i H
    intro _
    apply (irel_mono H)
    trivial

lemma irel_mono_le {T : Sort*} [IRelMono T] : ∀ {m n}, ∀ {x y : T}, x ≈[n] y -> m ≤ n -> x ≈[m] y := by
  intros
  rename_i H
  apply irel_le_mono H
  trivial

/-- An indexed relation is an indexed refinement of an equivalence relation -/
class IRelLimit extends Rel T, IRel T where
  refines : @irelation_refines_relation T irel rel

lemma irel_iff_rel [IRelLimit T] : ∀ {x y : T}, (∀ n, x ≈[n] y) <-> x ≈ y := by
  apply IRelLimit.refines

lemma forall_irel_of_rel [IRelLimit T] : ∀ {x y : T}, x ≈ y -> ∀ {n}, x ≈[n] y := by
  intros
  apply IRelLimit.refines.mpr
  trivial

lemma rel_of_forall_irel [IRelLimit T] : ∀ {x y : T}, (∀ n, x ≈[n] y) -> x ≈ y := by
  intros
  apply IRelLimit.refines.mp
  trivial

end OFEDef


/--
An ordered family of equivlances.
-/
class OFE (T : Sort*) extends Rel T, IRel T, IRelMono T, IRelLimit T

section OFEFunctions

/-!
#### Nonexpansive functions

NOTE: We define nonexpansive functions with respect to OFE's rather than indexed relations,
because it simplifies the bundling process. More generality is possible.
-/

variable {T1 T2 T3 T4 : Sort*}
variable [OFE T1] [OFE T2] [OFE T3] [OFE T4]

@[simp]
def nonexpansive (f : T1 -> T2) : Prop :=
  ∀ {i : ℕ}, is_proper1 (irel i) (irel i) f

@[simp]
def nonexpansive2 (f : T1 -> T2 -> T3) : Prop :=
  ∀ {i : ℕ}, is_proper2 (irel i) (irel i) (irel i) f

@[simp]
def nonexpansive3 (f : T1 -> T2 -> T3 -> T4) : Prop :=
  ∀ {i : ℕ}, is_proper3 (irel i) (irel i) (irel i) (irel i) f

@[simp]
def contractive (f : T1 -> T2) : Prop :=
  ∀ {i : ℕ}, is_proper1 (later irel i) (irel i) f

@[simp]
def contractive2 (f : T1 -> T2 -> T3) : Prop :=
  ∀ {i : ℕ}, is_proper2 (later irel i) (later irel i) (irel i) f

@[simp]
def contractive3 (f : T1 -> T2 -> T3 -> T4) : Prop :=
  ∀ {i : ℕ}, is_proper3 (later irel i) (later irel i) (later irel i) (irel i) f

@[simp]
def anticontractive (f : T1 -> T2) : Prop :=
  ∀ {i : ℕ}, is_proper1 (irel i) (later irel i) f

lemma nonexpansive_of_contractive (f : T1 -> T2) (H : contractive f) :
    nonexpansive f := by
  intro i x y H'
  apply H
  intro m Hm
  apply irel_mono Hm H'

/-- The identity function is nonexpansive -/
lemma id_nonexpansive : nonexpansive (@id T1) := by
  simp


/-- The composition of nonexpansive functions is nonexpansive -/
lemma cmp_nonexpansive {f : T1 -> T2} {g : T2 -> T3} (H1 : nonexpansive f) (H2 : nonexpansive g) :
    nonexpansive (g ∘ f) := by
  simp only [nonexpansive, is_proper1, Function.comp_apply]
  intros
  apply H2
  apply H1
  trivial

end OFEFunctions


namespace OFE

/-! ### Lemmas about OFE's -/

variable {T1 T2 : Sort*}
variable [OFE T1] [OFE T2]

lemma nonexpansive_equiv_equiv_proper {f : T1 -> T2} (H : nonexpansive f) :
    is_proper1 rel rel f := by
  intro _ _ H'
  apply rel_of_forall_irel
  intro _
  apply H
  apply forall_irel_of_rel
  apply H'

end OFE




section OFELater

/-! ### Properties of the later construction in OFE's -/

variable  {T : Sort*}
variable [OFE T]

def later_IEquivalence : @IEquivalence T (later irel) where
  irefl := by
    intro _ m _ _
    apply irel_mono
    · trivial
    · apply refl
  isymm := by
    intro _ _ _ HL _ _
    apply symm
    apply HL
    trivial
  itrans := by
    intro _ _ _ _ HL1 HL2 _ Hm
    apply _root_.trans -- FIXME: _root_
    · apply HL1 _ Hm
    · apply HL2 _ Hm

lemma later_of_rel (x y : T) (i : ℕ) : x ≈[i] y -> x ≈l[i] y := by
  intro _ _ Hm
  apply irel_mono Hm
  trivial

lemma lt_later_rel (x y : T) (m n : ℕ) :
    (m < n) -> x ≈l[n] y -> x ≈[m] y := by
  intro _ H
  apply H
  trivial

/-- All elements are later-related at index 0 -/
lemma later_rel_0 (x y : T) : x ≈l[0] y := by
  intro _ Hm
  exfalso
  simp_all

/-- All elements are later-related at n+1 exactly when they are related at n -/
lemma rel_iff_later_rel_S (x y : T) (n : ℕ) : x ≈[n] y <-> x ≈l[n + 1] y := by
  apply Iff.intro
  · intro H' m Hm
    apply irel_le_mono
    · apply Nat.lt_succ_iff.mp Hm
    · trivial
  · intro H'
    apply H'
    apply Nat.lt_add_one

lemma later_rel_S_of_rel {x y : T} {n : ℕ} (H : x ≈[n] y) : x ≈l[n + 1] y:= by
  apply (rel_iff_later_rel_S _ _ _).mp H

lemma rel_of_later_rel_S {x y : T} {n : ℕ} (H : x ≈l[n + 1] y) : x ≈[n] y := by
  apply (rel_iff_later_rel_S _ _ _).mpr H

/-- The later construction on an OFE also refines its equivalence -/
lemma later_rel_refines_rel : @irelation_refines_relation T (later irel) rel := by
  intro x y
  apply Iff.intro
  · intro H
    apply rel_of_forall_irel
    intro _
    apply rel_of_later_rel_S
    apply H
  · intro _ _ _ _
    apply forall_irel_of_rel
    trivial


lemma later_equivalence : @IEquivalence T (later irel) where
  irefl := by
    intro _ _ _ _
    apply refl
  isymm := by
    intros _ _ _ H _ _
    apply symm
    apply H
    trivial
  itrans := by
    intros _ _ _ _ H1 H2 _ _
    apply _root_.trans
    · apply H1
      trivial
    · apply H2
      trivial

lemma later_mono_index : @irelation_mono_index T (later irel) := by
  intros _ _ _ _ _ H _ _
  apply irel_mono _ ?G
  case G =>
    apply H
    trivial
  trivial

end OFELater


section NonExpansiveBundled
/-! ### Bundled NonExpansive maps  -/

/-- [semi-bundled] [2.1] A nonexpansive function between two OFE's -/
@[ext]
structure NonExpansive (M N : Sort*) [OFE M] [OFE N] where
  toFun : M -> N
  is_nonexpansive : nonexpansive toFun

attribute [simp] NonExpansive.toFun

infixr:25 " -n> " => NonExpansive

/-- A type F behaves like an nonexpansive function from M to N at each index  -/
class NonExpansiveClass (F : Sort*) (M N : outParam Sort*) [OFE M] [OFE N] extends
     FunLike F M N where
  is_nonexpansive : ∀ f : F, nonexpansive f

/-- Coerce a NonExpansiveClass to a bundled NonExpansived map -/
@[coe]
def NonExpansiveClass.toNonExpansive {F : Sort*} {M N : outParam Sort*} [OFE M] [OFE N] [NonExpansiveClass F M N] (f : F) :
    M -n> N where
  toFun := f
  is_nonexpansive := by apply is_nonexpansive

attribute [simp] NonExpansive.toFun

instance {F : Sort*} {M N : outParam Sort*} [OFE M] [OFE N] [NonExpansiveClass F M N] : CoeTC F (M -n> N) where
  coe := NonExpansiveClass.toNonExpansive

-- -- [2.?] Coercion between a term that behaves like a nonexpansive function, and the structure
-- instance [OFE M] [OFE N] [NonExpansiveClass F M N] : CoeOut F (NonExpansive M N) where
--   coe F := NonExpansive.mk F (NonExpansiveClass.is_nonexpansive F)

/-- The NonExpansive structure behaves like a function -/
instance (M N : Sort*) [OFE M] [OFE N] : FunLike (M -n> N) M N where
  coe := fun F x => F.toFun x
  coe_injective' := by
    intro x y H
    cases x
    congr

/-- The structure behaves like a nonexpansive function-/
instance (M N : Sort*) [OFE M] [OFE N] : NonExpansiveClass (NonExpansive M N) M N where
  is_nonexpansive := by
    simp [DFunLike.coe]
    intro f _ _ _ _
    apply f.is_nonexpansive
    trivial

-- -- [2.?] Regular functions can be lifted to nonexpansive functions, provided they are nonexpansive
-- instance [OFE M] [OFE N] : CanLift (M -> N) (M -n> N) DFunLike.coe nonexpansive where
--   prf := by
--     simp [DFunLike.coe]
--     intros f H
--     exists NonExpansive.mk f H

/-- The term f has a proof of its nonexpansivity -/
class HasNonExpansive [OFE M] [OFE N] [FunLike F M N] (f : F) : Prop where
  is_nonexpansive : nonexpansive f

/-- All terms of a nonexpansive type have a proof of their nonexpansivity -/
instance [OFE M] [OFE N] [NonExpansiveClass F M N] (f : F) : HasNonExpansive f where
  is_nonexpansive := by apply NonExpansiveClass.is_nonexpansive

namespace NonExpansive

/-- An instance of the struct for a function which has a nonexpansive proof -/
def lift [OFE M] [OFE N] [FunLike F M N] (f : F) [HasNonExpansive f] : NonExpansive M N where
  toFun := f
  is_nonexpansive := HasNonExpansive.is_nonexpansive

-- FIXME: Rename
/-- The (bundled) identity morphism in the category of OFE+NonExpansive functions -/
def cid (M : Type) [OFE M] : M -n> M where
  toFun := @_root_.id _
  is_nonexpansive := id_nonexpansive


@[simp]
lemma coe_cid [OFE T] : ⇑(NonExpansive.cid T) = _root_.id := by rfl

@[simp]
lemma id_apply [OFE T] (t : T ): NonExpansive.cid T t = t := by rfl

-- FIXME: Rename
/-- The (bundled) constant nonexpansive function -/
def cconst [OFE α] [OFE β] (x : β) : α -n> β where
  toFun _ := x
  is_nonexpansive := by
    simp [nonexpansive]
    intros
    apply refl

-- FIXME: Rename
/-- The (bundled) composition of morphisms in the category of OFE+NonExpansive functions -/
def ccompose [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  toFun := g ∘ f
  is_nonexpansive := by
    simp only [DFunLike.coe]
    apply cmp_nonexpansive
    · apply is_nonexpansive
    · apply is_nonexpansive

@[inherit_doc] notation:60 l:60 " ⊙ " r:60 => NonExpansive.ccompose l r

lemma ccompose_assoc [OFE α] [OFE β] [OFE γ] [OFE δ] {h : γ -n> δ} {g : β -n> γ} {f : α -n> β} :
    (h ⊙ g) ⊙ f = h ⊙ (g ⊙ f) := by rfl

@[simp]
lemma coe_ccompose [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) :
    (g ⊙ f : α -> γ) = g ∘ f := by
  rfl

@[simp]
lemma ccompose_apply [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) (x : α) :
    (g ⊙ f) x = g (f x) := by
  rfl

@[simp]
lemma ccompose_cid [OFE α] [OFE β] (f : α -n> β) :
    f ⊙ (NonExpansive.cid α) = f := by
  rfl

@[simp]
lemma cid_ccompose [OFE α] [OFE β] (f : α -n> β) :
    (NonExpansive.cid β) ⊙ f = f := by
  rfl

/- Would probably be nice to port these

@[simp]
theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => RingHom.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

-/


/-- A "map" of nonexpansive functions. -/
def map [OFE A] [OFE B] [OFE A'] [OFE B']
    (f : A' -n> A) (g : B -n> B') (x : A -n> B) : (A' -n> B') :=
  g ⊙ (x ⊙ f)

end NonExpansive
end NonExpansiveBundled



section ContractiveBundled

/-! ### Bundled Contractive maps  -/

/-- A contractive function between two OFE's -/
@[ext]
structure Contractive (M N : Sort*) [OFE M] [OFE N]  extends NonExpansive M N where
  is_contractive : contractive toFun

infixr:25 " -c> " => Contractive

/-- The type F behaves like a contractive function -/
class ContractiveClass (F : Sort*) (M N : outParam Sort*) [OFE M] [OFE N] extends
    NonExpansiveClass F M N where
  is_contractive : ∀ f : F, contractive f

instance [OFE M] [OFE N] [ContractiveClass F M N] : NonExpansiveClass F M N where
  is_nonexpansive f := by
    apply nonexpansive_of_contractive
    apply ContractiveClass.is_contractive

@[coe]
def ContractiveClass.toContractive {F : Sort*} {M N : outParam Sort*} [OFE M] [OFE N] [ContractiveClass F M N] (f : F) :
    M -c> N where
  toFun := f
  is_nonexpansive := by apply NonExpansiveClass.is_nonexpansive
  is_contractive := by apply is_contractive

instance {F : Sort*} {M N : outParam Sort*} [OFE M] [OFE N] [ContractiveClass F M N] : CoeTC F (M -c> N) where
  coe := ContractiveClass.toContractive

instance (M N : Sort*) [OFE M] [OFE N] : FunLike (M -c> N) M N where
  coe := fun F x => F.toFun x
  -- TODO: Simplify
  coe_injective' := by
    intro x y H
    cases x
    cases y
    simp_all
    ext
    simp_all

instance (M N : Sort*) [OFE M] [OFE N] : ContractiveClass (Contractive M N) M N where
  is_contractive := by
    simp [DFunLike.coe]
    intro f _ _ _ _
    apply f.is_contractive
    trivial
  is_nonexpansive := by
    simp [DFunLike.coe]
    intro f
    apply nonexpansive_of_contractive
    rcases f
    apply Contractive.is_contractive

/-- The term f behaves has a proof of contractivity -/
class HasContractive [OFE M] [OFE N] [FunLike F M N] (f : F) where
  is_contractive : contractive f

/-- Any term is a type of contractive functions has a proof of contractivity -/
instance [OFE M] [OFE N] [ContractiveClass F M N] (f : F) : HasContractive f where
  is_contractive := by apply ContractiveClass.is_contractive


namespace Contractive

/-- Obtain a Contractive struct for any term which has a proof of contractivity -/
def lift [OFE M] [OFE N] [FunLike F M N] (f : F) [HasContractive f] : Contractive M N where
  toFun := f
  is_nonexpansive := by
    apply nonexpansive_of_contractive
    apply HasContractive.is_contractive
  is_contractive := HasContractive.is_contractive

-- /-- The (bundled) composition of morphisms in the category of OFE+NonExpansive functions -/
-- def Contractive.comp [OFE α] [OFE β] [OFE γ] (g : β -c> γ) (f : α -c> β) : α -c> γ where
--   toFun := g ∘ f
--   is_nonexpansive := by
--     simp only [DFunLike.coe]
--     apply cmp_nonexpansive
--     · apply NonExpansive.is_nonexpansive
--     · apply NonExpansive.is_nonexpansive
--   is_contractive := by
--     sorry

-- lemma Contractive.comp_assoc [OFE α] [OFE β] [OFE γ] [OFE δ] {h : γ -c> δ} {g : β -c> γ} {f : α -c> β} :
--     (h.comp g).comp f = h.comp (g.comp f) := by rfl

@[simp]
lemma coe_ccompose [OFE α] [OFE β] [OFE γ] (g : β -c> γ) (f : α -c> β) :
    (g.ccompose f : α -> γ) = g ∘ f := by
  rfl

@[simp]
lemma ccompose_apply [OFE α] [OFE β] [OFE γ] (g : β -c> γ) (f : α -c> β) (x : α) :
    (g.ccompose f) x = g (f x) := by
  rfl

end Contractive
end ContractiveBundled

section OFEDiscrete

/-! ### Definition for a type with a discrete OFE -/

/-- [semi-bundled] A discrete OFE is an OFE where all elements are discrete -/
class DiscreteOFE (T : Sort*) extends OFE T where
  discrete : ∀ (x : T), is_discrete x irel rel

lemma rel_of_irel_0 {T : Sort*} [DiscreteOFE T] :
    ∀ {x y : T}, x ≈[0] y -> x ≈ y := by
  intros
  apply DiscreteOFE.discrete
  trivial


/--
discreteO is the default discrete OFE over a type with an equivalence relation
-/
structure discreteO (T : Type) : Type where
  t : T

prefix:max  "Δ"  => discreteO

instance [Rel T] : DiscreteOFE (Δ T) where
  r x y := rel x.t y.t
  ir _ x y := rel x.t y.t
  iseqv := by
    apply Equivalence.mk
    · intro
      apply refl
    · intros
      apply symm
      trivial
    · intros
      apply _root_.trans
      · trivial
      · trivial
  isieqv := by
    apply IEquivalence.mk
    · intros
      apply refl
    · simp
      intros
      apply symm
      trivial
    · simp
      intros
      apply _root_.trans
      · trivial
      · trivial
  mono_index := by simp [irel]
  refines := by simp [rel, irel]
  discrete := by simp [rel, irel]

lemma discrete_irel_iff_rel {T : Sort*} [DiscreteOFE T] (n : ℕ) (x y : T) :
    (x ≈[n] y) <-> x ≈ y := by
  apply Iff.intro
  · intro H
    apply DiscreteOFE.discrete
    apply irel_mono_le
    · apply H
    · apply Nat.zero_le
  · intros
    apply forall_irel_of_rel
    trivial

end OFEDiscrete


section OFENonexpansive

/-! ### OFE on nonexpansive functions  -/

/-- The canoncial instance of an OFE on a bundled nonexpansive function -/
instance [OFE A] [OFE B] : OFE (A -n> B) where
  r f g := ∀ x, f x ≈ g x
  ir n f g := ∀ x, f x ≈[n] g x
  iseqv := by
    apply Equivalence.mk
    · intros
      apply refl
    · intros _ _ H _
      apply symm
      apply H
    · intros _ _ _ H1 H2 _
      apply _root_.trans
      · apply H1
      · apply H2
  isieqv := by
    apply IEquivalence.mk <;> intro n
    · intros
      apply refl
    · intros _ _ H _
      apply symm
      apply H
    · intros _ _ _ H1 H2 _
      apply _root_.trans
      · apply H1
      · apply H2
  mono_index := by
    simp [irel]
    intros _ _ _ _ H1 H2 _
    apply irel_mono H1
    apply H2
  refines := by
    intros _ _
    apply Iff.intro
    · intros H _
      apply rel_of_forall_irel
      intro _
      apply H
    · intros H _ _
      apply forall_irel_of_rel
      apply H

/-- Composition in the category of OFE's is nonexpansive -/
lemma ccompose_nonexpansive [OFE α] [OFE β] [OFE γ] :
    nonexpansive2 (@NonExpansive.ccompose α β γ _ _ _) := by
  simp [nonexpansive2]
  intro _ _ _ _ _ H1 H2 _
  simp [NonExpansive.ccompose, DFunLike.coe]
  -- FIXME: Setoid
  apply _root_.trans
  · apply NonExpansive.is_nonexpansive
    apply H2
  apply symm
  apply _root_.trans
  · apply symm
    apply H1
  apply refl


/-- Composition in the category of COFE's is proper with respect to equivalence -/
lemma eq_proper_ccompose [OFE α] [OFE β] [OFE γ] :
    is_proper2 rel rel rel (@NonExpansive.ccompose α β γ _ _ _) := by
  simp [NonExpansive.ccompose, DFunLike.coe]
  intros _ _ _ _ H1 H2 _
  -- FIXME: Setoid
  simp [DFunLike.coe]
  apply _root_.trans
  · apply H1
  apply OFE.nonexpansive_equiv_equiv_proper
  · apply @NonExpansive.is_nonexpansive
  apply _root_.trans
  · apply H2
  apply OFE.nonexpansive_equiv_equiv_proper
  · apply @NonExpansive.is_nonexpansive
  apply refl



lemma NonExpansive.map_nonexpansive [OFE A] [OFE B] [OFE A'] [OFE B'] :
    nonexpansive3 (@NonExpansive.map A B A' B' _ _ _ _) := by
  simp [nonexpansive3, NonExpansive.map]
  intro _ _ _ _ _ _ _ H1 H2 H3 x
  -- FIXME: Setoid
  apply ccompose_nonexpansive
  · apply H2
  apply ccompose_nonexpansive
  · apply H3
  · apply H1

end OFENonexpansive



section Chains

/-! ### Chains -/


/-- [unbundled] A function c satisfies the chain property -/
@[simp]
def chain_is_cauchy {T : Sort*} [OFE T] (c : ℕ -> T) : Prop :=
  ∀ {m n : Nat}, n ≤ m -> (c m) ≈[n] (c n)

/-- The type of functions which satisfy the chain property -/
structure Chain (T : Sort*) [OFE T] where
  car : ℕ -> T
  is_cauchy : chain_is_cauchy car

instance [OFE T] : CoeFun (Chain T) (fun _ => (Nat -> T)) where
  coe s := s.1

lemma Chain.cauchy [OFE T] (c : Chain T) : ∀ {m n : Nat}, n ≤ m -> (c m) ≈[n] (c n) := by
  rcases c with ⟨ _, cauchy ⟩
  simp
  intros
  apply cauchy
  trivial


/-- Map a nonexpansive function throguh a chain -/
def Chain.map {α β : Sort*} [OFE α] [OFE β] {f : α -> β} (c : Chain α) (Hf : nonexpansive f) : Chain β where
  car := f ∘ c
  is_cauchy := by
    rcases c with ⟨ c', Hc' ⟩
    simp [chain_is_cauchy, DFunLike.coe ]
    intros m n Hnm
    simp at Hc'
    apply Hf
    apply Hc'
    apply Hnm

def Chain.const {α : Sort*} [OFE α] (x : α) : Chain α where
  car _ := x
  is_cauchy := by
    intro _ _ _
    simp
    apply refl

/-- Apply a chain of nonexpansive functions to a value, yielding another chain -/
@[simp]
def Chain.app [OFE α] [OFE β] (c : Chain (α -n> β)) (x : α) : Chain β where
  car n := c n x
  is_cauchy := by
    intro _ _ _
    simp only [chain_is_cauchy, irel]
    rcases c with ⟨ f, cauchy ⟩ -- FIXME: chain_is_cauchy'
    simp only []
    apply cauchy
    trivial

end Chains



section COFE

/-! ### COFEs -/

class COFE (α : Sort*) extends OFE α where
  lim : Chain α -> α
  completeness : ∀ (n : Nat), ∀ (c : Chain α), (lim c) ≈[n] (c n)

-- -- Unbundled type which says that an OFE is a COFE
structure COFEMixin (α : Sort*) [OFE α] where
  lim : Chain α -> α
  completeness : ∀ (n : Nat), ∀ (c : Chain α), (lim c) ≈[n] (c n)

abbrev COFEMixin.toCOFE (α : Sort*) [OFE α] (M : COFEMixin α) : COFE α where
  lim := M.lim
  completeness := M.completeness


/-- COFE limit commutes with nonexpansive maps -/
lemma COFE.lim_map_nonexpansive [COFE α] [COFE β] (f : α -> β) (c : Chain α) (Hf : nonexpansive f) :
    lim (Chain.map c Hf) ≈ f (lim c) := by
  apply rel_of_forall_irel
  intro n
  -- NOTE: Setoid rewrite
  apply _root_.trans
  · apply COFE.completeness
  · apply symm
    apply Hf
    apply COFE.completeness


/-- Limit of a constant chain -/
lemma COFE.lim_const {α : Sort*} [COFE α] (x : α) :
    lim (Chain.const x) ≈ x := by
  apply rel_of_forall_irel
  intro _
  apply COFE.completeness


/-- COFE of nonexpansive functions between two COFE's -/
instance [OFE α] [COFE β] : COFE (α -n> β) where
  lim c :=
    let f (x : α) : β := COFE.lim <| Chain.app c x
    let ne : nonexpansive f := by
      simp
      intro n x y H
      -- FIXME: Setoids
      apply _root_.trans
      · apply COFE.completeness
      -- _ (nonexpansive_app_chain c x)
      apply symm
      apply _root_.trans
      · apply COFE.completeness -- _ (nonexpansive_app_chain c y)
      apply symm
      simp
      apply NonExpansive.is_nonexpansive
      trivial
    NonExpansive.mk f ne
  completeness := by
    intro n c
    intro x
    -- FIXME: annoying coercion
    rcases c with ⟨ c, cauchy ⟩
    simp [DFunLike.coe]
    -- FIXME: Setoids
    apply _root_.trans
    · apply COFE.completeness
    simp
    apply refl

end COFE




section LimitPreserving
/-! ### Limit preserving propositions -/

variable {α : Sort*}
variable [COFE α]

/-- A predicate is true on the limit of a chain if it is true at every point -/
@[simp]
def limit_preserving (P : α -> Prop) : Prop :=
  ∀ (c : Chain α), (∀ n, P (c n)) -> P (COFE.lim c)

lemma limit_preserving.ext (P Q : α -> Prop) :
    (∀ x, P x = Q x) -> limit_preserving P -> limit_preserving Q := by
  intro H
  rewrite [<- funext H]
  simp only [imp_self]


lemma limit_preserving.const (P : Prop) : limit_preserving (fun (_ : α) => P) := by
  simp

/-
lemma limit_preserving_discrete [COFE α] (P : α -> Prop) :
    proper1 (IRel.irel 0) Eq P -> limit_preserving P := by
  intros HP _ _
  sorry
-/


lemma limit_preserving.and (P Q : α -> Prop) :
    limit_preserving P -> limit_preserving Q -> limit_preserving (fun a => P a ∧ Q a):= by
  simp
  intros H1 H2 _ H3
  apply And.intro
  · apply H1
    intro n
    cases (H3 n)
    trivial
  · apply H2
    intro n
    cases (H3 n)
    trivial

/-
lemma limit_preserving.imp [COFE α] (P Q : α -> Prop) :
    limit_preserving P -> limit_preserving Q -> limit_preserving (fun a => P a -> Q a):= by
  simp
  sorry

lemma limit_preserving.forall [COFE α] (P : β -> α -> Prop) :
    (∀ b, limit_preserving (P b)) -> limit_preserving (fun a => ∀ b, P b a):= by
  simp
  sorry

lemma limit_preserving.equiv [COFE α] [COFE β] (f g : α -> β)
    (Hf : nonexpansive f) (Hg : nonexpansive g) :
    limit_preserving (fun a => f a ≈ g a) := by
  simp
  sorry
-/


end LimitPreserving





section Contractive

/-! ### Contractive functions -/

variable {α β : Sort*}
variable [OFE α] [OFE β]

lemma contractive_rel_0 (f : α -> β) (H : contractive f) x y :
    f x ≈[ 0 ] f y := by
  apply H
  apply later_rel_0

lemma contractive_rel_S_of_rel (f : α -> β) (H : contractive f) x y n :
    (x ≈[ n ] y) -> f x ≈[ n + 1 ] f y := by
  intro _
  apply H
  apply later_rel_S_of_rel
  trivial

lemma contractive_rel_of_later (f : α -> β) (H : contractive f) x y n :
    (x ≈l[n] y) -> f x ≈[ n ] f y := by
  intro _
  apply H
  trivial

lemma const_contractive (x : β) : contractive (fun (_ : α) => x) := by
  intro _ _ _ _
  apply refl

end Contractive



section Fixpoint

/-! ## Fixpoint construction in a COFE -/

variable {α : Type*}


def fixpoint_chain [OFE α] [Inhabited α] (f : α -> α) (H : contractive f) : Chain α where
  car n := Nat.repeat f (n + 1) default
  is_cauchy := by
    simp [chain_is_cauchy]
    intro n
    induction n
    · intro i
      cases i
      · intro
        apply refl
      · simp
    · rename_i n IH
      intro i
      simp [Nat.repeat]
      cases i
      · intro
        apply contractive_rel_0
        apply H
      · intro
        apply contractive_rel_S_of_rel
        · apply H
        apply IH
        simp_all only [Nat.add_le_add_iff_right]


/-- The fixpoint chain of a contractive function -/
def Contractive.fixpoint_chain [COFE α] [Inhabited α] (f : α -c> α) : Chain α :=
  _root_.fixpoint_chain f f.is_contractive

/-- The fixpoint of a contractive function -/
def Contractive.fixpoint [COFE α] [Inhabited α] (f : α -c> α) : α :=
  COFE.lim (Contractive.fixpoint_chain f)

/-- Fixpoint unfolding lemma -/
lemma Contractive.fixpoint_unfold [COFE α] [Inhabited α] (f : α -c> α) :
    Contractive.fixpoint f ≈ f (Contractive.fixpoint f) := by
  apply rel_of_forall_irel
  intro n
  -- FIXME: Setoid
  apply _root_.trans
  · apply COFE.completeness n (fixpoint_chain f)
  apply symm
  apply _root_.trans
  · apply HasNonExpansive.is_nonexpansive
    apply COFE.completeness
  apply symm
  induction n
  · simp [DFunLike.coe]
    apply (contractive_rel_0 f f.is_contractive)
  · rename_i n IH
    apply (contractive_rel_S_of_rel f f.is_contractive)
    apply IH

lemma Contractive.fixpoint_unique [COFE α] [Inhabited α] (f : α -c> α) (x : α) :
    (x ≈ f x) -> x ≈ fixpoint f := by
  intro H
  apply rel_of_forall_irel
  intro n
  -- FIXME: Setoid
  let L := Contractive.fixpoint_unfold f
  induction n
  · apply _root_.trans
    · apply forall_irel_of_rel
      apply H
    apply symm
    apply _root_.trans
    · apply forall_irel_of_rel
      apply L
    apply symm
    apply (contractive_rel_0 f f.is_contractive)
  · rename_i n IH
    apply _root_.trans
    · apply forall_irel_of_rel
      apply H
    apply symm
    apply _root_.trans
    · apply forall_irel_of_rel
      apply L
    apply symm
    apply (contractive_rel_S_of_rel f f.is_contractive)
    apply IH


lemma Contractive.fixpoint_nonexpansive' [COFE α] [Inhabited α] (f g : α -c> α) n :
    (∀ z, f z ≈[n] g z) -> fixpoint f ≈[n] fixpoint g := by
  intro H
  -- FIXME: Setoid
  apply _root_.trans
  · apply COFE.completeness
  apply symm
  apply _root_.trans
  · apply COFE.completeness
  apply symm
  simp [fixpoint_chain, _root_.fixpoint_chain, Nat.repeat]
  induction n
  · apply H
  rename_i n IH
  simp [Nat.repeat]
  apply _root_.trans
  · apply H
  apply Contractive.is_contractive
  apply later_rel_S_of_rel
  apply IH
  intro i
  apply irel_mono_le
  · apply H
  · simp

lemma Contractive.fixpoint_proper [COFE α] [Inhabited α] (f g : α -c> α) :
    (∀ x, f x ≈ g x) -> fixpoint f ≈ fixpoint g := by
  intro H
  apply rel_of_forall_irel
  intro
  apply Contractive.fixpoint_nonexpansive'
  intro z
  apply forall_irel_of_rel
  apply (H z)


-- TODO: What's a Lean-appropriate induction principle?
lemma Contractive.fixpoint_ind [COFE α] [Inhabited α] (f : α -c> α)
    (P : α -> Prop) (HP : is_proper1 rel (fun A B => A -> B) P)
    (Hbase : ∃ x, P x) (Hind : ∀ x, P x -> P (f x)) (Hlim : limit_preserving P) :
    P (fixpoint f) := by
  rcases Hbase with ⟨ x, Hx ⟩
  let chain : Chain α :=
    ⟨ fun i => Nat.repeat f (i + 1) x,
      by
        intro n
        simp only []
        induction n
        · simp [refl]
        · rename_i i IH
          intros n H
          simp [Nat.repeat]
          apply Contractive.is_contractive
          cases n
          · apply later_rel_0
          rename_i n
          apply later_rel_S_of_rel
          apply IH
          simp_all ⟩
  apply HP
  · apply Contractive.fixpoint_unique f (COFE.lim chain)
    apply rel_of_forall_irel
    intro n
    -- FIXME: Setoid
    apply _root_.trans
    · apply COFE.completeness
    apply symm
    apply _root_.trans
    · apply HasNonExpansive.is_nonexpansive
      apply COFE.completeness
    apply symm
    simp [chain, Nat.repeat]
    induction n
    · apply Contractive.is_contractive
      apply later_rel_0
    rename_i i IH
    simp [Nat.repeat]
    apply Contractive.is_contractive
    apply later_rel_S_of_rel
    apply IH
  apply Hlim
  intros n
  simp [Nat.repeat]
  induction n
  · simp [Nat.repeat]
    apply Hind
    apply Hx
  · rename_i n IH
    simp [Nat.repeat]
    apply Hind
    apply IH

end Fixpoint



section Unit

/-! ### Unit OFE -/

def unitO : Type := Unit

instance : DiscreteOFE unitO where
  ir _ _ _ := True
  r _ _ := True
  iseqv := by simp [Equivalence.mk]
  isieqv := by simp [IEquivalence.mk]
  mono_index := by simp [irel]
  refines := by simp [rel, irel]
  discrete := by simp  [rel, irel]

instance unitO_COFE : COFE unitO where
  lim _ := Unit.unit
  completeness _ _ := by simp [irel, IRel.ir]

end Unit


section Empty

/-! ### Empty type -/

def emptyO : Type := Empty
instance : DiscreteOFE emptyO where
  ir _ _ _ := True
  r _ _ := True
  iseqv := by simp [Equivalence.mk]
  isieqv := by simp [IEquivalence.mk]
  mono_index := by simp [irel]
  refines := by simp [rel, irel]
  discrete := by simp [irel, rel]

instance : COFE emptyO where
  lim c := by cases c 0
  completeness c := by simp [irel, IRel.ir]

end Empty



section Product

/-! ### Product OFE -/

abbrev prodO (A B : Type) : Type := A × B

-- instance [OFE A] [OFE B] : Coe (A × B) (prodO A B) where
--   coe := sorry

instance [OFE A] [OFE B] : OFE (prodO A B) where
  ir n x y := (x.1 ≈[n] y.1) ∧ (x.2 ≈[n] y.2)
  r x y := (x.1 ≈ y.1) ∧ (x.2 ≈ y.2)
  iseqv := by
    apply Equivalence.mk
    · intro
      apply And.intro
      · apply refl
      · apply refl
    · simp
      intros
      apply And.intro
      · apply symm
        trivial
      · apply symm
        trivial
    · simp
      intros
      apply And.intro
      · apply _root_.trans
        · trivial
        · trivial
      · apply _root_.trans
        · trivial
        · trivial
  isieqv := by
    apply IEquivalence.mk <;> intro n
    · intro
      apply And.intro
      · apply refl
      · apply refl
    · simp
      intros
      apply And.intro
      · apply symm
        trivial
      · apply symm
        trivial
    · simp
      intros
      apply And.intro
      · apply _root_.trans
        · trivial
        · trivial
      · apply _root_.trans
        · trivial
        · trivial
  mono_index := by
    simp
    simp [irel]
    intros
    apply And.intro
    · apply irel_mono
      · trivial
      · trivial
    · apply irel_mono
      · trivial
      · trivial
  refines := by
    simp
    intros
    apply Iff.intro
    · intros
      rename_i H
      apply And.intro
      · apply rel_of_forall_irel
        intro n
        apply (H n).1
      · apply rel_of_forall_irel
        intro n
        apply (H n).2
    · intros H _
      cases H
      apply And.intro
      · apply forall_irel_of_rel
        trivial
      · apply forall_irel_of_rel
        trivial

lemma fst_nonexpansive [OFE A] [OFE B] : @nonexpansive (prodO A B) _ _ _ Prod.fst := by
  simp [nonexpansive, irel, IRel.ir]
  intros
  trivial

lemma snd_nonexpansive [OFE A] [OFE B] : @nonexpansive (prodO A B) _ _ _ Prod.snd := by
  simp [nonexpansive, irel, IRel.ir]


instance [OFE A] [OFE B] : @HasNonExpansive (prodO A B) A _ _ _ _ Prod.fst where
  is_nonexpansive := fst_nonexpansive

instance [OFE A] [OFE B] : @HasNonExpansive (prodO A B) B _ _ _ _ Prod.snd where
  is_nonexpansive := snd_nonexpansive

instance [COFE A] [COFE B] : COFE (prodO A B) where
  lim c :=
    (COFE.lim (Chain.map c fst_nonexpansive), COFE.lim (Chain.map c snd_nonexpansive))
  completeness := by
    simp
    intros
    apply And.intro
    · apply COFE.completeness
    · apply COFE.completeness

instance [DiscreteOFE A] [DiscreteOFE B] : DiscreteOFE (prodO A B) where
  discrete := by
    simp [irel, IRel.ir]
    intros
    apply And.intro
    · apply DiscreteOFE.discrete
      trivial
    · apply DiscreteOFE.discrete
      trivial

def Product.functor_prod {A B C : Type} [OFE A] [OFE B] [OFE C]
    (f : (A -n> B)) (g : (A -n> C)) : (A -n> (prodO B C)) where
  toFun a := (f a, g a)
  is_nonexpansive := by
    simp [nonexpansive]
    intros
    apply And.intro <;>
    apply HasNonExpansive.is_nonexpansive <;>
    trivial

-- TODO: Derive from more general case
def Product.functor_prod' {A B C : Type} [OFE A] [OFE B] [OFE C]
    (fg : (prodO (A -n> B) (A -n> C))) : (A -n> (prodO B C)) :=
  NonExpansive.mk (fun a => (fg.1 a, fg.2 a)) <| by
    simp [nonexpansive]
    intros
    apply And.intro <;>
    apply HasNonExpansive.is_nonexpansive <;>
    trivial

lemma Product.functor_prod'_nonexpansive [OFE A] [OFE B] [OFE C] :
    nonexpansive (@Product.functor_prod' A B C _ _ _) := by
  simp [nonexpansive, functor_prod']
  intros
  rename_i H
  simp [irel, IRel.ir] at H
  rcases H with ⟨ H1, H2 ⟩
  intro a
  simp [DFunLike.coe]
  apply And.intro <;> simp
  · apply H1
  · apply H2


-- def Product.prod' {A B C : Type*} [OFE A] [OFE B] [OFE C] : (prodO (A -n> B) (A -n> C)) -n> (A -n> (prodO B C)) where


-- #synth OFE (emptyO × emptyO)
-- #check (((_ : emptyO), (_ : emptyO)) : prodO _ _)

-- abbrev prodC [OFE A] [OFE B] (a : A) (b : B) : prodO A B := (a, b)
--
-- lemma prod_irel_iff [OFE A] [OFE B] (a a' : A) (b b' : B) (n : ℕ) :
--     (prodC a b ≈[n] prodC a' b') <-> (a ≈[n] a') ∧  (b ≈[n] b') := by
--   sorry

end Product


section oFunctor

/-! ### oFunctors
NOTE: See https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/resource_algebras.md
-/

/-- The data of an oFunctor -/
structure oFunctorStruct where
  /-- An assignment of pairs of COFE to types. -/
  obj (A B : Type) [COFE A] [COFE B] : Type
  /-- An assignment of morphism pairs to a function between the appropriate objects -/
  map [COFE A] [COFE A'] [COFE B] [COFE B'] (f : prodO (A' -n> A)  (B -n> B')) : obj A B -> obj A' B'

abbrev oFunctorStruct.ap (F : oFunctorStruct) (A : Type) [COFE A] : Type := F.obj A A

/-- An oFunctorStruct with objects that are OFE's -/
class oFunctorPre (F : oFunctorStruct) where
  obj_ofe [COFE A] [COFE B] : OFE <| F.obj A B

attribute [instance] oFunctorPre.obj_ofe

class cFunctorPre (F : oFunctorStruct) [oFunctorPre F] where
  obj_cofe [COFE A] [COFE B] : COFEMixin (F.obj A B)

class dcFunctorPre (F : oFunctorStruct) [oFunctorPre F] where
  obj_diag_cofe [COFE A] : COFEMixin (F.ap A)

instance (F : oFunctorStruct) [oFunctorPre F] [cFunctorPre F] : dcFunctorPre F where
  obj_diag_cofe := cFunctorPre.obj_cofe

instance (F : oFunctorStruct) [oFunctorPre F] [cFunctorPre F] [COFE A] [COFE B] : COFE (F.obj A B) :=
  cFunctorPre.obj_cofe.toCOFE

-- The inheritance diamond is now definitional
-- NOTE: this breaks when we change cFunctorPre to use extends instead of tc constraint
example [COFE A] [COFE B] (F : oFunctorStruct) [oFunctorPre F] [cFunctorPre F] :
    oFunctorPre.obj_ofe = ((instCOFEObjOfCFunctorPre F).toOFE : OFE (F.obj A B)) := by
  rfl

-- The functor is lawful
class oFunctorPreLawful (F : oFunctorStruct) extends oFunctorPre F where
  /-- The map sends all morphisms to nonexpansive morphisms -/
  map_pointwise_ne [COFE A] [COFE A'] [COFE B] [COFE B'] (f : prodO (A' -n> A) (B -n> B')) :
    HasNonExpansive (F.map f)
  /-- Identity law -/
  map_id [COFE A] [COFE B] (x : F.obj A B) :
    F.map ((NonExpansive.cid A), (NonExpansive.cid B)) x ≈ x
  /-- Composition law -/
  map_cmp [COFE A] [COFE A'] [COFE A''] [COFE B] [COFE B'] [COFE B'']
      (f : A' -n> A) (g : A'' -n> A') (f' : B -n> B') (g' : B' -n> B'') (x : F.obj A B):
    F.map ((f ⊙ g), (g' ⊙ f')) x ≈ (F.map (g, g') <| F.map (f, f') x)

attribute [instance] oFunctorPreLawful.map_pointwise_ne

@[reducible]
def oFunctorStruct.nemap (F : oFunctorStruct) {A A' B B' : Type}
      [oFunctorPreLawful F] [COFE A] [COFE A'] [COFE B] [COFE B']
      (f : prodO (A' -n> A) (B -n> B')) :
    -- @NonExpansive (F.obj A B) (F.obj A' B') oFunctorPre.obj_ofe oFunctorPre.obj_ofe :=
      (F.obj A B) -n> (F.obj A' B') :=
  NonExpansive.lift (F.map f)

class oFunctor (F : oFunctorStruct) extends oFunctorPreLawful F where
  map_ne [COFE A] [COFE A'] [COFE B] [COFE B'] :
    HasNonExpansive (@F.nemap A A' B B' _ _ _ _ _)

class oFunctorContractive (F : oFunctorStruct) extends oFunctor F where
  map_ct [COFE A] [COFE A'] [COFE B] [COFE B'] :
    HasContractive (@F.nemap A A' B B' _ _ _ _ _)

-- Is the contractive diamond definitional?
-- Not sure. But hopefully it shouldn't be so bad becase contractive and nonexpansive are both prop-typed.

-- lemma transp [COFE A] [COFE B] (F : oFunctorStruct) [oFunctorPre F] [cFunctorPre F] :
--     oFunctorPre.obj_ofe = ((instCOFEObjOfCFunctorPre F).toOFE : OFE (F.obj A B)) := by
--   rfl
--
-- lemma transp2 {A A' B B' : Type} [COFE A] [COFE A'] [COFE B] [COFE B'] (F2 : oFunctorStruct) [oFunctorPre F2] [cFunctorPre F2] [oFunctorPreLawful F2] :
--     @NonExpansive (F2.obj B' A') (F2.obj B A) oFunctorPre.obj_ofe oFunctorPre.obj_ofe =  @NonExpansive (F2.obj B' A') (F2.obj B A) COFE.toOFE COFE.toOFE := by
--   rfl

def oFunctorStruct.comp (F1 F2 : oFunctorStruct) [oFunctorPre F1] [oFunctorPreLawful F2] [cFunctorPre F2]:
    oFunctorStruct where
  obj A B := F1.obj (F2.obj B A) (F2.obj A B)
  map fg := F1.map (NonExpansive.lift <| F2.map (fg.2, fg.1), NonExpansive.lift <| F2.map (fg.1, fg.2))


end oFunctor



section Leibniz

/-! ### Leibniz OFE -/

/-- A type alias for T with eqivalence relation given by equality -/
@[simp]
def WithEquality (T : Type) : Type := T

instance : Rel (WithEquality T) where
  r := Eq
  iseqv := by simp [Equivalence.mk]

abbrev LeibnizO T := Δ (WithEquality T)

lemma LeibnizO_irel_leibniz : relation_leibniz (rel : Relation (LeibnizO T)) := by
  intros x y
  cases x
  cases y
  simp [rel, Setoid.r]

-- #synth ERel (LeibnizO Bool)
-- #synth OFE (LeibnizO Bool)


/-- Booleans with Leibniz equivalence -/
def boolO := LeibnizO Bool

/-- Naturals with Leibniz equivalence -/
def natO  := LeibnizO ℕ

/-- Integers with Leibniz equivalence -/
def intO  := LeibnizO ℤ

/-- Propositions with Leibniz equivalence
NOTE: Because we're using propext anyways, can use equuality here. -/
def propO  := LeibnizO Prop

end Leibniz



section Later

/-! ### Later OFE -/


structure laterO (T : Type) : Type where
  Next ::
  t : T

prefix:max  "▸"  => laterO

-- FIXME: Clean up this instance, there's related proofs above (just tricky TC management)
instance [OFE T] : OFE ▸T where
  ir n x y := later irel n x.t y.t
  r x y := rel x.t y.t
  iseqv := by
    apply Equivalence.mk
    · intro
      apply refl
    · intros
      apply symm
      trivial
    · intros
      apply _root_.trans
      · trivial
      · trivial
  isieqv := by
    apply IEquivalence.mk
    intro n
    · simp [later]
      intros
      apply refl
    · simp [later]
      intros _ _ _ H _ _
      apply symm
      apply H
      trivial
    · simp [later]
      intros _ _ _ _ H1 H2 _ _
      apply _root_.trans
      · apply H1
        trivial
      · apply H2
        trivial
  mono_index := by
    intros _ _ _ _ _ H _ _
    apply irel_mono _ ?G
    case G =>
      apply H
      trivial
    trivial
  refines := by
    intro x y
    apply Iff.intro
    · intro H
      apply rel_of_forall_irel
      intro _
      apply rel_of_later_rel_S
      apply H
    · intro _ _ _ _
      apply forall_irel_of_rel
      trivial


/-- Lift a later through a chain -/
def Chain.later [OFE α] (c : Chain ▸α) : Chain α where
  car n := laterO.t <| c <| Nat.succ n
  is_cauchy := by
    simp [DFunLike.coe]
    intros
    apply c.is_cauchy
    · simp
      trivial
    · apply Nat.lt_add_one

instance [COFE α] : COFE (▸α) where
  lim := laterO.Next ∘ COFE.lim ∘ Chain.later
  completeness := by
    intros n c
    cases n
    · apply later_rel_0
    rename_i n
    -- FIXME: Setoid
    simp only [irel, Function.comp_apply]
    apply later_rel_S_of_rel
    apply symm
    simp
    apply symm
    apply _root_.trans
    · apply COFE.completeness
    apply refl


lemma Next_contractive [OFE T] : contractive (@laterO.Next T) := by
  simp [contractive, irel, IRel.ir]

lemma later_car_anti_contractive [OFE T] : anticontractive (@laterO.t T) := by
  simp [anticontractive, irel, IRel.ir]

/-- Characterization for contractice functions in terms of laters -/
lemma contractive_iff [OFE A] [OFE B] (f : A -> B) :
    contractive f <-> ∃ g : ▸A -> B, nonexpansive g ∧ ∀ x, (f x ≈ g (laterO.Next x)) := by
  apply Iff.intro
  · intros H
    exists (f ∘ laterO.t)
    simp [nonexpansive]
    apply And.intro
    · intros
      apply H
      trivial
    · intros
      apply Setoid.refl -- FIXME: Why can't it synthesize refl here?
  · intros H
    rcases H with ⟨ g, ⟨ HNE, H ⟩ ⟩
    simp [contractive, Contractive.is_contractive]
    intros n x y HL
    -- FIXME: Setoid
    apply _root_.trans
    · apply forall_irel_of_rel
      apply H
    apply symm
    apply _root_.trans
    · apply forall_irel_of_rel
      apply H
    apply symm
    apply HNE
    apply HL


/--
The implementation of laterO.map, which isn't nonexpansive, but doesn't require a nonexpansive input
Not sure how often we map by a non-nonexpansive map, but it might be useful?
-/
@[simp]
def laterO.map (f : A -> B) (x : ▸A) : ▸B := Next <| f x.t


lemma later_map_nonexpansive [OFE A] [OFE B] (f : A -> B) (HN : ∀ n, is_proper1 (later irel n) (later irel n) f) :
    nonexpansive (laterO.map f) := by
  simp [nonexpansive]
  intros
  apply HN
  trivial

lemma later_map_nonexpansive' [OFE A] [OFE B] (f : A -n> B) : nonexpansive (laterO.map f) := by
  simp [nonexpansive, later]
  intros _ _ _ H _ _
  apply NonExpansive.is_nonexpansive
  apply H
  trivial


lemma later_rel_rel_proper [OFE A] [OFE B] (f : A -> B) (HN : is_proper1 rel rel f) :
    is_proper1 rel rel (laterO.map f) := by
  simp [nonexpansive]
  intros
  apply HN
  trivial

lemma later_map_next [OFE A] [OFE B] (f : A -> B) (x : A) :
    laterO.map f (laterO.Next x) = laterO.Next (f x) := by
  simp only [laterO.map]

lemma later_map_id [OFE A] [OFE B] (x : ▸A) :
    laterO.map id x = x := by
  simp only [laterO.map, id_eq]

lemma later_map_cmp [OFE A] [OFE B] [OFE C] (f : A -> B) (g : B -> C) (x : ▸ A):
    laterO.map (g ∘ f) x = laterO.map g (laterO.map f x) := by
  simp only [laterO.map, Function.comp_apply]

lemma later_map_ext [OFE A] [OFE B] (f : A -> B) :
    (∀ x, f x ≈ g x) -> laterO.map f x ≈ laterO.map g x := by
  intro H
  simp only [rel, laterO.map]
  apply H

instance [OFE A] [OFE B] [FunLike F A B] (f : F) [HasNonExpansive f] : HasNonExpansive (laterO.map f) where
  is_nonexpansive := by
    simp [DFunLike.coe]
    intros _ _ _ H _ _
    apply HasNonExpansive.is_nonexpansive
    apply H
    trivial

-- section Test1
-- variable [OFE A] [OFE B]
-- variable (f : A -n> B)
-- -- #synth HasNonExpansive (laterO.map f)
-- -- #check @NonExpansive.lift (▸A) (▸B) (▸A -> ▸B) _ _ _ (laterO.map f) _
--
--
-- -- TODO: Is there some way to automatically insert this lift?
-- #check NonExpansive.lift (laterO.map f)
-- end Test1

lemma later_map_contractive [OFE A] [OFE B] :
    contractive (fun f : A -n> B => (NonExpansive.lift (laterO.map f))) := by
 simp [contractive, later, laterO.map, DFunLike.coe]
 intros _ f f' H _ _ _
 apply _root_.trans
 · apply H
   trivial
 apply refl

end Later


section Iso

structure OFEIso [OFE A] [OFE B] where
  f : A -n> B
  g : B -n> A
  f_g_id x : f (g x) ≈ x
  g_f_id x : g (f x) ≈ x

end Iso



section COFESolver

/- ### oFunctor fixpoints
NOTE: This secion is more or less a straight port of ``cofe_solver.v``. I'm making
no effort to make the names in this section make more sense or anything because I don't
really understand the original paper.
see https://gitlab.mpi-sws.org/iris/iris/blob/master/iris/algebra/cofe_solver.v
-/

/-
structure oFix (F : oFunctorStruct) where
  t : Type
  t_COFE : COFE T
  -- t_iso : OFEIso t t
attribute [instance] oFix.t_COFE
-/

namespace COFESolver
variable (F : oFunctorStruct)
variable [Inhabited (F.ap unitO)]
variable [oFunctorContractive F]
variable [dcFunctorPre F]

abbrev A' : ℕ -> (T : Type) × (COFE T)
| 0 =>
  ⟨ unitO, unitO_COFE ⟩
| Nat.succ n' =>
  let ⟨ R,  _ ⟩ := A' n'
  ⟨ F.ap R, dcFunctorPre.obj_diag_cofe.toCOFE ⟩
  -- let Z : COFEMixin (F.ap R) := dcFunctorPre.obj_diag_cofe
  -- Z.toCOFE

abbrev A (n : ℕ) : Type := Sigma.fst <| A' F n

@[reducible]
instance ACOFE (n : ℕ) : COFE (A F n) := Sigma.snd <| A' F n

-- #check (ACOFE F 10 : COFE (A F 10))
mutual

def f (k : ℕ) : (A F k) -n> (A F (k + 1)) :=
  match k with
  | 0 => NonExpansive.cconst default
  | Nat.succ k =>
    -- FIX instances. Why can it synthesize COFE up top, but not here?
    let L := @F.map (A F k) (A F k.succ) (A F k) (A F k.succ) (ACOFE F _) (ACOFE F _) (ACOFE F _) (ACOFE F _) (g k, f k)
    NonExpansive.lift <| L

def g (k : ℕ) : (A F (k + 1)) -n> (A F k) :=
  match k with
  | 0 => NonExpansive.cconst ()
  | Nat.succ k =>
    let L := @F.map _ _ _ _ (ACOFE _ _) (ACOFE _ _) (ACOFE _ _) (ACOFE _ _) (f k, g k)
    NonExpansive.lift <| L
end

-- FIXME: Synth of ACOFE
def f_S (k : ℕ) (x : A F (k + 1)) : f F (k + 1) x = @F.map _ _ _ _ (ACOFE _ _) (ACOFE _ _) (ACOFE _ _) (ACOFE _ _) (g F k, f F k) x := by rfl

def g_S (k : ℕ) (x : A F (k + 1 + 1)) : g F (k + 1) x = @F.map _ _ _ _ (ACOFE _ _) (ACOFE _ _) (ACOFE _ _) (ACOFE _ _) (f F k, g F k) x := by rfl

lemma gf (k : ℕ) (x : A F k) : g F k (f F k x) ≈ x := by
  sorry

lemma fg (k : ℕ) (x : A F (k + 1 + 1)) : f F (k + 1) (g F (k + 1) x) ≈[k] x := by
  sorry


structure Tower where
  car (k : ℕ) : A F k
  g_tower (k : ℕ) : g F k (car (k + 1)) ≈ car k

export Tower (g_tower)

instance : OFE (Tower F) where
  r TX TY := ∀ k, TX.car k ≈ TY.car k
  ir n TX TY := ∀ k, TX.car k ≈[n] TY.car k
  iseqv := sorry
  isieqv := sorry
  mono_index := sorry
  refines := sorry

def tower_chain (c : Chain (Tower F)) (k : ℕ) : Chain (A F k) where
  car i := (c i).car k
  is_cauchy := sorry

/-
instance : COFE (Tower F) where
  lim c :=
    Tower.mk (fun i => COFE.lim <| tower_chain F c i)
    sorry
  completeness :=
    sorry
-/

def TowerCOFEMixin : COFEMixin (Tower F) where
  lim c := Tower.mk (fun i => COFE.lim <| tower_chain F c i) sorry
  completeness := sorry

instance : COFE (Tower F) := COFEMixin.toCOFE _ (TowerCOFEMixin F)

mutual

def ff {k : ℕ} (i : ℕ) : (A F k) -n> (A F (k + i)) :=
  match i with
  | 0 => NonExpansive.cid _
  | Nat.succ i => (f F (k + i)) ⊙ (ff i)

def gg {k : ℕ} (i : ℕ) : (A F (k + i)) -n> (A F k) :=
  match i with
  | 0 => NonExpansive.cid _
  | Nat.succ i => (gg i) ⊙ (g F (k + i))

end

lemma ggff {k i : ℕ} (x : A F k) : gg F i (ff F i x) ≈ x := sorry

lemma f_tower (k : ℕ) (X : Tower F) : f F (k + 1) (X.car (k + 1)) ≈[k] X.car (k + 1 + 1) := sorry

lemma ff_tower (k i : ℕ) (X : Tower F) : ff F i (X.car (k + 1)) ≈[k] X.car (k + 1 + i) := sorry

lemma gg_tower (k i : ℕ) (X : Tower F) : gg F i (X.car (k + i)) ≈ X.car k := sorry

lemma Tower.car_ne (k : ℕ) : nonexpansive (fun T : Tower F => T.car k) := sorry

def Tower.project (k : ℕ) : Tower F -n> A F k := NonExpansive.mk _ (Tower.car_ne F k)

def coerce {i j : ℕ} (H : i = j) : A F i -n> A F j := by
  -- Make into a proof term
  rw [H]
  apply NonExpansive.cid (A F j)

-- Which coerce lemmas do I need?

lemma gg_gg {k i i1 i2 j : ℕ} (H1 : k = j + i) (H2 : k = j + i1 + i2) (x : A F k) :
    gg F i (coerce F H1 x) = gg F i1 (gg F i2 (coerce F H2 x)) := by sorry

lemma ff_ff {k i i1 i2 j : ℕ} (H1 : k + i = j) (H2 : k + i2 + i1 = j) (x : A F k) :
    coerce F H1 (ff F i x) = coerce F H2 (ff F i1 (ff F i2 x)) := by sorry

def embed_coerce {k : ℕ} (i : ℕ) : A F k -n> A F i :=
  match (Nat.decLt k i) with
  | isTrue H =>
    let R : k + (i - k) = i := Nat.add_sub_of_le <| Nat.le_of_succ_le H
    coerce F R ⊙ ff F (i - k)
  | isFalse H =>
    let R : k = i + (k - i) := by simp_all only [Nat.not_lt, Nat.add_sub_cancel']
    gg F (k - i) ⊙ coerce F R

lemma g_embed_coerce {k i : ℕ} (x : A F k) : (g F i <| embed_coerce F (i + 1) x) ≈ embed_coerce F i x := by
  sorry

def embed (k : ℕ) (x : A F k) : Tower F where
  car n := embed_coerce F n x
  g_tower := sorry

lemma embed_ne (n : ℕ) : nonexpansive (embed F n) := by sorry

def Tower.embed (k : ℕ) : (A F k) -n> Tower F := NonExpansive.mk _ (embed_ne _ _)

lemma embed_f (k : ℕ) (x : A F k) : embed F (k + 1) (f F k x) ≈ embed F k x := by sorry

lemma embed_tower (k : ℕ) (X : Tower F) : embed F (k + 1) (X.car (k + 1)) ≈[k] X := sorry

def unfold_chain (X : Tower F) : Chain (F.ap (Tower F)) where
  car n := F.map (Tower.project F n, Tower.embed F n) (X.car (n + 1))
  is_cauchy := sorry

def unfold (X : Tower F) : F.ap (Tower F) :=
  COFEMixin.lim dcFunctorPre.obj_diag_cofe (unfold_chain F X)

lemma unfold_ne : nonexpansive (unfold F) := by sorry

def fold (X : F.ap (Tower F)) : Tower F where
  car n := g F n <| F.map (Tower.embed F n, Tower.project F n) X
  g_tower := sorry

lemma fold_ne : nonexpansive (fold F) := by sorry

end COFESolver
end COFESolver
