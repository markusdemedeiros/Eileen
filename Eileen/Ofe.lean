/-
Authors: Markus de Medeiros
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types
import Eileen.Proper

/-!
This file defines ordered families of equivalences (OFE's).

## Main definitions

## Main statements

## Implementation Notes
- Because we have bundled OFE's, it's easier to defined nonexpansive functions as between
  OFE's instead of IRels, even though the latter is more general.

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

/-- An indexed relation is discrete -/
@[simp]
def irelation_discrete {T : Sort*} (R : IRelation T) (R' : Relation T) : Prop :=
  ∀ {x y : T}, R 0 x y -> R' x y

/-- An indexed relation is leibniz -/
@[simp]
def relation_leibniz {T : Sort*} (R : Relation T) : Prop :=
  ∀ {x y : T}, (R x y) -> x = y




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
  intros; apply irel_le_mono <;> trivial

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


-- FIXME: These next 6 defintions should be removable, and probably will have to be
-- once generalized rewiting lands. For some reason, the mathlib setoid typeclasses
-- aren't being inferred properly.

/-
section OFESetoid

variable (T : Sort*)
variable [OFE T]

def OFE.refl (x : T): x ≈ x := by
  apply Setoid.refl

def OFE.symm {x y : T} : x ≈ y -> y ≈ x := by
  apply Setoid.symm

def OFE.trans {x y z : T} : x ≈ y -> y ≈ z -> x ≈ z := by
  apply Setoid.trans

def OFE.irefl (x : T) (i : ℕ) : x ≈[i] x := by
  apply IRel.isieqv.irefl

def OFE.isymm {x y : T} {i : ℕ} : x ≈[i] y -> y ≈[i] x := by
  apply IRel.isieqv.isymm

def OFE.itrans {x y z : T} {i : ℕ} : x ≈[i] y -> y ≈[i] z -> x ≈[i] z := by
  apply IRel.isieqv.itrans

end OFESetoid
-/



/-

/-- Notation to help infer an irel from an OFE instance -/
@[simp]
def OFE.irel (I : Type*) (T : Sort*) [Ix I] [Rel T] [OFE I T] : IRelation I T :=
  _root_.irel


/-- Notation to help infer a rel from an OFE instance -/
@[simp]
def OFE.rel (I : Type*) (T : Sort*) [Ix I] [Rel T] [OFE I T] : Relation T :=
  _root_.rel


-- variable (I : Type*) (T : Type*)
-- variable [Ix I] [Rel T] [OFE I T]
-- variable (t1 t2 : T)
-- variable (i i': I)
-- -- -- #check (t1 ≈ t2)
-- -- -- #check (t1 ≈[i] t2)
-- -- -- #check (t1 ≈l[i] t2)
-- -- -- #check (i < i')
-- -- -- #check @irel_mono I T _ _ _
-- -- -- #check @refl T
-- -- -- #synth (IRel I T)
-- -- -- #check (irel : IRelation I T)
-- -- #check trans (_ : t1 ≈ t2)
-- -- example (_ : t1 ≈[i] t2) : t2 ≈[i] t1 := by
-- --   apply symm
-- --   trivial
--   -- No need for isymm, can just use symm
--
-- -- NOTE: dist_le should be replaced with irel_mono
-/



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

def nonexpansive_equiv_equiv_proper {f : T1 -> T2} (H : nonexpansive f) :
    is_proper1 rel rel f := by
  intro _ _ H'
  apply rel_of_forall_irel
  intro _
  apply H
  apply forall_irel_of_rel
  apply H'


/-
/--
A nonexpansive map is proper wrt. equality when the index relations refine the equality
-/
lemma is_nonexpansive_refinement_proper (RM : irelation M) (RN : irelation N) (EM : relation M) (EN : relation N)
    (f : M -> N) (HIM : is_indexed_refinement RM EM) (HIN : is_indexed_refinement RN EN)
    (HN : is_nonexpansive RM RN f) :
    proper1 EM EN f := by
  simp
  intro x y H
  apply HIN.mp
  apply HIM.mpr at H
  intro _
  apply HN
  apply H

-/



-- example (f : T1 -> T2) (i : I) (HN : nonexpansive I f) (t1 t2 : T1) (H : t1 ≈[i] t2) : f t1 ≈[i] f t2 := by
--   apply OFE.itrans
--   · apply HN
--     apply H
--   apply OFE.irefl
--
-- example (f : T1 -> T2) (HN : nonexpansive I f) (t1 t2 : T1) (H : t1 ≈ t2) : f t1 ≈ f t2 := by
--   apply OFE.trans
--   · apply (equiv_equiv_proper I HN)
--     apply H
--   apply OFE.refl


end OFE




section OFELater

/-! ### Properties of the later construction in OFE's -/

variable  {T : Sort*}
variable [OFE T]

instance : @IEquivalence T (later irel) where
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



section OFEBundled

/-!
### Bundled Hierarchy of OFE's, and the category of OFE's/COFE's

See Order/Lattice.lean
See Order/Hom/Lattice.lean
See Order/Category/Lat.lean

NOTE: How to define a Mathlib-style bundled hierarchy:

Step 1: TC Hierarchy of classes
  See Order/lattice.lean
  Semi-bundled, hierarchy defined using extension (see Mathematics in Lean)
  For multiple instances: see Mathlib.Order.Synonym

Step 2: Semi-bundled TC hierarchy of morphisms
  See Order/Hom/Lattice.lean
  2.1. Define structure (hierarchy) with toFun
  2.2. Define class (hierarchy) which extends FunLike
  2.3. Register class instances for each structure
  2.4. Register CoeTC from F (of class) to structure
  2.5. Register instance of FunLike for the class
  2.5. Define comp and id structures

Step 3: Bundled structure
  See Order/Category/Lat.lean
  3.1. Define bundled type with CategoryTheory.Bundled
  3.2. Register CoeSort for the bundled type
  3.3. Register typeclass instance for the bundled type
  3.4. Define coercion from type to bundled type

Step 4: Bundled morphisms
  See Order/Category/Lat.lean
  4.1. Register BundledHom instance for @structure
  4.2. Register Category instance
  4.3. Register ConcreteCategory instance
-/

/-- [semi-bundled] [2.1] A nonexpansive function between two OFE's -/
structure NonExpansive (M N : Type) [OFE M] [OFE N] where
  toFun : M -> N
  is_nonexpansive : nonexpansive toFun

attribute [simp] NonExpansive.toFun

notation:50 a1 " -n> "  a2 => NonExpansive a1 a2

/-- [semi-bundled] [2.2] A type F behaves like an nonexpansive function from M to N at each index  -/
class NonExpansiveClass (F : Type) (M N : outParam Type) [OFE M] [OFE N] extends
     FunLike F M N where
  is_nonexpansive : ∀ f : F, nonexpansive f

-- [2.3] The structure behaves like a function
instance (M N : Type) [OFE M] [OFE N] : FunLike (NonExpansive M N) M N where
  coe := fun F x => F.toFun x
  coe_injective' := by
    intro x y H
    cases x
    congr

-- [2.3] The structure behaves like a nonexpansive function
instance (M N : Type) [OFE M] [OFE N] : NonExpansiveClass (NonExpansive M N) M N where
  is_nonexpansive := by
    simp [DFunLike.coe]
    intro f _ _ _ _
    apply f.is_nonexpansive
    trivial

-- [2.?] Regular functions can be lifted to nonexpansive functions, provided they are nonexpansive
instance [OFE M] [OFE N] : CanLift (M -> N) (M -n> N) DFunLike.coe nonexpansive where
  prf := by
    simp [DFunLike.coe]
    intros f H
    exists NonExpansive.mk f H

-- [2.?] Coercion between a term that behaves like a nonexpansive function, and the structure
instance [OFE M] [OFE N] [NonExpansiveClass F M N] : CoeOut F (NonExpansive M N) where
  coe F := NonExpansive.mk F (NonExpansiveClass.is_nonexpansive F)

/-- The term f has a proof of its nonexpansivity -/
class HasNonExpansive [OFE M] [OFE N] [FunLike F M N] (f : F) where
  is_nonexpansive : nonexpansive f

/-- All terms of a nonexpansive type have a proof of their nonexpansivity -/
instance [OFE M] [OFE N] [NonExpansiveClass F M N] (f : F) : HasNonExpansive f where
  is_nonexpansive := by apply NonExpansiveClass.is_nonexpansive

/-- An instance of the struct for a function which has a nonexpansive proof -/
def NonExpansive.lift [OFE M] [OFE N] [FunLike F M N] (f : F) [HasNonExpansive f] : NonExpansive M N where
  toFun := f
  is_nonexpansive := HasNonExpansive.is_nonexpansive

/-- The (bundled) identity morphism in the category of OFE+NonExpansive functions -/
def NonExpansive.cid [OFE M] : M -n> M where
  toFun := @_root_.id _
  is_nonexpansive := id_nonexpansive

/-- The (bundled) constant nonexpansive function -/
def NonExpansive.cconst [OFE α] [OFE β] (x : β) : α -n> β where
  toFun _ := x
  is_nonexpansive := by
    simp [nonexpansive]
    intros
    apply refl

/-- The (bundled) composition of morphisms in the category of OFE+NonExpansive functions -/
def NonExpansive.ccompose [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  toFun := g ∘ f
  is_nonexpansive := by
    simp only [DFunLike.coe]
    apply cmp_nonexpansive
    · apply is_nonexpansive
    · apply is_nonexpansive


/-- A "map" of nonexpansive functions.
NOTE: The real construction is based on Hom functors?
-/
def NonExpansive.map [OFE A] [OFE B] [OFE A'] [OFE B']
    (f : A' -n> A) (g : B -n> B') (x : A -n> B) : (A' -n> B') :=
  ccompose g (ccompose x f)


/-- [bundled] [3.1] Objects in the category of OFE's -/
def OFECat := CategoryTheory.Bundled OFE

-- [3.2] Coercion between objects in the category of OFE's and Type (their type)
instance : CoeSort OFECat Type where
  coe := CategoryTheory.Bundled.α

-- [3.3] The carrier type of every object in the category of OFE's is an OFE
instance (X : OFECat) : OFE X := X.str

/-- [3.4] An object in the category of OFE's, for any type that is an OFE -/
def OFE.of (T : Type) [OFE T] : OFECat :=
  CategoryTheory.Bundled.of T


-- [4.1]: Bundled OFE's and nonexpansive functions form a category
instance : CategoryTheory.BundledHom @NonExpansive where
  toFun _ _ F := F
  id _ := NonExpansive.cid
  comp := @NonExpansive.ccompose
  comp_toFun _ _ _ f g := by
    simp only [DFunLike.coe]
    rfl

/-- The category of OFE's and nonexpansive functions -/
instance : CategoryTheory.LargeCategory @OFECat :=
  CategoryTheory.BundledHom.category @NonExpansive

/-- The category of OFE's and nonexpansive functions -/
instance : CategoryTheory.ConcreteCategory OFECat :=
  CategoryTheory.BundledHom.concreteCategory NonExpansive






/-- A contractive function between two OFE's -/
structure Contractive (M N : Type) [OFE M] [OFE N]  where
  toFun : M -> N
  is_contractive : contractive toFun

attribute [simp] Contractive.toFun

notation:50 a1 " -c> "  a2 => Contractive a1 a2


/-- The type F behaves like a contractive function -/
class ContractiveClass (F : Type) (M N : outParam Type) [OFE M] [OFE N] extends
    FunLike F M N where
  is_contractive : ∀ f : F, contractive f

/-- Every term which behaves like a contractive function also behaves like
  a nonexpansive function -/
instance [OFE M] [OFE N] [ContractiveClass F M N] : NonExpansiveClass F M N where
  is_nonexpansive f := by
    apply nonexpansive_of_contractive
    apply ContractiveClass.is_contractive

/-- The Contractive struct behaves like a function -/
instance [OFE M] [OFE N] : FunLike (Contractive M N) M N where
  coe F x := F.toFun x
  coe_injective' := by
    intro x _ _
    cases x
    congr

/-- The Contractive struct behaves like a contractive function -/
instance [OFE M] [OFE N] : ContractiveClass (Contractive M N) M N where
  is_contractive f := by
    simp only [DFunLike.coe]
    apply Contractive.is_contractive


/-- Coercion between Anything which behaves like a contractive function and the contractive struct -/
instance [OFE M] [OFE N] [ContractiveClass F M N] : CoeOut F (Contractive M N) where
  coe F := Contractive.mk F (ContractiveClass.is_contractive F)

/-- The term f behaves has a proof of contractivity -/
class HasContractive [OFE M] [OFE N] [FunLike F M N] (f : F) where
  is_contractive : contractive f

/-- Any term is a type of contractive functions has a proof of contractivity -/
instance [OFE M] [OFE N] [ContractiveClass F M N] (f : F) : HasContractive f where
  is_contractive := by apply ContractiveClass.is_contractive

/-- Coercion between any term which has a proof of contractivity and the Contractive struct -/
instance [OFE M] [OFE N] [FunLike F M N] (f : F) : CoeOut (HasContractive f) (Contractive M N) where
  coe _ := Contractive.mk f HasContractive.is_contractive

/-- Obtain a Contractive struct for any term which has a proof of contractivity -/
def Contractive.lift [OFE M] [OFE N] [FunLike F M N] (f : F) [HasContractive f] : Contractive M N where
  toFun := f
  is_contractive := HasContractive.is_contractive

end OFEBundled




/-


/-
## Discrete OFE
-/


/-- [unbundled] An element in an indexed relation is discrete -/
@[simp]
def is_discrete [OFE T] (e : T) : Prop := ∀ y, (e ≈[0] y) -> e ≈ y

/-- [semi-bundled] A discrete OFE is an OFE where all elements are discrete -/
class DiscreteOFE (T : Type) extends OFE T where
  discrete : ∀ (x : T), is_discrete x

/--
discreteO is the default discrete OFE, which compares by equality
-/
structure discreteO (T : Type) : Type where
  t : T

prefix:max  "Δ"  => discreteO

instance [ERel T] : OFE (Δ T) where
  irel _ x y := Rel.rel x.t y.t
  rel x y := Rel.rel x.t y.t
  equivalence := by
    apply Equivalence.mk
    · intro
      apply ERel.refl
    · simp
      intros
      apply ERel.symm
      trivial
    · simp
      intros
      apply ERel.trans
      · trivial
      · trivial
  equiv := by
    intro n
    apply Equivalence.mk
    · intro
      apply ERel.refl
    · simp
      intros
      apply ERel.symm
      trivial
    · simp
      intros
      apply ERel.trans
      · trivial
      · trivial
  mono := by simp [IRel.irel]
  limit := by simp [IRel.irel]

instance [ERel T] : DiscreteOFE (Δ T) where
  discrete := by simp [IRel.irel]

lemma discrete_equiv_iff_n_iRel (T : Type) [DiscreteOFE T] (n : ℕ) (x y : T) :
    (x ≈[n] y) <-> x ≈ y := by
  apply Iff.intro
  · intro H
    apply DiscreteOFE.discrete
    apply OFE.dist_le H
    apply Nat.zero_le
  · intros
    apply OFE.limit.mpr
    trivial

lemma discrete_equiv_iff_0_iRel (T : Type) [DiscreteOFE T] (x y : T) :
    (x ≈[0] y) <-> x ≈ y := by
  apply discrete_equiv_iff_n_iRel



/-
## OFE on function types

Use the bundled function type
-/

instance [OFE A] [OFE B] : IRel (A -n> B) where
  irel n f g := ∀ x, f x ≈[n] g x

instance [OFE A] [OFE B] : Rel (A -n> B) where
  rel f g := ∀ x, f x ≈ g x

instance [OFE A] [OFE B] : ERel (A -n> B) where
  equivalence := by
    apply Equivalence.mk <;> simp only [Rel.rel]
    · intros
      exact OFE.refl
    · intros _ _ H _
      apply OFE.symm
      apply H
    · intros _ _ _ H1 H2 _
      apply OFE.trans
      · apply H1
      · apply H2

instance [OFE A] [OFE B] : OFE (A -n> B) where
  equiv := by
    intro n
    apply Equivalence.mk <;> simp only [IRel.irel]
    · intros
      apply OFE.irefl
    · intros _ _ H _
      apply OFE.isymm
      apply H
    · intros _ _ _ H1 H2 _
      apply OFE.itrans
      · apply H1
      · apply H2
  mono := by
    simp only [is_indexed_mono, IRel.irel]
    intros _ _ _ _ H1 H2 _
    apply OFE.mono H1
    apply H2
  limit := by
    simp only [is_indexed_refinement, IRel.irel, Rel.rel]
    intros _ _
    apply Iff.intro
    · intros H _
      apply OFE.limit.mp
      intro _
      apply H
    · intros H _ _
      apply OFE.limit.mpr
      apply H

lemma nonexpansive_ccompose [OFE α] [OFE β] [OFE γ] :
    nonexpansive2 (@ccompose α β γ _ _ _) := by
  simp [nonexpansive2]
  intro _ _ _ _ _ H1 H2 _
  simp [ccompose, DFunLike.coe]
  -- FIXME: Setoid
  apply OFE.itrans
  · apply NonExpansive.unif_hom
    apply H2
  apply OFE.isymm
  apply OFE.itrans
  · apply OFE.isymm
    apply H1
  apply OFE.irefl


lemma eq_proper_ccompose [OFE α] [OFE β] [OFE γ] :
    proper2 Rel.rel Rel.rel Rel.rel (@ccompose α β γ _ _ _) := by
  simp [ccompose, DFunLike.coe]
  intros _ _ _ _ H1 H2 _
  -- FIXME: Setoid
  apply OFE.trans
  · apply H1
  apply OFE.equiv_proper
  · apply NonExpansive.unif_hom
  apply H2


lemma NonExpansive.map_nonexpansive [OFE A] [OFE B] [OFE A'] [OFE B'] :
    nonexpansive3 (@NonExpansive.map A B A' B' _ _ _ _) := by
  simp [nonexpansive3, NonExpansive.map]
  intro _ _ _ _ _ _ _ H1 H2 H3 x
  -- FIXME: Setoid
  apply nonexpansive_ccompose
  · apply H2
  apply nonexpansive_ccompose
  · apply H3
  · apply H1


/-
## Chains
-/

/-- [unbundled] c satisfies the chain property -/
@[simp]
def chain_is_cauchy {α : Type} [OFE α] (c : Nat -> α) : Prop :=
  ∀ {m n : Nat}, n ≤ m -> (c m) ≈[n] (c n)

/-- The type of functions which satisfy the chain property -/
abbrev Chain (α : Type) [OFE α] := { c : Nat -> α // chain_is_cauchy c }

instance (α : Type) [OFE α] : CoeFun (Chain α) (fun _ => (Nat -> α)) where
  coe s := s.1

lemma chain_is_cauchy' [OFE α] (c : Chain α) : ∀ {m n : Nat}, n ≤ m -> (c m) ≈[n] (c n) := by
  rcases c with ⟨ _, cauchy ⟩
  simp
  intros
  apply cauchy
  trivial




def Chain.cmap {α β : Type} [OFE α] [OFE β] {f : α -> β} (c : Chain α) (Hf : nonexpansive f) : Chain β where
  val := f ∘ c
  property := by
    rcases c with ⟨ c', Hc' ⟩
    simp [chain_is_cauchy, DFunLike.coe ]
    intros m n Hnm
    simp at Hc'
    apply Hf
    apply Hc'
    apply Hnm

def Chain.const {α : Type} [OFE α] (x : α) : Chain α where
  val _ := x
  property := by
    intro _ _ _
    simp
    apply OFE.irefl


@[simp]
def nonexpansive_app_chain [OFE α] [OFE β] (c : Chain (α -n> β)) (x : α) : Chain β where
  val n := c n x
  property := by
    intro _ _ _
    simp only [chain_is_cauchy, IRel.irel]
    rcases c with ⟨ f, cauchy ⟩ -- FIXME: chain_is_cauchy'
    simp only []
    apply cauchy
    trivial





/-
## COFE
-/

class COFE (α : Type) extends OFE α where
  lim : Chain α -> α
  complete : ∀ (n : Nat), ∀ (c : Chain α), (lim c) ≈[n] (c n)

lemma COFE.map {α β : Type} [COFEα: COFE α] [COFEβ : COFE β] (f : α -> β) (c : Chain α) (Hf : nonexpansive f) :
    lim (Chain.cmap c Hf) ≈ f (lim c) := by
  apply OFE.limit.mp
  intro n

  -- NOTE: Setoid rewrite
  apply @(@COFEβ.equiv n).trans _ _ _ _ ?G
  case G =>
    apply Hf
    apply (@COFEα.equiv n).symm
    apply @COFEα.complete
  apply @(@COFEβ.equiv n).trans _ _ _ ?G
  case G =>
    apply @COFEβ.complete
  simp
  apply @(@COFEβ.equiv n).refl


lemma COFE.lim_const {α : Type} [COFE α] (x : α) :
    lim (Chain.const x) ≈ x := by
  apply OFE.limit.mp
  intro _
  apply complete


instance [OFE α] [COFE β] : COFE (α -n> β) where
  lim c :=
    let f (x : α) : β := COFE.lim <| nonexpansive_app_chain c x
    let ne : nonexpansive f := by
      simp only [nonexpansive, is_nonexpansive, proper1]
      intro n x y H
      -- FIXME: Setoids
      apply OFE.itrans
      · apply COFE.complete _ (nonexpansive_app_chain c x)
      apply OFE.isymm
      apply OFE.itrans
      · apply COFE.complete _ (nonexpansive_app_chain c y)
      apply OFE.isymm
      simp
      apply NonExpansive.unif_hom -- Proper
      trivial
    NonExpansive.mk f ne
  complete := by
    intro n c
    intro x
    -- FIXME: annoying coercion
    rcases c with ⟨ c, cauchy ⟩
    simp [DFunLike.coe]
    -- FIXME: Setoids
    apply OFE.itrans
    · apply COFE.complete _
    simp
    apply OFE.irefl


@[simp]
def limit_preserving [COFE α] (P : α -> Prop) : Prop :=
  ∀ (c : Chain α), (∀ n, P (c n)) -> P (COFE.lim c)


lemma limit_preserving.ext [COFE α] (P Q : α -> Prop) :
    (∀ x, P x = Q x) -> limit_preserving P -> limit_preserving Q := by
  intro H
  rewrite [<- funext H]
  simp only [imp_self]


lemma limit_preserving.const [COFE α] (P : Prop) : limit_preserving (fun (_ : α) => P) := by
  simp

/-
lemma limit_preserving_discrete [COFE α] (P : α -> Prop) :
    proper1 (IRel.irel 0) Eq P -> limit_preserving P := by
  intros HP _ _
  sorry
-/


lemma limit_preserving.and [COFE α] (P Q : α -> Prop) :
    limit_preserving P -> limit_preserving Q -> limit_preserving (fun a => P a ∧ Q a):= by
  simp
  intros H1 H2 _ _ H3
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



/-
## The category of COFE's
-/

/-- [bundled] [3.1] Objects in the category of COFE's -/
def COFECat := CategoryTheory.Bundled COFE

-- [3.2]
instance : CoeSort COFECat Type where
  coe := CategoryTheory.Bundled.α

-- [3.3]
instance (X : COFECat) : COFE X := X.str

/-- [3.4] Bundle a COFE instance into an COFECat -/
def COFE.of (T : Type) [COFE T] : COFECat :=
  CategoryTheory.Bundled.of T

abbrev NonExpansive' (M N : Type) [COFE M] [COFE N] : Type := @NonExpansive M N _ _


-- [4.1] Homs in the category of COFE's
instance : CategoryTheory.BundledHom @NonExpansive' where
  toFun _ _ F := F
  id _ := cid
  comp _ _ _ g f := ccompose g f
  comp_toFun _ _ _ f g := by
    simp only [DFunLike.coe]
    rfl

instance : CategoryTheory.LargeCategory @COFECat :=
  CategoryTheory.BundledHom.category @NonExpansive'

instance : CategoryTheory.ConcreteCategory COFECat :=
  CategoryTheory.BundledHom.concreteCategory NonExpansive'





/-
## Contractive functions
-/

lemma contractive0 {α β: Type} (f : α -> β) [OFEα : OFE α] [OFE β] [Inhabited α] (H : contractive f) x y :
    f x ≈[ 0 ] f y := by
  apply H
  apply iLater_0

lemma contractiveS {α β : Type} (f : α -> β) [OFE α] [OFE β] (H : contractive f) x y n :
    (x ≈[ n ] y) -> f x ≈[ n + 1 ] f y := by
  intro _
  apply H
  apply OFE.iLater_S.mp
  trivial

lemma contractive_iLater {α β : Type} (f : α -> β) [OFE α] [OFE β] (H : contractive f) x y n :
    (x ≈L[n] y) -> f x ≈[ n ] f y := by
  intro _
  apply H
  trivial

lemma const_contractive {α β: Type} [OFE α] [OFE β] (x : β) : contractive (fun (_ : α) => x) := by
  intro _ _ _ _
  apply OFE.irefl





/-
## Fixpoint
-/

/-- [unbundled] fixpoint -/
def fixpoint_chain [OFE α] (f : α -> α)  [Inhabited α] (H : contractive f) : Chain α where
  val n := Nat.repeat f (n + 1) default
  property := by
    simp [chain_is_cauchy]
    intro n
    induction n
    · intro i
      cases i
      · intro
        apply OFE.irefl
      · simp
    · rename_i n IH
      intro i
      simp [Nat.repeat]
      cases i
      · intro
        apply contractive0
        apply H
      · intro
        apply contractiveS
        · apply H
        apply IH
        simp_all only [Nat.add_le_add_iff_right]

-- /- [unbundled] -/
-- def fixpoint [COFE α] [Inhabited α] (f : α -> α) (H : contractive f) : α :=
--   COFE.lim (fixpoint_chain f H)

def Contractive.fixpoint_chain [COFE α] [Inhabited α] (f : α -c> α) : Chain α :=
  _root_.fixpoint_chain f f.contractive

/-- [bundled] -/
def Contractive.fixpoint [COFE α] [Inhabited α] (f : α -c> α) : α :=
  COFE.lim (fixpoint_chain f)

/-- [bundled] -/
lemma Contractive.unfold [COFE α] [Inhabited α] (f : α -c> α) :
    Contractive.fixpoint f ≈ f (Contractive.fixpoint f) := by
  apply OFE.limit.mp
  intro n
  -- FIXME: Setoid
  apply OFE.itrans
  · apply COFE.complete n (fixpoint_chain f)
  apply OFE.isymm
  apply OFE.itrans
  · -- apply Contractive.contractive
    apply Contractive.unif_hom
    apply COFE.complete n (fixpoint_chain f)
  apply OFE.isymm
  induction n
  · simp [DFunLike.coe]
    apply (contractive0 f f.contractive)
  · rename_i n IH
    apply (contractiveS f f.contractive)
    apply IH

lemma Contractive.unique [COFE α] [Inhabited α] (f : α -c> α) (x : α) :
    (x ≈ f x) -> x ≈ fixpoint f := by
  intro H
  apply OFE.limit.mpr at H
  apply OFE.limit.mp
  intro n
  -- FIXME: Setoid
  let L := Contractive.unfold f
  apply OFE.limit.mpr at L
  induction n
  · apply OFE.itrans
    · apply H
    apply OFE.isymm
    apply OFE.itrans
    · apply L
    apply OFE.isymm
    apply (contractive0 f f.contractive)
  · rename_i n IH
    apply OFE.itrans
    · apply H
    apply OFE.isymm
    apply OFE.itrans
    · apply L
    apply OFE.isymm
    apply (contractiveS f f.contractive)
    apply IH


lemma Contractive.fixpoint_ne [COFE α] [Inhabited α] (f g : α -c> α) n :
    (∀ z, f z ≈[n] g z) -> fixpoint f ≈[n] fixpoint g := by
  intro H
  -- FIXME: Setoid
  apply OFE.itrans
  · apply COFE.complete
  apply OFE.isymm
  apply OFE.itrans
  · apply COFE.complete
  apply OFE.isymm
  simp [fixpoint_chain, _root_.fixpoint_chain, Nat.repeat]
  induction n
  · apply H
  rename_i n IH
  simp [Nat.repeat]
  apply OFE.itrans
  · apply H
  apply Contractive.contractive
  apply (@iLater_S α IRel.irel OFE.mono _ _ n).mp
  apply IH
  intro i
  apply is_indexed_mono_le
  · apply OFE.mono
  · apply H
  · simp

lemma Contractive.proper [COFE α] [Inhabited α] (f g : α -c> α) :
    (∀ x, f x ≈ g x) -> fixpoint f ≈ fixpoint g := by
  intro H
  apply OFE.limit.mp
  intro
  apply Contractive.fixpoint_ne
  intro z
  apply OFE.limit.mpr (H z)


lemma Contractive.fixpoint_ind [COFE α] [Inhabited α] (f : α -c> α)
    (P : α -> Prop) (HP : proper1 Rel.rel (fun A B => A -> B) P)
    (Hbase : ∃ x, P x) (Hind : ∀ x, P x -> P (f x)) (Hlim : limit_preserving P) :
    P (fixpoint f) := by
  rcases Hbase with ⟨ x, Hx ⟩
  let chain : Chain α :=
    ⟨ fun i => Nat.repeat f (i + 1) x,
      by
        intro n
        simp only []
        induction n
        · simp [OFE.irefl]
        · rename_i i IH
          intros n H
          simp [Nat.repeat]
          apply Contractive.contractive
          cases n
          · apply @iLater_0
          rename_i n
          apply (@iLater_S α _ OFE.mono x x n).mp -- FIXME: What is that x x doing? Seems like a bug
          apply IH
          simp_all
        ⟩
  apply HP
  · apply Contractive.unique f (COFE.lim chain)
    apply OFE.limit.mp
    intro n
    -- FIXME: Setoid
    apply OFE.itrans
    · apply COFE.complete
    apply OFE.isymm
    apply OFE.itrans
    · apply Contractive.unif_hom
      apply COFE.complete
    apply OFE.isymm
    simp [chain, Nat.repeat]
    induction n
    · apply Contractive.contractive
      apply iLater_0
    rename_i i IH
    simp [Nat.repeat]
    apply Contractive.contractive
    apply (@iLater_S α _ OFE.mono x x i).mp -- FIXME: iLater_S bug
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




/-
## Unit type
-/

def unitO : Type := Unit

instance : OFE unitO where
  irel _ _ _ := True
  rel _ _ := True
  equivalence := by simp [Equivalence.mk]
  equiv := by simp [Equivalence.mk]
  mono := by simp
  limit := by simp

instance : DiscreteOFE unitO where
  discrete := by simp

instance : COFE unitO where
  lim _ := Unit.unit
  complete := by simp

/-
## Empty type
-/

def emptyO : Type := Empty

instance : OFE emptyO where
  irel _ _ _ := True
  rel _ _ := True
  equivalence := by simp [Equivalence.mk]
  equiv := by simp [Equivalence.mk]
  mono := by simp
  limit := by simp

instance : DiscreteOFE emptyO where
  discrete := by simp

instance : COFE emptyO where
  lim c := by cases c 0
  complete c := by simp



/-
## Product OFE
-/
def prodO (A B : Type) : Type := A × B


-- instance [OFE A] [OFE B] : Coe (A × B) (prodO A B) where
--   coe := sorry

instance [OFE A] [OFE B] : OFE (prodO A B) where
  irel n x y := (x.1 ≈[n] y.1) ∧ (x.2 ≈[n] y.2)
  rel x y := (x.1 ≈ y.1) ∧ (x.2 ≈ y.2)
  equivalence := by
    apply Equivalence.mk
    · intro
      simp only [Rel.rel]
      apply And.intro
      · apply OFE.refl
      · apply OFE.refl
    · simp
      intros
      apply And.intro
      · apply OFE.symm
        trivial
      · apply OFE.symm
        trivial
    · simp
      intros
      apply And.intro
      · apply OFE.trans
        · trivial
        · trivial
      · apply OFE.trans
        · trivial
        · trivial
  equiv := by
    intro n
    apply Equivalence.mk
    · intro
      simp only [Rel.rel]
      apply And.intro
      · apply OFE.irefl
      · apply OFE.irefl
    · simp
      intros
      apply And.intro
      · apply OFE.isymm
        trivial
      · apply OFE.isymm
        trivial
    · simp
      intros
      apply And.intro
      · apply OFE.itrans
        · trivial
        · trivial
      · apply OFE.itrans
        · trivial
        · trivial
  mono := by
    simp
    intros
    apply And.intro
    · apply OFE.mono
      · trivial
      · trivial
    · apply OFE.mono
      · trivial
      · trivial
  limit := by
    simp
    intros
    apply Iff.intro
    · intros
      rename_i H
      apply And.intro
      · apply OFE.limit.mp
        intro n
        apply (H n).1
      · apply OFE.limit.mp
        intro n
        apply (H n).2
    · simp
      intros
      apply And.intro
      · apply OFE.limit.mpr
        trivial
      · apply OFE.limit.mpr
        trivial

lemma fst_nonexpansive [OFE A] [OFE B] : @nonexpansive (prodO A B) A _ _ Prod.fst := by
  simp [nonexpansive]
  intros
  trivial

lemma snd_nonexpansive [OFE A] [OFE B] : @nonexpansive (prodO A B) B _ _ Prod.snd := by
  simp [nonexpansive]

instance [COFE A] [COFE B] : COFE (prodO A B) where
  lim c :=
    (COFE.lim (Chain.cmap c fst_nonexpansive), COFE.lim (Chain.cmap c snd_nonexpansive))
  complete := by
    simp
    intros
    apply And.intro
    · apply COFE.complete
    · apply COFE.complete

instance [DiscreteOFE A] [DiscreteOFE B] : DiscreteOFE (prodO A B) where
  discrete := by
    simp
    intros
    apply And.intro
    · apply DiscreteOFE.discrete
      trivial
    · apply DiscreteOFE.discrete
      trivial

-- #synth OFE (prodO emptyO emptyO)

-- FIXME: Fix this goofy type
-- Even if I delete this lemma it's silly to have to state it like this
-- Do I need a low-priority coercion instance or something?
-- TODO: Give a notation for this?

abbrev prodC [OFE A] [OFE B] (a : A) (b : B) : prodO A B := (a, b)


lemma prod_irel_iff [OFE A] [OFE B] (a a' : A) (b b' : B) (n : ℕ) :
    (prodC a b ≈[n] prodC a' b') <-> (a ≈[n] a') ∧  (b ≈[n] b') := by
  simp

-- def test [COFE A] [COFE A'] [COFE B] [COFE B']
--   (f : A -n> A') (g : B -n> B') : (prodO A B) -n> (prodO A' B') where
--      toFun := sorry
--      unif_hom := sorry

/-
## oFunctors (OFE -> COFE functors)
-/

-- TODO: I wonder if this could be written as an actual (bi)functor between categories?
-- The Hom functor does exist in Mathlib
-- NOTE: No hierarchy. Do we need it?

/-- [bundled] COFE -> OFE bifunctor -/
structure oFunctor where
  car : COFECat × COFECat -> OFECat
  map [COFE A] [COFE A'] [COFE B] [COFE B'] :
    (prodO (A' -n> A) (B -n> B')) -> (car (COFE.of A, COFE.of B) -n> car (COFE.of A', COFE.of B'))
  map_ne [COFE A] [COFE A'] [COFE B] [COFE B'] : nonexpansive (@map A A' B B' _ _ _ _)
  map_id [COFE A] [COFE B] (x : car (COFE.of A, COFE.of B)) : map (prodC cid cid) x ≈ cid x
  map_cmp [COFE A] [COFE A'] [COFE A''] [COFE B] [COFE B'] [COFE B'']
      (f : A' -n> A) (g : A'' -n> A') (f' : B -n> B') (g' : B' -n> B'') x :
    map (prodC (ccompose f g) (ccompose g' f')) x ≈ (map (prodC g g') (map (prodC f f') x))

/-- Mixin: an oFunctor is contractive -/
class oFunctorContractive (F : oFunctor) where
  map_contractive [COFE A] [COFE A'] [COFE B] [COFE B'] :
    contractive (@oFunctor.map F A A' B B' _ _ _ _)

/-- Action of the oFunctor on objects -/
def oFunctor.app (F : oFunctor) (a : COFECat) : OFECat := F.car (a, a)






-- def NonExpansive.irrel [M1 : OFE M] [M2 : OFE M] [N1 : OFE N] [N2 : OFE N]
--     (NE1 : @NonExpansive M N M1 N1)
--     (HIRel : @OFE.toIRel M M2 = @OFE.toIRel M M1) : @NonExpansive M N M2 N2 where
--   toFun := @NE1.toFun
--   unif_hom := by
--     simp [nonexpansive]
--     intros n x y H
--     rewrite [HIRel] at H
--     let X := @NE1.unif_hom n x  y
--     sorry


-- def OFECat_is_COFE (a : OFECat) : Prop := sorry
-- /-
-- An oFunctor which only sends objects to COFEs
-- -/
-- class oFunctorCOFE (F : oFunctor) where
--   coe : OFECat -> COFECat
--   coe_id [COFE A] [COFE A'] [COFE B] [COFE B'] (m : prodO (A' -n> A) (B -n> B')):
--     ∀ p, OFECat_is_COFE (F.map m p)


-- TODO: We can only compose oFunctors whose range is all COFE's


-- def oFunctor_cmp (F1 F2 : oFunctor) [∀ p, COFE (F2.car p)] : oFunctor where
--   car p := F1.car (COFE.of (F2.car (p.2, p.1)), COFE.of (F2.car (p.1, p.2)))
--   map m :=
--     let L1 := F2.map (m.2, m.1)
--     let L2 := F2.map (m.1, m.2)
--     F1.map (prodC
--       (@NonExpansive.irrel _ _ _ _ _ _ L1 sorry)
--       sorry)
--     -- (by
--     --   dsimp
--     --   apply F1.map
--     --   · apply L1
--     --   · apply L2)
--   map_ne := sorry
--   map_id := sorry
--   map_cmp := sorry

















/-
## Leibniz OFE
-/

@[simp]
def WithEquality (T : Type) : Type := T

instance : ERel (WithEquality T) where
  rel := Eq
  equivalence := by simp [Equivalence.mk]

abbrev LeibnizO T := Δ (WithEquality T)

instance : LeibnizRel (LeibnizO T) where
  leibniz := by
    simp [WithEquality, Rel.rel]
    intros x y
    cases x
    cases y
    simp


-- #synth ERel (LeibnizO Bool)
-- #synth OFE (LeibnizO Bool)

def boolO := LeibnizO Bool
def natO  := LeibnizO ℕ
def intO  := LeibnizO ℤ
/- Because we're using propext  anyways, can use equuality here -/
def propO  := LeibnizO Prop





/-
## Later OFE
-/


structure laterO (T : Type) : Type where
  Next ::
  t : T

prefix:max  "▸"  => laterO

-- FIXME: Clean up this instance
instance [I : OFE T] : OFE ▸T where
  irel n x y:= later (I.irel) n x.t y.t
  rel x y := I.rel x.t y.t
  equivalence := by
    apply Equivalence.mk
    · simp
      intro
      apply OFE.refl
    · simp
      intros
      apply OFE.symm
      trivial
    · simp
      intros
      apply OFE.trans
      · trivial
      · trivial
  equiv := by
    intro n
    -- apply iLater_is_indexed_equiv
    apply Equivalence.mk
    · simp [later]
      intros
      apply OFE.irefl
    · simp [later]
      intros _ _ H _ _
      apply OFE.isymm
      apply H
      trivial
    · simp [later]
      intros _ _ _ H1 H2 _ _
      apply OFE.itrans
      · apply H1
        trivial
      · apply H2
        trivial
  mono := by
    apply iLater_is_indexed_mono
    simp
    intros
    apply OFE.mono
    · trivial
    · trivial
  limit := by
    apply iLater_is_indexed_refinement
    · simp
      intros
      apply OFE.limit
    · simp
      intros
      apply OFE.mono
      · trivial
      · trivial


def Chain.later [OFE α] (c : Chain ▸α) : Chain α where
  val n := laterO.t <| c <| Nat.succ n
  property := by
    simp [DFunLike.coe]
    intros
    apply c.property
    · simp
      trivial
    · apply Nat.lt_add_one

instance [COFE α] : COFE (▸α) where
  lim := laterO.Next ∘ COFE.lim ∘ Chain.later
  complete := by
    intros n c
    cases n
    · apply iLater_0
    rename_i n
    -- FIXME: Setoid
    simp only [IRel.irel, Function.comp_apply]
    apply (@iLater_S α IRel.irel OFE.mono _ _ _).mp
    apply OFE.isymm
    apply OFE.itrans
    · apply OFE.isymm
      apply COFE.complete _ c.later
    apply OFE.irefl


lemma Next_contractive [OFE T] : contractive (@laterO.Next T) := by
  simp [contractive, is_contractive]

lemma later_car_anti_contractive [OFE T] : anticontractive (@laterO.t T) := by
  simp [anticontractive, is_anticontractive]

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
      apply OFE.refl
  · intros H
    rcases H with ⟨ g, ⟨ HNE, H ⟩ ⟩
    simp [contractive, is_contractive]
    intros n x y HL
    -- FIXME: Setoid
    apply OFE.itrans
    · apply (OFE.limit).mpr
      apply H
    apply OFE.isymm
    apply OFE.itrans
    · apply (OFE.limit).mpr
      apply H
    apply OFE.isymm
    apply HNE
    apply HL

-- FIXME: How many of these lemmas need to be the stronger (pre_map) version?
-- FIXME: I feel like I should be able to remove laterO_pre_map:
--        Need to infer that the result is nonexpansive when the argument is nonexpansive
--        So that the input can cast from A -n> B and the output can cast to ▸A -n> ▸B

-- See: Topology.ContinusFunction.Basic

-- C(A, B) is my A -n> B


/--
The implementation of laterO.map, which isn't nonexpansive, but doesn't rewure a nonexpansive input

Not sure how ofen we map by a nonexpansive map, but it might be useful?
-/
@[simp]
def laterO.map (f : A -> B) (x : ▸A) : ▸B := Next <| f x.t


-- CanLift doesn't work
-- section test
-- variable [OFE A] [OFE B] (f : A -> B)
-- variable (H : nonexpansive f)
--
-- #check laterO.pre_map f
-- #check (laterO.pre_map f : ▸A -> ▸B)
--
-- example : True := by
--   lift f to (A -n> B) using H
--   simp
--
-- end test

lemma later_map_ne [OFE A] [OFE B] (f : A -> B) (HN : ∀ n, proper1 (later IRel.irel n) (later IRel.irel n) f) :
    nonexpansive (laterO.map f) := by
  simp [nonexpansive]
  intros
  apply HN
  trivial

lemma later_map_ne' [OFE A] [OFE B] (f : A -n> B) : nonexpansive (laterO.map f) := by
  simp [nonexpansive, later]
  intros _ _ _ H _ _
  apply NonExpansive.unif_hom
  apply H
  trivial


lemma later_equiv_proper [OFE A] [OFE B] (f : A -> B) (HN : proper1 Rel.rel Rel.rel f) :
    proper1 Rel.rel Rel.rel (laterO.map f) := by
  simp [nonexpansive]
  intros
  apply HN
  trivial

lemma later_map_next [OFE A] [OFE B] (f : A -> B) (x : A) :
    laterO.map f (laterO.Next x) = laterO.Next (f x) := by
  simp only [laterO.map]

lemma later_map_id [OFE A] [OFE B] (f : A -> B) (x : ▸A) :
    laterO.map id x = x := by
  simp only [laterO.map, id_eq]

lemma later_map_cmp [OFE A] [OFE B] [OFE C] (f : A -> B) (g : B -> C) (x : ▸ A):
    laterO.map (g ∘ f) x = laterO.map g (laterO.map f x) := by
  simp only [laterO.map, Function.comp_apply]

lemma later_map_ext [OFE A] [OFE B] (f : A -> B) :
    (∀ x, f x ≈ g x) -> laterO.map f x ≈ laterO.map g x := by
  intro H
  simp only [Rel.rel, laterO.map]
  apply H

instance [OFE A] [OFE B] [FunLike F A B] (f : F) [HasNonExpansive f] : HasNonExpansive (laterO.map f) where
  ne := by
    simp [DFunLike.coe]
    simp [nonexpansive, later]
    intros _ _ _ H _ _
    apply HasNonExpansive.ne
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
 apply OFE.itrans
 · apply H
   trivial
 apply OFE.irefl









/-

/-- The type of step-indexed propositions -/
@[ext]
structure SProp where
  sp : Nat -> Prop
  sp_down_closed : ∀ n m : Nat, m ≤ n -> sp n -> sp m

instance : CoeFun SProp (fun _ => (Nat -> Prop)) where
  coe s := s.1

instance : IRel SProp where
  irel n sp1 sp2 := ∀ m, m ≤ n -> (sp1 m <-> sp2 m)


instance : OFE SProp where
  equiv := by
    simp [IRel.irel]
    intro n
    constructor
    · intros; rfl
    · intro _ _ H _ Hmn
      symm
      apply H
      apply Hmn
    · intro _ _ _ H1 H2 _ Hnm
      trans
      · apply H1
        trivial
      · apply H2
        trivial
  mono  := by
    simp [IRel.irel]
    intro m n x y Hmn H1 m' Hm'
    rcases x with ⟨ x, Hx ⟩
    rcases y with ⟨ y, Hy ⟩
    simp_all
    apply Iff.intro
    · intro z
      -- apply Hy
      sorry
    · sorry
  limit := by
    simp [IRel.irel]
    intro x y
    apply Iff.intro
    · intro H
      apply SProp.ext
      apply funext
      intro z
      apply propext
      apply H z
      apply Nat.le_refl
    · intro H
      subst H
      simp
-/
-/
