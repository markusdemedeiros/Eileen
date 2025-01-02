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



-- NOTE / Skipped
--  - Apparently inferring the right OFE is hard for CMRA's and unital CMRA's (ln. 100)
--  - Bundled type
--  + 160

-- FIXME: Fix the naming scheme
-- FIXME: Generalize type unvierses

/-
# Basic props
-/

abbrev relation (T : Type) : Type := T -> T -> Prop

abbrev irelation (T : Type) := ℕ -> T -> T -> Prop


/-- [unbundled] A relation is an equivalence relation  -/
@[simp]
abbrev is_equiv_rel {T : Type} (R : relation T) := Equivalence R

/-- [unbundled] An indexed relation is an indexed equivalence relation  -/
@[simp]
def is_indexed_equiv {T : Type} (R : irelation T) : Prop :=
  ∀ n : ℕ, is_equiv_rel (R n)

/-- [unbundled] the indexed relation is down-closed -/
@[simp]
def is_indexed_mono {T : Type} (R : irelation T) : Prop :=
  ∀ {m n : Nat}, ∀ {x y : T}, m < n -> R n x y -> R m x y

/-- [unbundled] the indexed relation R refines the relation R' -/
@[simp]
def is_indexed_refinement {T : Type} (R : irelation T) (R' : relation T) : Prop :=
  ∀ {x y : T}, (∀ n, R n x y) <-> R' x y

-- /- [unbundled] R forms an OFE with respect to R' -/
-- @[simp]
-- def is_ofe {T : Type u} (R : ℕ -> T -> T -> Prop) (R' : T -> T -> Prop) : Prop :=
--   is_indexed_equiv R ∧
--   is_indexed_mono R ∧
--   is_indexed_refinement R R'

/-- A relation that is one later than R -/
def later {T : Type} (R : irelation T) : irelation T :=
  fun n x y => ∀ m, m < n -> R m x y

/-- [unbundled] A function is nonexpansive wrt. two indexed equivalences -/
@[simp]
def is_nonexpansive {M N : Type} (RM : irelation M) (RN : irelation N) (f : M -> N) : Prop :=
  ∀ (n : Nat), proper1 (RM n) (RN n) f

@[simp]
def is_nonexpansive2 {M N T : Type} (RM : irelation M) (RN : irelation N) (RT : irelation T) (f : M -> N -> T) : Prop :=
  ∀ (n : Nat), proper2 (RM n) (RN n) (RT n) f

@[simp]
def is_nonexpansive3 {M N T : Type} (RM : irelation M) (RN : irelation N) (RT : irelation T) (RS : irelation S)
  (f : M -> N -> T -> S) : Prop :=
  ∀ (n : Nat), proper3 (RM n) (RN n) (RT n) (RS n) f


/-- [unbundled] A function is contractive wrt. two indexed equivalences -/
@[simp]
def is_contractive {M N : Type} (RM : irelation M) (RN : irelation N) (f : M -> N) : Prop :=
  ∀ (n : Nat), proper1 (later RM n) (RN n) f


/-- [unbundled] A function is contractive wrt. two indexed equivalences -/
@[simp]
def is_contractive2 {M N S : Type} (RM : irelation M) (RN : irelation N) (RS : irelation S) (f : M -> N -> S) : Prop :=
  ∀ (n : Nat), proper2 (later RM n) (later RN n) (RS n) f

@[simp]
def is_anticontractive {M N : Type} (RM : irelation M) (RN : irelation N) (f : M -> N) : Prop :=
  ∀ (n : Nat), proper1 (RM n) (later RN n) f

def is_indexed_mono_le {R : irelation T} (H : is_indexed_mono R) :
    R n x y -> (m ≤ n) -> R m x y := by
  intros _ H'
  cases (Nat.eq_or_lt_of_le H')
  · simp_all
  · rename_i h
    apply H h
    trivial

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




/-
## iLater properties
-/

lemma iLater_is_indexed_equiv {T : Type} (R : irelation T) (H : is_indexed_equiv R) :
    is_indexed_equiv (later R) := by
  intro n
  apply Equivalence.mk
  · intro _ m _
    apply (H m).refl
  · intro _ _ HL
    intro m _
    apply (H m).symm
    apply HL
    trivial
  · intro _ _ _ HL1 HL2
    intro m Hm
    apply (H m).trans
    · apply HL1 _ Hm
    · apply HL2 _ Hm

lemma iLater_is_indexed_mono {T : Type} (R : irelation T) (H : is_indexed_mono R) :
    is_indexed_mono (later R) := by
  intro _ _ _ _ _ HL
  intro _ Hm'
  apply H Hm'
  apply HL
  trivial

lemma rel_later_iLater {T : Type} (R : irelation T) (H : is_indexed_mono R) (x y : T) (n : ℕ) :
    R n x y -> (later R) n x y := by
  intro _ _ Hm
  apply H Hm
  trivial

lemma iLater_lt_rel {T : Type} (R : irelation T) (x y : T) (m n : ℕ) :
    m < n -> (later R) n x y -> R m x y := by
  intro _ H2
  apply H2
  trivial

lemma iLater_0 {T : Type} (R : irelation T) (x y : T) :
    (later R) 0 x y := by
  intro _
  simp only [Nat.not_lt_zero, IsEmpty.forall_iff]

lemma iLater_S {T : Type} (R : irelation T) (H : is_indexed_mono R) (x y : T) (n : ℕ):
    R n x y <-> (later R) (Nat.succ n) x y := by
  apply Iff.intro
  · intro H' m Hm
    -- FIXME: Where are all those extra goals coming from?
    -- apply is_indexed_mono_le H H' (Nat.le_of_lt_succ Hm)
    exact @is_indexed_mono_le T n x y m R H H' (Nat.le_of_lt_succ Hm)
  · intro H'
    apply H'
    apply Nat.lt_add_one

lemma iLater_is_indexed_refinement {T : Type} (R : irelation T) (R' : relation T)
  (Hi : is_indexed_refinement R R') (Hm : is_indexed_mono R) :
    is_indexed_refinement (later R) R' := by
  intro x y
  apply Iff.intro
  · intro H
    apply Hi.mp
    intro _
    apply (iLater_S R Hm _ _ _).mpr
    apply H
  · intro _ _ _ _
    apply Hi.mpr
    trivial





/-
# Typeclass hierarchy (semi-bundled)
-/

/--
A type with a binary relation
Note: Dupe of std
-/
class Rel (T : Type u) where
  rel : T -> T -> Prop

notation:30 a1 " ≈ "  a2 => Rel.rel a1 a2

attribute [simp] Rel.rel

/--
An equivalence relation
-/
class ERel (T : Type) extends Rel T where
  equivalence : Equivalence (@Rel.rel T _)

-- FIXME: Notations
lemma ERel.refl [ERel T] : ∀ x, (@Rel.rel T _ x x) :=
  ERel.equivalence.refl

-- FIXME: Notations
lemma ERel.symm [ERel T] : ∀ {x y}, (@Rel.rel T _ x y) → (@Rel.rel T _ y x) :=
  ERel.equivalence.symm

-- FIXME: Notations
lemma ERel.trans [ERel T] : ∀ {x y z}, (@Rel.rel T _ x y) -> (@Rel.rel T _ y z) -> (@Rel.rel T _ x z) :=
  ERel.equivalence.trans

class LeibnizRel (T : Type u) extends Rel T where
  leibniz : ∀ {x y : T}, (x ≈ y) -> x = y


/--
An indexed binary relation
Note: duplicate  of std.
-/
class IRel.{u} (T : Type u) where
  /-- The indexed binary operation on a type -/
  irel : ℕ -> T -> T -> Prop

attribute [simp] IRel.irel

-- FIXME: Brackets
notation:30 a1 " ≈[ " n " ] "  a2 => IRel.irel n a1 a2
notation:30 a1 " ≈L[ " n " ]"  a2 => (later IRel.irel n) a1 a2 -- This notation should just be used internally


/-- A function between IRels is nonexpansive -/
def nonexpansive [M : IRel T1] [N : IRel T2] (f : T1 -> T2): Prop :=
  is_nonexpansive M.irel N.irel f

def nonexpansive2 [M : IRel T1] [N : IRel T2] [S : IRel T3] (f : T1 -> T2 -> T3): Prop :=
  is_nonexpansive2 M.irel N.irel S.irel f

def nonexpansive3 [M : IRel T1] [N : IRel T2] [S : IRel T3] [U : IRel T4] (f : T1 -> T2 -> T3 -> T4): Prop :=
  is_nonexpansive3 M.irel N.irel S.irel U.irel f

/-- A function between IRels is contractive  -/
def contractive [M : IRel T1] [N : IRel T2] (f : T1 -> T2): Prop :=
  is_contractive M.irel N.irel f

/-- A function between IRels is contractive  -/
def contractive2 [M : IRel T1] [N : IRel T2] [S : IRel T3] (f : T1 -> T2 -> T3): Prop :=
  is_contractive2 M.irel N.irel S.irel f

def anticontractive [M : IRel T1] [N : IRel T2] (f : T1 -> T2): Prop :=
  is_anticontractive M.irel N.irel f

lemma id_nonexpansive [IRel T] : nonexpansive (@id T) := by
  simp [nonexpansive]

lemma cmp_nonexpansive [IRel T] [IRel U] [IRel V] (f : T -> U) (g : U -> V)
    (H1 : nonexpansive f) (H2 : nonexpansive g) :
    nonexpansive (g ∘ f) := by
  simp only [nonexpansive, is_nonexpansive, proper1]
  intros
  apply H2
  apply H1
  trivial





/-- [Semi-bundled] T has an OFE structure -/
class OFE (T : Type) extends ERel T, IRel T where
  equiv : @is_indexed_equiv T IRel.irel
  mono : @is_indexed_mono T IRel.irel
  limit : @is_indexed_refinement T IRel.irel Rel.rel

-- FIXME: Change this name. It's "indexed reflexive" but it looks like "irreflexive"
/-- Lifted property of indexed relation from OFE -/
lemma OFE.irefl [OFE T] {n : ℕ} {x : T} : (x ≈[n] x) :=
  Equivalence.refl (OFE.equiv n) x

/-- Lifted property of indexed relation from OFE -/
lemma OFE.isymm [OFE T] {n : ℕ} {x y : T} : (x ≈[n] y) -> y ≈[n] x :=
  Equivalence.symm (OFE.equiv n)

/-- Lifted property of indexed relation from OFE -/
lemma OFE.itrans [OFE T] {n : ℕ} {x y z : T} : (x ≈[n] y) -> (y ≈[n] z) -> x ≈[n] z :=
  Equivalence.trans (OFE.equiv n)

/-- Lifted property of relation from OFE -/
lemma OFE.refl [OFE T] {x : T} : (x ≈ x) := Equivalence.refl ERel.equivalence x

/-- Lifted property of relation from OFE -/
lemma OFE.symm [OFE T] {x y : T} : (x ≈ y) -> y ≈ x := Equivalence.symm ERel.equivalence

/-- Lifted property of relation from OFE -/
lemma OFE.trans [OFE T] {x y z : T} : (x ≈ y) -> (y ≈ z) -> x ≈ z := Equivalence.trans ERel.equivalence

lemma OFE.dist_le [OFE T] {x y : T} {m n : ℕ} : (x ≈[n] y) -> (m ≤ n) -> (x ≈[m] y) := by
  apply is_indexed_mono_le
  apply OFE.mono

lemma OFE.equiv_proper [OFE T1] [OFE T2] {f : T1 -> T2} (H : nonexpansive f) :
    proper1 Rel.rel Rel.rel f :=
  @is_nonexpansive_refinement_proper T1 T2
    IRel.irel IRel.irel Rel.rel Rel.rel f
    OFE.limit OFE.limit H

/- Lifted iLater properties -/
-- FIXME: Cleanup

lemma OFE.rel_later_iLater [OFE T] (x y : T) : (x ≈[n] y) -> (x ≈L[n] y) := by
  intro H
  apply _root_.rel_later_iLater
  · apply OFE.mono
  · apply H

lemma OFE.iLater_lt_rel [OFE T] (x y : T) (m n : ℕ) :
    m < n -> (x ≈L[n] y) -> x ≈[m] y := by
  intro H1 H2
  apply _root_.iLater_lt_rel
  · apply H1
  · apply H2

lemma OFE.iLater_0 [OFE T] (x y : T) : x ≈L[0] y := by
  apply _root_.iLater_0

lemma OFE.iLater_S [OFE T] {x y : T} {n : ℕ} : (x ≈[n] y) <-> (x ≈L[Nat.succ n] y) := by
  apply _root_.iLater_S
  apply OFE.mono






/-
## Bundled OFE's
-/


-- See Order/Lattice.lean
-- See Order/Hom/Lattice.lean
-- See Order/Category/Lat.lean



-- Step 1: TC Hierarchy of classes
--   See Order/lattice.lean
--   Semi-bundled, hierarchy defined using extension (see Mathematics in Lean)
--   For multiple instances: see Mathlib.Order.Synonym

-- Step 2: Semi-bundled TC hierarchy of morphisms
--   See Order/Hom/Lattice.lean
--   2.1. Define structure (hierarchy) with toFun
--   2.2. Define class (hierarchy) which extends FunLike
--   2.3. Register class instances for each structure
--   2.4. Register CoeTC from F (of class) to structure
--   2.5. Register instance of FunLike for the class
--   2.5. Define comp and id structures

-- Step 3: Bundled structure
--   See Order/Category/Lat.lean
--   3.1. Define bundled type with CategoryTheory.Bundled
--   3.2. Register CoeSort for the bundled type
--   3.3. Register typeclass instance for the bundled type
--   3.4. Define coercion from type to bundled type

-- Step 4: Bundled morphisms
--   See Order/Category/Lat.lean
--   4.1. Register BundledHom instance for @structure
--   4.2. Register Category instance
--   4.3. Register ConcreteCategory instance


-- NOTE: Not sure if this is the best way to organize this
-- FIXME: Can I define Contractive and NonExpansive in a hierachy


/-- [semi-bundled] [2.1] A nonexpansive function between two indexed relations -/
structure NonExpansive (M N : Type) [OFE M] [OFE N] where
  toFun : M -> N
  unif_hom : nonexpansive toFun

attribute [simp] NonExpansive.toFun

-- FIXME: Brackets
notation:30 a1 " -n> "  a2 => NonExpansive a1 a2

/-- [semi-bundled] [2.2] A type F behaves like an irel morphism from M to N at each index  -/
class NonExpansiveClass (F : Type) (M N : outParam Type) [OFE M] [OFE N] extends
     FunLike F M N where
  unif_hom : ∀ f : F, nonexpansive f



-- [2.3]
instance (M N : Type) [OFE M] [OFE N] : FunLike (NonExpansive M N) M N where
  coe := fun F x => F.toFun x
  coe_injective' := by
    intro x y H
    cases x
    congr

-- [2.3]
instance (M N : Type) [OFE M] [OFE N] : NonExpansiveClass (NonExpansive M N) M N where
  unif_hom := by
    simp [DFunLike.coe]
    intro f
    apply f.unif_hom

-- Can lift a function to M -n> N when nonnexpansive holds
instance [OFE M] [OFE N] : CanLift (M -> N) (M -n> N) DFunLike.coe nonexpansive where
  prf := by
    simp [DFunLike.coe]
    intros f H
    exists NonExpansive.mk f H

-- Replace with HasNonExpansive + Coe?
instance [OFE M] [OFE N] [NonExpansiveClass F M N] : CoeOut F (NonExpansive M N) where
  coe F := NonExpansive.mk F (NonExpansiveClass.unif_hom F)


/--
A given function f has a proof of non-expansivity, and therefore can be lifted into NonExpansive

See: laterO.map

NOTE: This class is only used to register coercions
-/
class HasNonExpansive [OFE M] [OFE N] [FunLike F M N] (f : F) where
  ne : nonexpansive f

-- TODO: Is this not somewhere already??
instance : FunLike (A → B) A B where
  coe f := f
  coe_injective' := by simp [Function.Injective]

-- All elemenets of a NonExpansiveClass have a nonexpansive proof
instance [OFE M] [OFE N] [NonExpansiveClass F M N] (f : F) : HasNonExpansive f where
  ne := by apply NonExpansiveClass.unif_hom


-- This is implied by above
-- -- The underlying functions of a bundled NonExpansive have a nonexpansive proof
-- instance [OFE M] [OFE N] (f : M -n> N) : HasNonExpansive f where
--   ne := by apply NonExpansive.unif_hom

-- instance [OFE M] [OFE N] [FunLike F M N] (f : F) : CoeTC (HasNonExpansive f) (NonExpansive M N) where
--   coe _ := NonExpansive.mk f HasNonExpansive.ne

-- instance [OFE M] [OFE N] [FunLike F M N] (f : F) : CoeOut (HasNonExpansive f) (NonExpansive M N) where
--   coe _ := NonExpansive.mk f HasNonExpansive.ne
--
-- section neCoeTest
-- variable [OFE A] [OFE B]
-- variable (f : A -> B)
-- variable [HasNonExpansive f]
--
-- #check f
-- -- #check @CoeTC.coe (HasNonExpansive f) (NonExpansive A B) _ _
-- #check (@CoeOut.coe (HasNonExpansive f) (A -n> B) _ _)
--
-- end neCoeTest

def NonExpansive.lift [OFE M] [OFE N] [FunLike F M N] (f : F) [HasNonExpansive f] : NonExpansive M N where
  toFun := f
  unif_hom := HasNonExpansive.ne






def cid [OFE M] : M -n> M where
  toFun := @_root_.id _
  unif_hom := id_nonexpansive

def cconst [OFE α] [OFE β] (x : β) : α -n> β where
  toFun _ := x
  unif_hom := by
    simp [nonexpansive]
    intros
    apply OFE.irefl

def ccompose [OFE α] [OFE β] [OFE γ] (g : NonExpansive β γ) (f : NonExpansive α β) : NonExpansive α γ where
  toFun := g ∘ f
  unif_hom := by
    simp only [DFunLike.coe]
    apply cmp_nonexpansive
    · apply f.unif_hom
    · apply g.unif_hom


-- It's hom functors or some crap like that
def NonExpansive.map [OFE A] [OFE B] [OFE A'] [OFE B']
    (f : A' -n> A) (g : B -n> B') (x : A -n> B) : (A' -n> B') :=
  ccompose g (ccompose x f)



/-- [bundled] [3.1] Objects in the category of OFE's -/
def OFECat := CategoryTheory.Bundled OFE

-- [3.2]
instance : CoeSort OFECat Type where
  coe := CategoryTheory.Bundled.α

-- [3.3]
instance (X : OFECat) : OFE X := X.str

/-- [3.4] Bundle an OFE instance into an OFECat -/
def OFE.of (T : Type) [OFE T] : OFECat :=
  CategoryTheory.Bundled.of T


-- [4.1]
instance : CategoryTheory.BundledHom @NonExpansive where
  toFun _ _ F := F
  id _ := cid
  comp := @ccompose
  comp_toFun _ _ _ f g := by
    simp only [DFunLike.coe]
    rfl

instance : CategoryTheory.LargeCategory @OFECat :=
  CategoryTheory.BundledHom.category @NonExpansive

instance : CategoryTheory.ConcreteCategory OFECat :=
  CategoryTheory.BundledHom.concreteCategory NonExpansive


















structure Contractive (M N : Type) [OFE M] [OFE N]  where
  toFun : M -> N
  contractive : contractive toFun

attribute [simp] Contractive.toFun

-- FIXME: Brackets
notation:30 a1 " -c> "  a2 => Contractive a1 a2

class ContractiveClass (F : Type) (M N : outParam Type) [OFE M] [OFE N] extends
    FunLike F M N where
  contractive : ∀ f : F, contractive f

instance [OFE M] [OFE N] [ContractiveClass F M N] : NonExpansiveClass F M N where
  unif_hom f := by
    simp [nonexpansive]
    intros
    apply ContractiveClass.contractive
    apply rel_later_iLater
    · apply OFE.mono
    trivial


instance [OFE M] [OFE N] : FunLike (Contractive M N) M N where
  coe F x := F.toFun x
  coe_injective' := by
    intro x _ _
    cases x
    congr

instance [OFE M] [OFE N] : ContractiveClass (Contractive M N) M N where
  contractive f := by
    simp [DFunLike.coe]
    apply f.contractive

-- CanLift instance?

instance [OFE M] [OFE N] [ContractiveClass F M N] : CoeOut F (Contractive M N) where
  coe F := Contractive.mk F (ContractiveClass.contractive F)

class HasContractive [OFE M] [OFE N] [FunLike F M N] (f : F) where
  contr : contractive f

instance [OFE M] [OFE N] [ContractiveClass F M N] (f : F) : HasContractive f where
  contr := by apply ContractiveClass.contractive

-- This is implied by above
-- instance [OFE M] [OFE N] (f : M -n> N) : HasContractive f where
--   ne := by apply ContractiveClass.contractive

instance [OFE M] [OFE N] [FunLike F M N] (f : F) : CoeOut (HasContractive f) (Contractive M N) where
  coe _ := Contractive.mk f HasContractive.contr

def Contractive.lift [OFE M] [OFE N] [FunLike F M N] (f : F) [HasContractive f] : Contractive M N where
  toFun := f
  contractive := HasContractive.contr

lemma Contractive.unif_hom [OFE M] [OFE N ] (f : M -c> N) : nonexpansive f :=
  NonExpansiveClass.unif_hom f




















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
    (Hbase : ∃ x, P x) (Hind : ∀ x, P x -> P (f x)) (Hlim : True) :
    P (fixpoint f) := by
  -- TODO: Limit preservation lemmas
  sorry






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
