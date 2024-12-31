/-
Authors: Markus de Medeiros
-/

-- import mathlib.CategoryTheory.Category.Basic
import mathlib.Data.FunLike.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
-- import mathlib.CategoryTheory.ConcreteCategory.Basic
import mathlib.Order.Basic


-- NOTE / Skipped
--  - Apparently inferring the right OFE is hard for CMRA's and unital CMRA's (ln. 100)
--  - Bundled type
--  + 160


/--
A proper map wrt. two relations
FIXME: Move if right
-/
@[simp]
def is_proper_1 {T1 T2 : Type} (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (f : T1 -> T2) : Prop :=
  ∀ {x y : T1}, R1 x y -> R2 (f x) (f y)

/--
A proper map wrt. three relations
FIXME: Move if right
-/
@[simp]
def is_proper_2 {T1 T2 T3 : Type} (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (R3 : T3 -> T3 -> Prop) (f : T1 -> T2 -> T3) : Prop :=
  ∀ {x y : T1} {z w : T2}, R1 x y -> R2 z w -> R3 (f x z) (f y w)


/-
# Basic props
-/


/-- [unbundled] A relation is an equivalence relation  -/
@[simp]
abbrev is_equiv_rel {T : Type u} (R : T -> T -> Prop) :=
  Equivalence R

/-- [unbundled] An indexed relation is an indexed equivalence relation  -/
@[simp]
def is_indexed_equiv {T : Type u} (R : ℕ -> T -> T -> Prop) : Prop :=
  ∀ n : ℕ, is_equiv_rel (R n)

/-- [unbundled] the indexed relation is down-closed -/
@[simp]
def is_indexed_mono {T : Type u} (R : ℕ -> T -> T -> Prop) : Prop :=
  ∀ {m n : Nat}, ∀ {x y : T}, m < n -> R n x y -> R m x y

/-- [unbundled] the indexed relation R refines the relation R' -/
@[simp]
def is_indexed_refinement {T : Type u} (R : ℕ -> T -> T -> Prop) (R' : T -> T -> Prop) : Prop :=
  ∀ {x y : T}, (∀ n, R n x y) <-> R' x y

/-- [unbundled] R forms an OFE with respect to R' -/
@[simp]
def is_ofe {T : Type u} (R : ℕ -> T -> T -> Prop) (R' : T -> T -> Prop) : Prop :=
  is_indexed_equiv R ∧
  is_indexed_mono R ∧
  is_indexed_refinement R R'

/-- A relation that is one later than R -/
def ilater {T : Type} (R : ℕ -> T -> T -> Prop) (n : ℕ) (x y : T) : Prop :=
  ∀ m, m < n -> R m x y

/-- [unbundled] A function is nonexpansive wrt. two indexed equivalences -/
def is_nonexpansive {M N : Type} (RM : ℕ -> M -> M -> Prop) (RN : ℕ -> N -> N -> Prop) (f : M -> N) : Prop :=
  ∀ (n : Nat), is_proper_1 (RM n) (RN n) f

/-- [unbundled] A function is contractive wrt. two indexed equivalences -/
def is_contractive {M N : Type} (RM : ℕ -> M -> M -> Prop) (RN : ℕ -> N -> N -> Prop) (f : M -> N) : Prop :=
  ∀ (n : Nat), is_proper_1 ((ilater RM) n) (RN n) f





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
class ERel (T : Type u) extends Rel T where
  equivalence : Equivalence (@Rel.rel T _)


/--
An indexed binary relation
Note: duplicate  of std.
-/
class IRel.{u} (T : Type u) where
  /-- The indexed binary operation on a type -/
  irel : ℕ -> T -> T -> Prop

attribute [simp] IRel.irel

notation:30 a1 " ≈[ " n " ] "  a2 => IRel.irel n a1 a2

/-- A function between IRels is nonexpansive -/
def nonexpansive [M : IRel T1] [N : IRel T2] (f : T1 -> T2): Prop :=
  is_nonexpansive M.irel N.irel f

/-- A function between IRels is contractive  -/
def contractive [M : IRel T1] [N : IRel T2] (f : T1 -> T2): Prop :=
  is_contractive M.irel N.irel f

/-- [Semi-bundled] T has an OFE structure -/
class OFE (T : Type u) extends ERel T, IRel T where
  equiv : @is_indexed_equiv T IRel.irel
  mono : @is_indexed_mono T IRel.irel
  limit : @is_indexed_refinement T IRel.irel Rel.rel

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











-- FIXME: Can I define Contractive and NonExpansive in a hierachy somehow?
-- see MulHom
-- see SemiRingCat.Hom

class NonExpansive (M N : Type) [IRel M] [IRel N] where
  toFun : M -> N
  unif_hom : nonexpansive toFun
notation:30 t1 " ==ne=> "  t2 => NonExpansive t1 t2

attribute [simp] NonExpansive.toFun

/-- [semi-bundled] A type F behaves like an irel morphism from M to N at each index  -/
class NonExpansiveClass (F : Type) (M N : outParam Type) [IRel M] [IRel N] extends
     FunLike F M N where
  unif_hom : ∀ f : F, nonexpansive f

instance (M N : Type) [IRel M] [IRel N] : FunLike (NonExpansive M N) M N where
  coe := fun F x => F.toFun x
  coe_injective' := by
    intro x y H
    cases x
    congr

instance (M N : Type) [IRel M] [IRel N] : NonExpansiveClass (NonExpansive M N) M N where
  unif_hom := by
    simp [DFunLike.coe]
    intro f
    apply f.unif_hom


def NonExpansiveClass.toNonExpansive [IRel M] [IRel N] [FunLike F M N] [NonExpansiveClass F M N] (f : F) :
    NonExpansive M N where
  toFun := sorry
  unif_hom := sorry

instance [IRel M] [IRel N] [FunLike F M N] [NonExpansiveClass F M N] (f : F) :
    CoeTC F (NonExpansive M N)  where
  coe := sorry

/-- [bundled] OFE -/
abbrev OFECat := CategoryTheory.Bundled OFE

instance : CoeSort OFECat (Type u) where
  coe := CategoryTheory.Bundled.α

-- @[reducible, inline]
@[inline]
abbrev OFECat.of (T : Type) [OFE T] : OFECat := { α := T, str := by infer_instance }

instance (A : OFECat) : OFE A where
  rel := sorry
  irel := sorry
  equivalence := sorry
  equiv := sorry
  mono := sorry
  limit := sorry

lemma OFECat.coe_of (T : Type) [OFE T] : OFECat.of T = T :=
  sorry

lemma OFECat.of_carrier (T : OFECat) : OFECat.of T = T :=
  sorry

structure OFECat.Hom (A : OFECat) (B : OFECat) where
  hom : NonExpansive A B

-- instance OFECat.instCategory : CategoryTheory.Category OFECat where








class Contractive (M N : Type) [IRel M] [IRel N]  where
  toFun : M -> N
  contractive : contractive toFun

class ContractiveClass (F : Type) (M N : outParam Type) [IRel M] [IRel N] extends
    FunLike F M N where
  contractive : ∀ f : F, contractive f

instance (M N : Type) [IRel M] [IRel N] : FunLike (Contractive M N) M N where
  coe := sorry
  coe_injective' := sorry

instance (M N : Type) [IRel M] [IRel N] : ContractiveClass (Contractive M N) M N where
  contractive := sorry










/-- [unbundled] An element in an indexed relation is discrete -/
@[simp]
def is_discrete [IRel T] (e : T) : Prop := ∀ y, (e ≈[0] y) -> e = y

/-- [semi-bundled] A discrete OFE is an OFE where all elements are discrete -/
class DiscreteOFE (T : Type) extends IRel T where
  discrete : ∀ (x : T), is_discrete x

/-- A wrapper around a type to treat it as if it's in the discrete OFE -/
structure discreteO (T : Type u) : Type u where
  t : T

prefix:max  "Δ"  => discreteO

instance (T : Type*) : Coe (Δ T) T where
  coe := discreteO.t

instance (T : Type*) : IRel (Δ T) where
  irel _ := Eq

instance (T : Type*) : Rel (Δ T) where
  rel := Eq

instance (T : Type*) : ERel (Δ T) where
  equivalence := sorry

instance (T : Type) : DiscreteOFE (Δ T) where
  discrete := by simp [IRel.irel]

instance (T : Type) : OFE (Δ T) where
  equiv := by
    simp [IRel.irel]
    constructor <;> simp
  mono  := by simp [IRel.irel]
  limit := by simp [IRel.irel]







/-

/-- A term which behaves like a map which is nonexpansive -/
@[ext]
structure nonexpansiveO (F M N : Type) [IRel M] [IRel N] [FunLike F M N] : Type where
  f : F
  is_nonexpansive : is_nonexpansive f

instance (F M N : Type) [IRel M] [IRel N] [FunLike F M N] : FunLike (nonexpansiveO F M N) M N where
  coe e := e.f
  coe_injective' _ _ := by
    simp [DFunLike.coe]
    exact nonexpansiveO.ext

-- notation:80  a:81 " -n> " b:79 => @nonexpansiveO a b (a -> b)

-- All values in type (nonexpansiveO F M N) behave like nonexpansive maps from M to N
instance (M N : outParam Type) (F : Type) [IRel M] [IRel N] [FunLike F M N]  :
    @NonExpansive (nonexpansiveO F M N) M N _ _ where
  unif_hom f := by
    rcases f
    simp [DFunLike.coe]
    trivial

-- You give me: a value in a type you've proven to consist of nonexpansive maps
-- I give you: a value of type nonexpansiveO
def nonexpansiveO.of (F M N : Type) [IRel M] [IRel N] [f : NonExpansive F M N] (f : F) : nonexpansiveO F M N where
  f := f
  is_nonexpansive := by apply @NonExpansive.unif_hom

instance [IRel M] [IRel N] [FunLike F M N] : IRel (nonexpansiveO F M N) where
  irel n f g := ∀ x : M, f x ≈[n] g x

-- This proof doesn't use the OFE property??? Works for a more general structure?
instance [OFE M] [OFE N] [FunLike F M N] : OFE (nonexpansiveO F M N) where
  equiv := by
    simp
    intro n
    rcases (@OFE.equiv N _ n) with ⟨ ENR, ENS, ENT ⟩
    simp_all [IRel.irel]
    constructor
    · intro _ _
      apply ENR
    · intro _ _ H1 _
      apply ENS
      apply H1
    · intro _ _ _ H1 H2 _
      apply ENT
      · apply H1
      · apply H2
  mono  := by
    simp [IRel.irel]
    intro n m f g Hmn H x
    apply (@OFE.mono N _ n m (f x) (g x) Hmn)
    apply H
  limit := by
    have X1 := (@OFE.limit N _ )
    have X2 := (@OFE.limit M _ )
    simp_all [IRel.irel]
    intro f g
    apply Iff.intro
    · intro H
      apply nonexpansiveO.ext
      apply DFunLike.ext
      intro m
      apply (@X1 (f.f m) (g.f m)).mp
      intro n
      apply H
    · intro H n x
      subst H
      rcases (@OFE.equiv N _ n) with ⟨ ENR, _, _⟩
      apply ENR




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



/-- [unbundled] c satisfies the chain property -/
@[simp]
def chain_is_cauchy {α : Type*} [IRel α] (c : Nat -> α) : Prop :=
  ∀ {m n : Nat}, n ≤ m -> (c m) ≈[n] (c n)

/-- The type of functions which satisfy the chain property -/
abbrev Chain (α : Type*) [IRel α] := { c : Nat -> α // chain_is_cauchy c }

instance (α : Type*) [IRel α] : CoeFun (Chain α) (fun _ => (Nat -> α)) where
  coe s := s.1

def Chain.map {α β : Type} [IRel α] [IRel β] (f : α -> β) (c : Chain α) (Hf : is_nonexpansive f) : Chain β where
  val := f ∘ c
  property := by
    rcases c with ⟨ c', Hc' ⟩
    simp [chain_is_cauchy, DFunLike.coe ]
    intros m n Hnm
    simp at Hc'
    apply Hf
    apply Hc'
    apply Hnm

class COFE (α : Type) extends OFE α where
  lim : Chain α -> α
  complete : ∀ {n : Nat}, ∀ (c : Chain α), (lim c) ≈[n] (c n)

lemma COFE.map {α β : Type} [COFEα: COFE α] [COFEβ : COFE β] (f : α -> β) (c : Chain α) (Hf : is_nonexpansive f) :
    lim (Chain.map f c Hf) = f (lim c) := by -- Iris: Equiv
  apply OFE.limit.mp
  intro n
  apply @(@COFEβ.equiv n).trans _ _ _ _ ?G
  case G =>
    apply Hf
    apply (@COFEα.equiv n).symm
    apply @COFEα.complete
  apply @(@COFEβ.equiv n).trans _ _ _ ?G
  case G =>
    apply @COFEβ.complete
  unfold Chain.map
  simp
  apply @(@COFEβ.equiv n).refl


def contractive0 {α β: Type} (f : α -> β) [OFEα : OFE α] [OFE β] [Inhabited α] (H : is_contractive f) x y :
    f x ≈[ 0 ] f y := by
  apply H
  simp

def contractiveS {α β : Type} (f : α -> β) [OFEα : OFE α] [OFE β] [Inhabited α] (H : is_contractive f) x y n :
    (x ≈[ n ] y) -> f x ≈[ n + 1 ] f y := by
  intro H1
  apply H
  intro m Hnm
  -- have X := @OFEα.mono m
  sorry





-- def fixpoint_chain {α : Type} (f : α -> α) (O : OFE α) [Inhabited α] (H : is_contractive f) : Chain α :=
--   ⟨ fun n => Nat.repeat f (n + 1) default,
--     by
--       simp only [is_chain, IRel.irel]
--       intro n
--       induction n
--       · simp
--         sorry
--       rename_i n IH
--       intro n' Hn'
--
--       cases (Nat.eq_or_lt_of_le Hn')
--       · simp_all
--         sorry
--       rename_i h'
--       -- have IH' := @IH n' (Nat.le_of_lt_succ h')
--       unfold is_contractive at H
--       simp [Nat.repeat]
--
--       -- have H'' := H n' (Nat.repeat f (n + 1) default ) (Nat.repeat f n' default) ?G1
--       -- case G1 =>
--       --   intro m Hmn'
--       --   sorry
--       sorry ⟩
















/-
-- Typeclass which mimics Order hierarchy

-- Type which specifies an OFE, and higher instance priority for specified OFE's (lower for trivial OFE's)?

-- Category: Like in Order/Cateogry/Lat.lean

-- Use Type* instead of type








-- Program Definition fixpoint_chain {A : ofe} `{Inhabited A} (f : A → A)
--   `{!Contractive f} : chain A := {| chain_car i := Nat.iter (S i) f inhabitant |}.




/-

/-- An IndexedEquivalence is an IndexedRelation, which is an equivalence at each index -/
class IndexedEquivalence (R : IndexedRelation T) where
  equiv : ∀ n, Equivalence (R n)

instance (R : IndexedRelation T) (n : Nat) [IndexedEquivalence R] : Equivalence (R n) where
  refl := (IndexedEquivalence.equiv n).refl
  trans := (IndexedEquivalence.equiv n).trans
  symm := (IndexedEquivalence.equiv n).symm

/-- Semi-bundled representation of an OFE -/
class OFE {T : Type} (R : IndexedRelation T) extends IndexedEquivalence R where
  mono  : ∀ {m n x y}, m ≤ n -> R m x y -> R n x y
  limit : ∀ {x y}, (∀ n, R n x y) <-> x = y



/-
## The category of equivalence relations
-/


-- class EquivHomClass (F : Type) {T S : outParam Type} (R : outParam (Relation T)) (R' : outParam (Relation T)) where


/-- A function is a homomorphism of equivalence relations -/
@[simp]
def is_EquivHom {T S} (R : Relation T) (R' : Relation S) (f : T -> S) : Prop :=
  ∀ t t' : T, R t t' -> R' (f t) (f t')

class EquivHom {T S} (R : Relation T) (R' : Relation S) (f : T -> S) where
  hom : is_EquivHom R R' f

class NonExpansive (R : IndexedRelation T) (R' : IndexedRelation S) (f : T -> S) where
  nonexpansive : ∀ n, EquivHom (R n) (R' n) f

@[simp]
def is_contractive (R : IndexedRelation T) (R' : IndexedRelation S) (f : T -> S) : Prop :=
  ∀ n, ∀ t t', (∀ m, m < n -> R m t t') -> R' n (f t) (f t')

class Contractive (R : IndexedRelation T) (R' : IndexedRelation S) (f : T -> S) extends NonExpansive R R' f where
  contractive : is_contractive R R' f


-- How does mathlib deal w/ exponentials

-- def nonexpansiveO (R : IndexedRelation T) (R' : IndexedRelation S) (f : T -> S)







/-

-- Bundling: If we wanted to work in the cateogry itself


abbrev EquivHom.{u} {T S : Type u} (R : Relation T) (R' : Relation S) : Type u :=
  { f : T -> S // is_EquivHom R R' f }

-- Already implemented
-- instance {T S : Type} (R : Relation T) (R' : Relation S) : CoeOut (EquivHom R R') (T -> S) where
--   coe h := h.1

def is_EquivHom_id_refl : is_EquivHom R R id := by
  simp

def is_EquivHom_comp : is_EquivHom R R' f -> is_EquivHom R' R'' g -> is_EquivHom R R'' (g ∘ f) := by
  simp_all

def EquivHom_id : EquivHom R R :=
  ⟨ _, is_EquivHom_id_refl ⟩

def EquivHom_comp (h0 : EquivHom R R') (h1 : EquivHom R' R'') : EquivHom R R'' :=
  ⟨ _,  is_EquivHom_comp h0.2 h1.2 ⟩

-/
-/
-/

/-

-- An object in the category of OFE's
-- FIXME: Use the actual ConcreteCategory machinery
structure OFECat : Type 2 where
  α : Type
  -- I could still unbundle R here
  ofe : OFE α := by infer_instance

structure OFEHom : Type 2 where
  α : Type
  β : Type
  F : Type
  f : F
  hom : NonExpansive α β F := by infer_instance

-/
-/
