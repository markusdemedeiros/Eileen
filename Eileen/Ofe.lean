/-
Authors: Markus de Medeiros
-/

-- import mathlib.CategoryTheory.Category.Basic
import mathlib.Data.FunLike.Basic
-- import mathlib.CategoryTheory.ConcreteCategory.Basic
import mathlib.Order.Basic

-- NOTE / Skipped
--  - Apparently inferring the right OFE is hard for CMRA's and unital CMRA's (ln. 100)
--  - Bundled type
--  + 160

/-- A type with a binary relation -/
abbrev Rel.{u} (T : Type u) := HasEquiv T

abbrev rel (T : Type u) [HasEquiv T] := @HasEquiv.Equiv T

/-- An indexed binary relation (dupe of std) -/
class IRel.{u} (T : Type u) where
  irel : ℕ -> T -> T -> Prop

notation:30 a1 " ≈[ " n " ] "  a2 => IRel.irel n a1 a2

/-- [unbundled] A relation is an equivalence relation  -/
@[simp]
abbrev is_equivalence_relation {T : Type u} (R : T -> T -> Prop) :=
  Equivalence R


/-- [unbundled] A relation is an indexed equivalence relation  -/
@[simp]
def is_indexed_equiv {T : Type u} (R : ℕ -> T -> T -> Prop) : Prop :=
  ∀ n : ℕ, is_equivalence_relation (R n)

/-- [unbundled] ... -/
@[simp]
def is_indexed_mono {T : Type u} (R : ℕ -> T -> T -> Prop) : Prop :=
  ∀ {m n : Nat}, ∀ {x y : T}, m < n -> R m x y -> R n x y -- < or ≤ ?

/-- [unbundled] ... -/
@[simp]
def indexed_refines_eq {T : Type u} (R : ℕ -> T -> T -> Prop) : Prop :=
  ∀ {x y : T}, (∀ n, R n x y) <-> x = y

/-- [semi-bundled] an OFE is an indexed relation that is an equivalence relation at each stpe -/
class OFE (T : Type u) extends (IRel T) where
  equiv : is_indexed_equiv toIRel.irel
  mono : is_indexed_mono toIRel.irel
  limit : indexed_refines_eq toIRel.irel -- In coq it refines an equivalence rather than an equality


/-- [unbundled] ... -/
def is_nonexpansive {M N : Type} [IRel M] [IRel N] (f : M -> N) : Prop :=
  ∀ (n : Nat), ∀ x y, (x ≈[n] y) -> (f x ≈[n] f y)

/-- [semi-bundled] A type F behaves like a relation morphism from M to N at each index  -/
class NonExpansive (F : Type) (M N : outParam Type) [IRel M] [IRel N] extends
     FunLike F M N where
  unif_hom : ∀ f : F, is_nonexpansive f

/-- [unbundled] A map is contractive -/
def is_contractive {M N : Type} [IRel M] [IRel N] (f : M -> N) : Prop :=
  ∀ n, ∀ t t', (∀ m, m < n -> t ≈[m] t') -> (f t) ≈[n] (f t')

/-- [semi-bundled] all elements of F behave like contractive maps -/
class Contractive (F : Type) (M N : outParam Type) [IRel M] [IRel N] extends
      NonExpansive F M N where
    contractive : ∀ f, is_contractive (f : M -> N)

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

instance (T : Type) : DiscreteOFE (Δ T) where
  discrete := by simp [IRel.irel]

instance (T : Type) : OFE (Δ T) where
  equiv := by
    simp [IRel.irel]
    constructor <;> simp
  mono  := by simp [IRel.irel]
  limit := by simp [IRel.irel]


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



def contractive0 {α : Type} (f : α -> α) (O : OFE α) [Inhabited α] (H : is_contractive f) x y :
    f x ≈[ 0 ] f y := by
  apply H
  simp

def contractiveS {α : Type} (f : α -> α) (O : OFE α) [Inhabited α] (H : is_contractive f) x y n :
    (f x ≈[ n ] f y) -> f x ≈[ n + 1 ] f y := by
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
