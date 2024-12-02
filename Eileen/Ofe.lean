/-
Authors: Markus de Medeiros
-/

-- import mathlib.CategoryTheory.Category.Basic
import mathlib.CategoryTheory.ConcreteCategory.Basic
import mathlib.Order.Basic


-- NOTE: Right now I'm using a hierarhy of weak structures (HasIndexedEquiv instead of IndexedSetoid).
-- For some reason it works, but if I need stronger properties, everything here can be strengthened.




/-
Before, I trued to unbundle the relation from the classes

I think that bundling it might be a better idea, this is more inline w/ the mathlib design practices
-/

-- -- A relation is like a function from α -> α -> Prop
-- abbrev RelLike (F : Sort*) (α : outParam (Sort*)) := FunLike F α (α -> Prop)
-- abbrev IRelLike (F : Sort*) (α : outParam (Sort*)) := FunLike F ℕ (α -> α -> Prop)

-- /-- A relation obeys the properties of an equivalence relation -/
-- class HasEquivalence {α : Sort u} (r : α → α → Prop) extends (Equivalence r)

-- class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
--     DFunLike F M (fun _ ↦ N) where
--   map_one : ∀ f : F, f 1 = 1
--   map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

abbrev Relation.{u} (T : Type u) : Type u := T -> T -> Prop

abbrev IndexedRelation.{u} (T : Type u) : Type u := Nat -> Relation T

/--
A type has an indexed relation
-/
class HasIndexedEquiv (α : Type) where
  iequiv : IndexedRelation α

attribute [simp] HasIndexedEquiv.iequiv

notation:30 a1 " ≈[ " n " ] "  a2 => HasIndexedEquiv.iequiv n a1 a2

/--
An indexed setoid is an indexed relation, which is an equivalence relation (setoid) at every index.
-/
class IndexedSetoid (α : Type) extends (HasIndexedEquiv α) where
  iseqv : ∀ n, Equivalence (iequiv n)

instance (n : Nat) [IndexedSetoid α] : Setoid α where
  r := HasIndexedEquiv.iequiv n
  iseqv := IndexedSetoid.iseqv n

/--
An OFE is an indexed setoid which satsifies the monotonicity and limit properties.
-/
class OFE (T : Type) extends IndexedSetoid T where
  mono : ∀ {m n : Nat}, ∀ {x y : T}, m ≤ n -> (x ≈[m] y) -> (x ≈[n] y)
  limit : ∀ {x y : T}, (∀ n, x ≈[n] y) <-> x = y


/-- A type F behaves like a relation morphism from M to N, where M and M have binary relations -/
class EquivHom (F : Type) (M N : outParam Type) [HasEquiv M] [HasEquiv N] extends
     FunLike F M N where
  hom : ∀ f : F, ∀ x y, (x ≈ y) -> (f x ≈ f y)

/-- A type F behaves like a relation morphism from M to N at each index  -/
class IndexedEquivHom (F : Type) (M N : outParam Type) [HasIndexedEquiv M] [HasIndexedEquiv N] extends
     FunLike F M N where
  unif_hom : ∀ f : F, ∀ {n : Nat}, ∀ x y, (x ≈[n] y) -> (f x ≈[n] f y)

abbrev NonExpansive (F : Type) (M N : Type) [HasIndexedEquiv M] [HasIndexedEquiv N] :=
  IndexedEquivHom F M N

/--
A map is contractive
-/
def is_contractive {M N : Type} [HasIndexedEquiv M] [HasIndexedEquiv N] (f : M -> N) : Prop :=
  ∀ n, ∀ t t', (∀ m, m < n -> t ≈[m] t') -> (f t) ≈[n] (f t')

/--
F is a type that behaves like a contractive map from M to N
-/
class ContractiveEquivHom {M N : Type} (F : Type) [HasIndexedEquiv M] [HasIndexedEquiv N] extends IndexedEquivHom F M N where
    contractive : ∀ f : F, is_contractive f






/-- An element in an indexed relation is discrete -/
@[simp]
def is_discrete [HasIndexedEquiv T] (e : T) : Prop := ∀ y, (e ≈[0] y) -> e = y

/-- A discrete OFE is an OFE where all elements are discrete -/
class DiscreteOFE (T : Type) extends HasIndexedEquiv T where
  discrete : ∀ (x : T), is_discrete x

/-
/-- The discrete OFE over a type -/
@[simp]
def discreteO (T : Type) : IndexedRelation T := fun _ => Eq
prefix:max  "Δ"   => discreteO

instance discrete_iequiv : HasIndexedEquiv T where
  iequiv := discreteO T

instance discreteO_equivalence (T : Type) (n : Nat) : Equivalence (Δ T n) where
  refl  := by simp
  trans := by simp
  symm  := by simp

instance discreteO_indexedsetoid (T : Type) : IndexedSetoid T where
  iseqv := discreteO_equivalence T

instance discreteO_ofe (T : Type) : OFE T where
  mono  := by simp
  limit := by simp

instance discreteO_discrete_ofe (T : Type) : DiscreteOFE T where
  discrete := by simp
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




/--
OFE structure on nonexpansive types
-/
@[simp]
def nonexpansiveO {M N : Type} (F : Type) [HasIndexedEquiv M] [HasIndexedEquiv N] [NonExpansive F M N] : IndexedRelation F :=
  fun n f g => ∀ x : M, f x ≈[n] g x

instance nonexpansiveO_equivalence (n : Nat) [HasIndexedEquiv M] [HasIndexedEquiv N] [NonExpansive F M N] :
    Equivalence (nonexpansiveO F n) where
  refl  := by
    simp
    sorry
  trans := by
    simp
    intro _ _ _ Hx Hy _
    -- simp [Hx, Hy]
    sorry
  symm  := by
    simp
    intro _ _ H _
    -- simp [H]
    sorry

instance nonexpansiveO_hasindexedequiv [HasIndexedEquiv M] [HasIndexedEquiv N] [NonExpansive F M N] : HasIndexedEquiv F where
  iequiv := nonexpansiveO F

instance nonexpansiveO_indexedsetoid [HasIndexedEquiv M] [HasIndexedEquiv N] [NonExpansive F M N] : IndexedSetoid F where
  iseqv n := nonexpansiveO_equivalence n

instance nonexpansiveO_ofe [HasIndexedEquiv M] [HasIndexedEquiv N] [NonExpansive F M N] : OFE F where
  mono  := by
    simp
    sorry
  limit := by
    simp
    -- exact Iff.symm DFunLike.ext_iff
    sorry



/--
The type of step-indexed propositions
-/
abbrev SProp := { sp : Nat -> Prop // ∀ n m : Nat, n ≥ m -> sp n -> sp m }

@[simp]
def SProp_imp (n : Nat) (sp0 sp1 : SProp) : Prop :=  ∀ m, m ≤ n -> (sp0.1 m -> sp1.1 m)

@[simp]
def SPropO : IndexedRelation SProp := fun n sp0 sp1 => ∀ m, m ≤ n -> (sp0.1 m <-> sp1.1 m)

instance SPropO_equivalence (n : Nat) : Equivalence (SPropO n) where
  refl  := by simp
  trans := by
    intros x y z
    cases x
    cases y
    cases z
    simp_all
  symm  := by
    intros x y
    cases x
    cases y
    simp_all

instance SPropO_iequiv : HasIndexedEquiv SProp where
  iequiv := SPropO

instance SPropO_indexedsetoid : IndexedSetoid SProp where
  iseqv n := SPropO_equivalence n

/-
instance SPropO_OFE : OFE SProp where
  mono  := by
    intros m n x y Hmn S0
    simp_all only [HasIndexedEquiv.iequiv]
    intro m' m'n
    rcases x with ⟨ p1, Hp1 ⟩
    rcases y with ⟨ p2, Hp2 ⟩
    simp_all
    apply Iff.intro
    · sorry
      -- what
    · intro Hp2'
      simp_all
      sorry
  limit := by
    simp
    sorry
-/


/--
c satisfies the chain property
-/
@[simp]
def is_chain {α : Type} [HasIndexedEquiv α] (c : Nat -> α) : Prop :=
  ∀ {m n : Nat}, n ≤ m -> (c m) ≈[n] (c n)

/--
The type of functions which satisfy the chain property
-/
abbrev Chain (α : Type) [HasIndexedEquiv α] := { c : Nat -> α // is_chain c }

class COFE (α : Type) extends OFE α where
  lim : Chain α -> α
  complete : ∀ {n : Nat}, ∀ {c : Chain α}, (lim c) ≈[n] (c.1 n)



def fixpoint_chain {α : Type} (f : α -> α) [OFE α] [Inhabited α] (H : is_contractive f) : Chain α :=
  ⟨ fun n => Nat.repeat f n default,
    by
      simp only [is_chain, HasIndexedEquiv.iequiv]
      intro n
      induction n
      · simp


        sorry
      -- rename_i n IH
      -- intro n' Hn'
      -- cases (Nat.eq_or_lt_of_le Hn')
      -- · simp_all
      -- rename_i h'
      -- rw [<- IH (Nat.le_of_lt_succ h')]
      sorry
      ⟩




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
