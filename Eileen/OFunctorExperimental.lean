import Eileen.Ofe


section qOFE

/-! ### Category of OFE's and nonexpansive maps, up to equivalence -/

/-- Two nonexpansive functions send the same element to equivalent elements -/
@[simp]
def qOFECat_hom_equivalent [OFE A] [OFE B] (f g : A -n> B) : Prop :=
  ∀ x : A, f x ≈ g x

@[simp]
def qOFECat_HomRel : HomRel OFECat := fun _ _ f g => qOFECat_hom_equivalent f.hom g.hom

/-- The category of OFE's and functions between them which are free to differ by equivalence -/
abbrev qOFECat := CategoryTheory.Quotient qOFECat_HomRel


instance : CategoryTheory.Congruence qOFECat_HomRel where
  equivalence := by
    intros X Y
    apply Equivalence.mk
    · simp [qOFECat_HomRel]
      intros
      apply refl
    · simp [qOFECat_HomRel]
      intros _ _ H _
      apply symm
      apply H
    · simp [qOFECat_HomRel]
      intros _ _ _ H1 H2 _
      apply _root_.trans
      · apply H1
      · apply H2
  compLeft := by aesop_cat
  compRight f H := by
    simp [qOFECat_HomRel]
    rcases f with ⟨ f, Hf ⟩
    simp [DFunLike.coe]
    intro x
    apply _root_.trans
    · apply OFE.nonexpansive_equiv_equiv_proper Hf
      apply H
    apply refl

-- The CompClosure of qOFECat_HomRel is itself.
lemma qOFECat_HomRel_iff {X Y : OFECat} (f g : X ⟶ Y) :
      CategoryTheory.Quotient.CompClosure qOFECat_HomRel f g ↔ qOFECat_HomRel f g := by
  apply CategoryTheory.Quotient.compClosure_iff_self


-- Functor from OFECat to qOFECat, the canonical way to lift OFE's into qOFE
abbrev qOFECat_functor : CategoryTheory.Functor OFECat qOFECat :=
  CategoryTheory.Quotient.functor qOFECat_HomRel


@[simp]
def qCOFECat_HomRel : HomRel COFECat := fun _ _ f g => qOFECat_hom_equivalent f.hom g.hom

abbrev qCOFECat := CategoryTheory.Quotient qCOFECat_HomRel


instance : CategoryTheory.Congruence qCOFECat_HomRel where
  equivalence := by
    intros X Y
    apply Equivalence.mk
    · simp [qOFECat_HomRel]
      intros
      apply refl
    · simp [qOFECat_HomRel]
      intros _ _ H _
      apply symm
      apply H
    · simp [qOFECat_HomRel]
      intros _ _ _ H1 H2 _
      apply _root_.trans
      · apply H1
      · apply H2
  compLeft := by aesop_cat
  compRight f H := by
    simp [qOFECat_HomRel]
    rcases f with ⟨ f, Hf ⟩
    simp [DFunLike.coe]
    intro x
    apply _root_.trans
    · apply OFE.nonexpansive_equiv_equiv_proper Hf
      apply H
    apply refl

lemma qCOFECat_HomRel_iff {X Y : COFECat} (f g : X ⟶ Y) :
      CategoryTheory.Quotient.CompClosure qCOFECat_HomRel f g ↔ qCOFECat_HomRel f g := by
  apply CategoryTheory.Quotient.compClosure_iff_self

abbrev qCOFECat_functor : CategoryTheory.Functor COFECat qCOFECat :=
  CategoryTheory.Quotient.functor qCOFECat_HomRel

/--
Lift the forgetful COFECat to qOFECat functor to a functor qCOFECat to qOFECat
-/
abbrev qCOFECat_qOFECat_forget : CategoryTheory.Functor qCOFECat qOFECat :=
  @CategoryTheory.Quotient.lift COFECat _ qCOFECat_HomRel qOFECat _ (CategoryTheory.Functor.comp OFECat.toOFE qOFECat_functor)
  (by
    intros
    apply CategoryTheory.Quotient.sound
    congr)



-- #synth CategoryTheory.Category qOFE

end qOFE



section oFunctorCat

/-! ### oFunctors -/

/-- The data of an oFunctor: A bifunctor from (COFEᵒᵖ × COFE) to OFE,
where the functor laws must hold up to equivalence. -/
abbrev oFunctorPre := CategoryTheory.Functor (COFECatᵒᵖ × COFECat) qOFECat

/-- A bifunctor from (COFEᵒᵖ × COFE) to OFE. This is stronger than an
oFunctor because the functor laws must hold up to equality in OFE. -/
abbrev oFunctorPreLeibniz := CategoryTheory.Functor (COFECatᵒᵖ × COFECat) OFECat

/-- This is the thing that we actually want for COFE solver -/
abbrev oFunctorCPre := CategoryTheory.Functor (COFECatᵒᵖ × COFECat) qCOFECat

/-- This is the strongest, it implies the above 3 structures-/
abbrev oFunctorCPreLeibniz := CategoryTheory.Functor (COFECatᵒᵖ × COFECat) COFECat

/-- Every Leibiz oFunctorPre has a canonical oFunctor, obtained by quotienting the
morphisms in its image by equivalence. -/
@[simp, coe]
def oFunctorPre.ofLeibniz (f : oFunctorPreLeibniz) : oFunctorPre :=
  CategoryTheory.Functor.comp f qOFECat_functor

@[simp, coe]
def oFunctorCPre.ofLeibniz (f : oFunctorCPreLeibniz) : oFunctorCPre :=
  CategoryTheory.Functor.comp f qCOFECat_functor


@[simp, coe]
def oFunctorPre.ofoFunctorCPre (f : oFunctorCPre) : oFunctorPre :=
  CategoryTheory.Functor.comp f qCOFECat_qOFECat_forget


-- Define some pre oFunctors

def const_oFunctorPreLeibniz (O : OFECat) : oFunctorPreLeibniz :=
  (CategoryTheory.Functor.const (COFECatᵒᵖ × COFECat)).obj O




-- #check CategoryTheory.Functor.prod

/-
/--
The oFunctor map internalized to products of morphisms
-/
def oFunctor.map_internal (f : oFunctorPre) (A A' B B' : COFECat) :
    prodO (A'.α -n> A.α) (B.α -n> B'.α) -> ((f.obj ⟨Opposite.op A, B⟩).as -n> (f.obj ⟨Opposite.op A', B'⟩).as) :=
  fun x => by
      let Y := CategoryTheory.prod_Hom COFECatᵒᵖ COFECat ⟨ Opposite.op A, B ⟩ ⟨ Opposite.op A', B' ⟩
      simp only [] at Y
      let X := @f.map ⟨ Opposite.op A, B ⟩ ⟨ Opposite.op A', B' ⟩
      rw [Y] at X
      have X' := X ⟨ ?G1, ?G2 ⟩
      case G1 =>
        apply Quiver.Hom.op
        apply COFECat.Hom.mk
        apply x.1
      case G2 =>
        apply COFECat.Hom.mk
        apply x.2
      clear X
      unfold Quiver.Hom at X'
      apply (Quot.lift ?G1 ?G2 X')
      case G1 =>
        intro f'
        apply f'.hom
      case G2 =>
        intro a b H
        apply (qOFECat_HomRel_iff a b).mp at H
        rcases a with ⟨ a', Ha' ⟩
        rcases b with ⟨ b', Hb' ⟩
        simp_all
        funext
        rename_i x
        -- These are not equal as OFE's!

        sorry
-/
/-
-- Ah but these are.
def oFunctor.map_internal' (f : oFunctorPreLeibniz) (A A' B B' : COFECat) :
    prodO (A'.α -n> A.α) (B.α -n> B'.α) -> ((f.obj ⟨Opposite.op A, B⟩) -n> (f.obj ⟨Opposite.op A', B'⟩)) :=
  fun x => by
      let Y := CategoryTheory.prod_Hom COFECatᵒᵖ COFECat ⟨ Opposite.op A, B ⟩ ⟨ Opposite.op A', B' ⟩
      let X := @f.map ⟨ Opposite.op A, B ⟩ ⟨ Opposite.op A', B' ⟩
      rw [Y] at X
      have X' := X ⟨ ?G1, ?G2 ⟩
      case G1 =>
        apply Quiver.Hom.op
        apply COFECat.Hom.mk
        apply x.1
      case G2 =>
        apply COFECat.Hom.mk
        apply x.2
      clear X
      apply X'.hom
-/
-- I wonder how much changes if I define an OFE structure on a type with objects quotiented by equivalence
-- The OFE on that type

class oFunctor (f : oFunctorCPre) where
  internal_nonexpansive : True

class oFunctorContractive (f : oFunctorCPre) extends oFunctor f where
  internal_contractive : True










/-
/-- The data of an oFunctor, namely, a bifunctor from COFECatᵒᵖ × COFECat to
  OFE where the functorial equalities only need to hold up to equivalence ``≈``
  in the target OFE. -/
abbrev oFunctor' := CategoryTheory.Functor (COFECatᵒᵖ × COFECat) qOFECat

-- State and derive the id equivalence
-- State and derive the functoriality equivalence
-- State the nonexpansivity requirement
-- Construct oFunctor as a typeclass
-- State the contractivity requirement
-- Construct oFunctorContractive as a typeclass

-- qOFE equality of morphisms -> OFE equivalence

-- We know that qOFE terms are all Quot.mk wrt. a particular relation

-- qOFECat objects -> OFECat objects
example (X : qOFECat) : OFECat := X.as

-- qOFECat morphisms -> OFECat morphisms

-- These types are all the same:
-- variable (X Y : qOFECat)
-- variable (f : x ⟶ y)
-- variable (f' : CategoryTheory.Quotient.Hom _ X Y)
-- variable (f'' : (Quot (@CategoryTheory.Quotient.CompClosure _ _ qOFECat_HomRel X.as Y.as)))

-- A morphism in qOFECat that is lifted from the identity morphism in OFECat
example (X : OFECat) : (qOFECat_functor.obj X) ⟶ (qOFECat_functor.obj X) :=
  qOFECat_functor.map (CategoryTheory.CategoryStruct.id X)

example (f : oFunctor') (A B : COFECat):
    (f.map ⟨ Quiver.Hom.op ⟨ NonExpansive.cid B ⟩, ⟨ NonExpansive.cid A ⟩ ⟩) =
    CategoryTheory.CategoryStruct.id (f.obj (Opposite.op B, A)) := by
  rw [<- CategoryTheory.Functor.map_id f (Opposite.op B, A)]
  congr



/-
variable (f : oFunctor')
variable (X : COFECatᵒᵖ × COFECat)
variable (Y : COFECatᵒᵖ )
variable (Z : COFECat )
#check f.map_id X
#check f.obj X
#check f.map (CategoryTheory.CategoryStruct.id X) = (CategoryTheory.CategoryStruct.id (f.obj X))

-- Derive qOFE facts: 1: can I prove the oFunctor laws from before?

#check f.map (CategoryTheory.CategoryStruct.id X.1, CategoryTheory.CategoryStruct.id X.2)
-- How do I reflect back out from the category into nonexpansive functions?
-- How do I go from f.map to a function between nonexpansive maps
-- How do I go from a morphism to a nonexpansive map?
#check (CategoryTheory.CategoryStruct.id X)
#check X ⟶ X
#check Quiver.Hom
#check OFECat.hom_id
#check @COFECat.Hom.hom Z Z (CategoryTheory.CategoryStruct.id Z) -- This is how you get the nonexpansive map

#check CategoryTheory.prod_Hom -- Products homs equal a pair of product homs
variable (h1 : X ⟶ X)
#check ((CategoryTheory.prod_Hom _ _ _ X)▸h1)

-- So How do I translate this?
--   Also need hom's for opposite categories and product categories
-- map (NonExpansive.cid _, NonExpansive.cid _) x ≈ NonExpansive.cid _ x



-- #check (X ⟶ X : _ -n> _)


-- All
-- qOFE objects are the same
-- qOFE homs are:
-- def Hom (s t : Quotient r) :=
--   Quot <| @CompClosure C _ r s.as t.as

#check Quot

variable (Q1 Q2 : qOFE)
variable (Qf1 Qf2 : Q1 ⟶ Q2)
variable (Qfh : Qf1 = Qf2)
#check CategoryTheory.Quotient.Hom



-- #check Quot.eq
#check Quot.congr
-- #check Quot.eqvGen_exact
#check Quot.lift
#check Quot.ind
-- #check Quot.sound
#check Quot.lift_mk
-- #check Quot.liftBeta
#check Quot.exists_rep -- Useful


#check Quot.exists_rep Qf1 -- There exists a function which is quotiented into Qf1







-- TODO: Unroll the functor equalities

variable (f : oFunctor')
variable (A B : COFECatᵒᵖ × COFECat)
-- #check A.1.unop.α
-- #synth COFE A.1.unop.α
variable (x : A ⟶ B)
-- #check (f.map x)


-- class oFunctor (F : oFunctor') where

-- An oFunctor is one of these things where the map function is nonexpansive, when viewed
-- as a function into the product space.
-- Figure out a better way to write that requirement (unfold defs).
def test (f : oFunctor') (X Y : COFECatᵒᵖ × COFECat) :
    (prodO (Y.1.unop.α -n> X.1.unop.α) (X.2.α -n> Y.2.α)) -> (emptyO -n> emptyO) :=
  sorry

-- An oFunctorContractive is an oFunctor where that map is actually contractive.

-- A oFunctorCmp is an oFunctor into qCOFE, rather than qOFE.
-- oFunctorCmps can be composed.
-/
-/
end oFunctorCat

-- Maybe use pseudofuntors instead of functors into the quotient category? Idk
