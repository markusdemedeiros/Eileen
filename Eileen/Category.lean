import Eileen.Ofe
import Eileen.Cmra
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.Data.FunLike.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Quotient


instance : CategoryTheory.BundledHom @NonExpansive where
  toFun _ _ F := F
  id _ := NonExpansive.cid _
  comp := @NonExpansive.ccompose
  comp_toFun _ _ _ f g := by
    simp only [DFunLike.coe]
    rfl


section OFEBundled
/-! ### The category of OFE's plus NonExpansive maps -/

/-- Objects in the category of OFE's -/
def OFECat := CategoryTheory.Bundled OFE

-- Coercion between objects in the category of OFE's and Type (their type)
instance : CoeSort OFECat Type where
  coe := CategoryTheory.Bundled.α

attribute [coe] CategoryTheory.Bundled.α

attribute [instance] CategoryTheory.Bundled.str

namespace OFECat

abbrev of (T : Type) [OFE T] : OFECat where
  α := T

lemma coe_of (T : Type) [OFE T] : (of T : Type) = T := by rfl

lemma of_carrier (O : OFECat) : of O = O := by rfl

variable {R} in
/-- Morphisms in the category of OFE's -/
@[ext]
structure Hom (R S : OFECat) where
  private mk::
  hom : R -n> S

/-- The category of OFEs and nonexpansive functions -/
instance : CategoryTheory.Category OFECat where
  Hom R S := OFECat.Hom R S
  id R := ⟨ NonExpansive.cid R ⟩
  comp F G := ⟨ G.hom.ccompose F.hom ⟩

/-- Morphisms of the OFE category behave like functions -/
instance {R S : OFECat} : CoeFun (R ⟶ S) (fun _ ↦ R → S) where
  coe f := f.hom

@[simp]
lemma hom_id {R : OFECat} : (CategoryTheory.CategoryStruct.id R : R ⟶ R).hom = NonExpansive.cid R := rfl

lemma id_apply (R : OFECat) (r : R) :
    (CategoryTheory.CategoryStruct.id  R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : OFECat} (f : R ⟶ S) (g : S ⟶ T) :
    (CategoryTheory.CategoryStruct.comp f g).hom = g.hom.ccompose f.hom := rfl

lemma comp_apply {R S T : OFECat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (CategoryTheory.CategoryStruct.comp f g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : OFECat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/-- Typecheck a nonexpansive function as a morphism in OFE  -/
abbrev ofHom {R S : Type} [OFE R] [OFE S] (f : R -n> S) : OFECat.of R ⟶ OFECat.of S :=
  ⟨f⟩

lemma hom_ofHom {R S : Type} [OFE R] [OFE S] (f : R -n> S) :
  (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : OFECat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type} [OFE R] : ofHom (NonExpansive.cid R) = CategoryTheory.CategoryStruct.id (OFECat.of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type} [OFE R] [OFE S] [OFE T]
    (f : R -n> S) (g : S -n> T) :
    ofHom (g.ccompose f) = CategoryTheory.CategoryStruct.comp (ofHom f) (ofHom g) :=
  rfl

lemma ofHom_apply {R S : Type} [OFE R] [OFE S]
    (f : R -n> S) (r : R) : ofHom f r = f r := rfl

instance : CategoryTheory.ConcreteCategory OFECat where
  -- Functor from OFECat to Type
  forget :=
    { obj R := R
      map f x := (f.hom) x }
  forget_faithful :=
    -- TODO: Simplify me
    ⟨fun h => by
      rename_i f g
      rcases f
      rcases g
      ext
      simp_all [DFunLike.coe] ⟩

instance : CategoryTheory.LargeCategory OFECat where

lemma forget_obj {R : OFECat} : CategoryTheory.ConcreteCategory.forget.obj R = R := by
  rfl

-- lemma forget_map {R S : OFECat} (f : R ⟶ S) :
--     CategoryTheory.ConcreteCategory.forget.map f = f := by
--   rfl
--
-- instance {R : OFECat} : OFE (CategoryTheory.ConcreteCategory.forget.obj R) :=
--   (inferInstance : OFE R.carrier)

end OFECat

-- -- TODO: Coercion?
-- def OFECat.ofHom [OFE A] [OFE B] (f : A -> B) [H : HasNonExpansive f] : Quiver.Hom A B :=
--   sorry
--   -- NonExpansive.mk f (H.is_nonexpansive)

end OFEBundled




section COFEBundled
/-! ### The category of COFE's with nonexpansive functions -/
/-- -/
def COFECat := CategoryTheory.Bundled COFE


-- Coercion between objects in the category of OFE's and Type (their type)
instance : CoeSort COFECat Type where
  coe := CategoryTheory.Bundled.α

attribute [coe] CategoryTheory.Bundled.α

attribute [instance] CategoryTheory.Bundled.str




namespace COFECat

abbrev of (T : Type) [COFE T] : COFECat where
  α := T

lemma coe_of (T : Type) [COFE T] : (of T : Type) = T := by rfl

lemma of_carrier (O : COFECat) : of O = O := by rfl

variable {R} in
/-- Morphisms in the category of COFE's -/
@[ext]
structure Hom (R S : COFECat) where
  private mk::
  hom : R -n> S

/-- The category of OFEs and nonexpansive functions -/
instance : CategoryTheory.Category COFECat where
  Hom R S := COFECat.Hom R S
  id R := ⟨ NonExpansive.cid R ⟩
  comp F G := ⟨ G.hom.ccompose F.hom ⟩

/-- Morphisms of the OFE category behave like functions -/
instance {R S : COFECat} : CoeFun (R ⟶ S) (fun _ ↦ R → S) where
  coe f := f.hom

@[simp]
lemma hom_id {R : COFECat} : (CategoryTheory.CategoryStruct.id R : R ⟶ R).hom = NonExpansive.cid R := rfl

lemma id_apply (R : COFECat) (r : R) :
    (CategoryTheory.CategoryStruct.id  R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : COFECat} (f : R ⟶ S) (g : S ⟶ T) :
    (CategoryTheory.CategoryStruct.comp f g).hom = g.hom.ccompose f.hom := rfl

lemma comp_apply {R S T : COFECat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (CategoryTheory.CategoryStruct.comp f g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : COFECat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/-- Typecheck a nonexpansive function as a morphism in OFE  -/
abbrev ofHom {R S : Type} [COFE R] [COFE S] (f : R -n> S) : COFECat.of R ⟶ COFECat.of S :=
  ⟨f⟩

lemma hom_ofHom {R S : Type} [COFE R] [COFE S] (f : R -n> S) :
  (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : COFECat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type} [COFE R] : ofHom (NonExpansive.cid R) = CategoryTheory.CategoryStruct.id (COFECat.of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type} [COFE R] [COFE S] [COFE T]
    (f : R -n> S) (g : S -n> T) :
    ofHom (g.ccompose f) = CategoryTheory.CategoryStruct.comp (ofHom f) (ofHom g) :=
  rfl

lemma ofHom_apply {R S : Type} [COFE R] [COFE S]
    (f : R -n> S) (r : R) : ofHom f r = f r := rfl

instance : CategoryTheory.ConcreteCategory COFECat where
  -- Functor from OFECat to Type
  forget :=
    { obj R := R
      map f x := (f.hom) x }
  forget_faithful :=
    -- TODO: Simplify me
    ⟨fun h => by
      rename_i f g
      rcases f
      rcases g
      ext
      simp_all [DFunLike.coe] ⟩

instance : CategoryTheory.LargeCategory COFECat where

lemma forget_obj {R : COFECat} : CategoryTheory.ConcreteCategory.forget.obj R = R := by
  rfl

instance {R : OFECat} : OFE (CategoryTheory.ConcreteCategory.forget.obj R) :=
  (inferInstance : OFE R.α)

-- lemma forget_map {R S : OFECat} (f : R ⟶ S) :
--     CategoryTheory.ConcreteCategory.forget.map f = f := by
--   rfl


end COFECat
end COFEBundled

def OFECat.toOFE : CategoryTheory.Functor COFECat OFECat where
  obj X := ⟨ X.1, by infer_instance ⟩
  map f := ⟨ f,
             by
               rcases f with ⟨ f, H ⟩
               apply H ⟩







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





section OFECatCCC

/-! ### (Experiment) Define oFunctors using mathlib's existing categorical definitions

This section mimics the pattern in Mathlib/CategoryTheory/ChosenFiniteProducts/Cat.lean
since the construction is very similar.
-/

-- TODO: There should be a way to lift morphisms
def OFECat.Fst (C D : OFECat) : (Quiver.Hom (OFECat.of (C × D)) C) :=
  -- OFECat.ofHom Prod.fst -- TODO: Need to fix coercions for the inference from HasNonExpansive to work, probably?
  OFECat.ofHom <| NonExpansive.mk Prod.fst fst_nonexpansive

def OFECat.Snd (C D : OFECat) : (Quiver.Hom (OFECat.of (C × D)) D) :=
  OFECat.ofHom <| NonExpansive.mk Prod.snd snd_nonexpansive

def OFEProdCone (C D : OFECat) : CategoryTheory.Limits.BinaryFan C D :=
  .mk (P := .of (C × D))
    (OFECat.Fst C D)
    (OFECat.Snd C D)

def isLimitProdCone (X Y : OFECat) : CategoryTheory.Limits.IsLimit (OFEProdCone X Y) :=
  CategoryTheory.Limits.BinaryFan.isLimitMk
     (fun S => OFECat.ofHom <| Product.functor_prod S.fst.hom S.snd.hom)
     (by aesop_cat)
     (by intros; congr)
     (by
       simp
       intros _ _ H1 H2
       rw [<- H1, <- H2]
       congr)

abbrev OFE.terminal : OFECat := OFECat.of unitO

def OFETerminalIsTerminal : CategoryTheory.Limits.IsTerminal OFE.terminal :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun _ => OFECat.ofHom <| NonExpansive.cconst Unit.unit)
    (by intros; congr)

instance : CategoryTheory.ChosenFiniteProducts OFECat where
  product X Y := { isLimit := isLimitProdCone X Y }
  terminal := { isLimit := OFETerminalIsTerminal }

-- #synth CategoryTheory.Limits.HasFiniteProducts OFECat

-- TODO: Cleanup
def OFEClosedCat.exponentiate (A : OFECat) : CategoryTheory.Functor OFECat OFECat where
  obj Y := OFECat.of (A -n> Y)
  map := fun {X Y} f =>
    OFECat.ofHom <|
    NonExpansive.mk (fun F =>
      (@NonExpansive.ccompose A X Y _ _ _
              (NonExpansive.mk f.hom.toFun <| by apply NonExpansive.is_nonexpansive)
              (NonExpansive.mk F.toFun <| by apply NonExpansive.is_nonexpansive))) <|
      by
        simp [nonexpansive, NonExpansive.ccompose, DFunLike.coe, irel, IRel.ir]
        intros
        apply NonExpansive.is_nonexpansive
        rename_i H x
        have H' := H x
        simp_all [DFunLike.coe]

def NonExpansive.curry [OFE A] [OFE B] [OFE C] (f : (prodO A B) -n> C) : B -n> (A -n> C) :=
  NonExpansive.mk (fun b => NonExpansive.mk (fun a => f (a, b))
      (by
        simp [nonexpansive]
        intros
        apply NonExpansive.is_nonexpansive
        simp [irel, IRel.ir]
        apply And.intro
        · trivial
        · apply refl))
    (by
      simp [nonexpansive]
      intros
      intro _
      simp [DFunLike.coe]
      apply NonExpansive.is_nonexpansive
      simp [irel, IRel.ir]
      apply And.intro
      · apply refl
      · trivial)

def NonExpansive.uncurry [OFE A] [OFE B] [OFE C] (f : B -n> (A -n> C)) : (prodO A B) -n> C :=
  NonExpansive.mk (fun p => f (Prod.snd p) (Prod.fst p)) <|
    by
      simp [nonexpansive]
      intros
      simp [DFunLike.coe]
      rcases f with ⟨ f, Hf ⟩
      simp
      rename_i H
      rcases H with ⟨ H1, H2 ⟩
      simp_all
      apply _root_.trans
      · apply NonExpansive.is_nonexpansive
        apply H1
      apply _root_.trans
      · apply Hf
        apply H2
      apply refl

def OFECatEqv (X Z Y : OFECat) :
    ((CategoryTheory.MonoidalCategory.tensorLeft X).obj Z ⟶ Y) ≃ (Z ⟶ (OFEClosedCat.exponentiate X).obj Y) where
  toFun x := OFECat.ofHom <| NonExpansive.curry x.hom
  invFun x := OFECat.ofHom <| NonExpansive.uncurry x.hom
  left_inv := by aesop_cat
  right_inv := by aesop_cat

def OFECatCoreHomEquiv (X : OFECat) :
    CategoryTheory.Adjunction.CoreHomEquiv (CategoryTheory.MonoidalCategory.tensorLeft X) (OFEClosedCat.exponentiate X) where
  homEquiv Z Y := @OFECatEqv X Z Y

def OFECatClosed (X : OFECat) : CategoryTheory.Closed X where
  rightAdj := OFEClosedCat.exponentiate X
  adj := CategoryTheory.Adjunction.mkOfHomEquiv (OFECatCoreHomEquiv X)

instance : CategoryTheory.CartesianClosed OFECat where
  closed := OFECatClosed

/- The internal hom functor can noe bw used -/
-- def oFunctor' := @CategoryTheory.internalHom OFECat _ _ _

end OFECatCCC





section oFunctorCat

/-! ### oFunctors -/

/-- The data of an oFunctor: A bifunctor from (COFEᵒᵖ × COFE) to OFE,
where the functor laws must hold up to equivalence. -/
abbrev oFunctorPre' := CategoryTheory.Functor (COFECatᵒᵖ × COFECat) qOFECat

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
def oFunctorPre.ofLeibniz (f : oFunctorPreLeibniz) : oFunctorPre' :=
  CategoryTheory.Functor.comp f qOFECat_functor

@[simp, coe]
def oFunctorCPre.ofLeibniz (f : oFunctorCPreLeibniz) : oFunctorCPre :=
  CategoryTheory.Functor.comp f qCOFECat_functor


@[simp, coe]
def oFunctorPre.ofoFunctorCPre (f : oFunctorCPre) : oFunctorPre' :=
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

class oFunctor' (f : oFunctorCPre) where
  internal_nonexpansive : True

class oFunctorContractive' (f : oFunctorCPre) extends oFunctor' f where
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

section CMRABundled
/-! ### The category of CMRAs plus Camera morphisms -/

/-- Objects in the category of CMRA's -/
def CMRACat := CategoryTheory.Bundled CMRA

instance : CoeSort CMRACat Type where
  coe := CategoryTheory.Bundled.α

-- attribute [coe] CategoryTheory.Bundled.α
-- attribute [instance] CategoryTheory.Bundled.str

namespace CMRACat

-- TODO: Camera morphisms, and the category CMRA

end CMRACat

end CMRABundled
