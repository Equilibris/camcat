/-
Copyright (c) 2019 Kim Morrison, Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon, Adam Topaz, Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Cat.BiMonCat
import Cat.Product

/-!
# Categories with chosen finite coproducts

We introduce a class, `CartesianComonoidalCategory`, which bundles explicit choices
for an initial object and binary coproducts in a category `C`.
This is primarily useful for categories which have finite coproducts with good
definitional properties, such as the category of types.

For better defeqs, we also extend `ComonoidalCategory`.

## Implementation notes

For Cartesian comonoidal categories, the oplax-comonoidal/comonoidal/braided structure of a functor `F`
preserving finite coproducts is uniquely determined. See the `ofChosenFiniteCoproducts` declarations.

We however develop the theory for any `F.OplaxComonoidal`/`F.Comonoidal`/`F.Braided` instance instead of
requiring it to be the `ofChosenFiniteProducts` one. This is to avoid diamonds: Consider
e.g. `𝟭 C` and `F ⋙ G`.

In applications requiring a finite-coproduct-preserving functor to be
oplax-comonoidal/comonoidal/braided, avoid `attribute [local instance] ofChosenFiniteCoproducts` but
instead turn on the corresponding `ofChosenFiniteCoproducts` declaration for that functor only.

## Projects

- Construct an instance of chosen finite coproducts in the category of affine scheme, using
  the cotensor product.
- Construct chosen finite coproducts in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open ComonoidalCategory Limits

/-- A comonoidal category is semicartesian if the unit for the cotensor product is an initial object. -/
class SemiCartesianComonoidalCategory (C : Type u) [Category.{v} C] extends ComonoidalCategory C where
  /-- The cotensor unit is an initial object. -/
  isInitialCotensorUnit : IsInitial (𝟘_ C)
  /-- The first injection into the coproduct. -/
  inl (X Y : C) : X ⟶ X ⨿' Y
  /-- The second injection into the coproduct. -/
  inr (X Y : C) : Y ⟶ X ⨿' Y
  inl_def (X Y : C) : inl X Y = (ρ'_ X).inv ≫ X ◁ᵒᵖ isInitialCotensorUnit.to Y := by cat_disch
  inr_def (X Y : C) : inr X Y = (λ'_ Y).inv ≫ isInitialCotensorUnit.to X ▷ᵒᵖ Y := by cat_disch

namespace SemiCartesianComonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianComonoidalCategory C]

/-- The unique map from the initial object. -/
def ofUnit (X : C) : 𝟘_ C ⟶ X := isInitialCotensorUnit.to X

instance (X : C) : Unique (𝟘_ C ⟶ X) := isInitialEquivUnique _ _ isInitialCotensorUnit _

lemma default_eq_ofUnit (X : C) : default = ofUnit X := rfl

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply ofUnit_unique` forcing
lean to do the necessary elaboration.
-/
@[ext]
lemma ofUnit_unique {X : C} (f g : 𝟘_ _ ⟶ X) : f = g :=
  Subsingleton.elim _ _

@[simp] lemma ofUnit_unit : ofUnit (𝟘_ C) = 𝟙 (𝟘_ C) := ofUnit_unique ..

@[reassoc (attr := simp)]
theorem comp_ofUnit {X Y : C} (f : X ⟶ Y) : ofUnit X ≫ f = ofUnit Y :=
  ofUnit_unique _ _

end SemiCartesianComonoidalCategory

variable (C) in
/--
An instance of `CartesianComonoidalCategory C` bundles an explicit choice of a binary
coproduct of two objects of `C`, and an initial object in `C`.

Users should use the comonoidal notation: `X ⨿' Y` for the coproduct and `𝟘_ C` for
the initial object.
-/
class CartesianComonoidalCategory (C : Type u) [Category.{v} C] extends
    SemiCartesianComonoidalCategory C where
  /-- The comonoidal product is the categorical coproduct. -/
  cotensorProductIsBinaryCoproduct (X Y : C) : IsBinaryCoproduct (inl X Y) (inr X Y)

namespace CartesianComonoidalCategory

export SemiCartesianComonoidalCategory (isInitialCotensorUnit inl inr inl_def inr_def ofUnit
  ofUnit_unique ofUnit_unit comp_ofUnit comp_ofUnit_assoc default_eq_ofUnit)

variable {C : Type u} [Category.{v} C]

/- section OfChosenFiniteCoproducts -/
/- variable (𝒯 : ColimitCocone (Functor.empty.{0} C)) (ℬ : ∀ X Y : C, ColimitCocone (pair X Y)) -/
/-   {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : C} -/
/-  -/
/- -- Ignore this section -/
/- namespace ofChosenFiniteCoproducts -/
/-  -/
/- /-- Implementation of the cotensor product for `CartesianComonoidalCategory.ofChosenFiniteCoproducts`. -/ -/
/- abbrev cotensorObj (X Y : C) : C := (ℬ X Y).cocone.pt -/
/-  -/
/- /-- Implementation of the cotensor product of morphisms for -/
/- `CartesianComonoidalCategory.ofChosenFiniteCoproducts`. -/ -/
/- abbrev cotensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : cotensorObj ℬ X₁ X₂ ⟶ cotensorObj ℬ Y₁ Y₂ := -/
/-   (BinaryCofan.IsColimit.desc' -/
/-     (ℬ X₁ X₂).isColimit -/
/-     (f ≫ (ℬ Y₁ Y₂).cocone.ι.app ⟨.left⟩ : X₁ ⟶ (ℬ Y₁ Y₂).cocone.pt) -/
/-     (g ≫ (ℬ Y₁ Y₂).cocone.ι.app ⟨.right⟩ : X₂ ⟶ (ℬ Y₁ Y₂).cocone.pt) -/
/-     ).val -/
/-   /- (IsBinaryCoproduct.map (inl sorry sorry) _ sorry f g) -/ -/
/-  -/
/- lemma id_cotensorHom_id (X Y : C) : cotensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (cotensorObj ℬ X Y) := -/
/-   (ℬ _ _).isColimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [cotensorHom] -/
/-  -/
/- lemma cotensorHom_comp_cotensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : -/
/-     cotensorHom ℬ f₁ f₂ ≫ cotensorHom ℬ g₁ g₂ = cotensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) := -/
/-   (ℬ _ _).isColimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [cotensorHom] -/
/-  -/
/- /-- Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`, -/
/- we obtain an isomorphism between the cone points. -/ -/
/- abbrev associator {X Y Z} {sXY sYZ} (P : IsColimit sXY) (Q : IsColimit sYZ) {s : BinaryCofan sXY.pt Z} -/
/-     (R : IsColimit s) {t : BinaryCofan X sYZ.pt} (S : IsColimit t) : s.pt ≅ t.pt := -/
/-   (P.assoc Q R).conePointUniqueUpToIso S -/
/-  -/
/- /-- Given a fixed family of limit data for every pair `X Y`, we obtain an associator. -/ -/
/- abbrev associatorOfColimitCocone (L : ∀ X Y : C, LimitCone (pair X Y)) (X Y Z : C) : -/
/-     (L (L X Y).cone.pt Z).cone.pt ≅ (L X (L Y Z).cone.pt).cone.pt := -/
/-   associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit -/
/-     (L X (L Y Z).cone.pt).isLimit -/
/-  -/
/- lemma pentagon (W X Y Z : C) : -/
/-     cotensorHom ℬ (associatorOfColimitCocone ℬ W X Y).hom (𝟙 Z) ≫ -/
/-         (associatorOfColimitCocone ℬ W (cotensorObj ℬ X Y) Z).hom ≫ -/
/-           cotensorHom ℬ (𝟙 W) (associatorOfColimitCocone ℬ X Y Z).hom = -/
/-       (BinaryCofan.associatorOfColimitCocone ℬ (cotensorObj ℬ W X) Y Z).hom ≫ -/
/-         (BinaryCofan.associatorOfColimitCocone ℬ W X (cotensorObj ℬ Y Z)).hom := by -/
/-   dsimp [cotensorHom] -/
/-   apply (ℬ _ _).isColimit.hom_ext -/
/-   rintro ⟨_ | _⟩ -/
/-   · simp -/
/-   apply (ℬ _ _).isColimit.hom_ext -/
/-   rintro ⟨_ | _⟩ -/
/-   · simp -/
/-   apply (ℬ _ _).isColimit.hom_ext -/
/-   rintro ⟨_ | _⟩ <;> simp -/
/-  -/
/- lemma triangle (X Y : C) : -/
/-     (BinaryCofan.associatorOfColimitCocone ℬ X 𝒯.cocone.pt Y).hom ≫ -/
/-         cotensorHom ℬ (𝟙 X) (BinaryCofan.leftUnitor 𝒯.isColimit (ℬ 𝒯.cocone.pt Y).isColimit).hom = -/
/-       cotensorHom ℬ (BinaryCofan.rightUnitor 𝒯.isColimit (ℬ X 𝒯.cocone.pt).isColimit).hom (𝟙 Y) := -/
/-   (ℬ _ _).isColimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp -/
/-  -/
/- lemma leftUnitor_naturality (f : X₁ ⟶ X₂) : -/
/-     cotensorHom ℬ (𝟙 𝒯.cocone.pt) f ≫ (BinaryCofan.leftUnitor 𝒯.isColimit (ℬ 𝒯.cocone.pt X₂).isColimit).hom = -/
/-       (BinaryCofan.leftUnitor 𝒯.isColimit (ℬ 𝒯.cocone.pt X₁).isColimit).hom ≫ f := by -/
/-   simp [cotensorHom] -/
/-  -/
/- lemma rightUnitor_naturality (f : X₁ ⟶ X₂) : -/
/-     cotensorHom ℬ f (𝟙 𝒯.cocone.pt) ≫ (BinaryCofan.rightUnitor 𝒯.isColimit (ℬ X₂ 𝒯.cocone.pt).isColimit).hom = -/
/-       (BinaryCofan.rightUnitor 𝒯.isColimit (ℬ X₁ 𝒯.cocone.pt).isColimit).hom ≫ f := by -/
/-   simp [cotensorHom] -/
/-  -/
/- lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : -/
/-     cotensorHom ℬ (cotensorHom ℬ f₁ f₂) f₃ ≫ (BinaryCofan.associatorOfColimitCocone ℬ Y₁ Y₂ Y₃).hom = -/
/-       (BinaryCofan.associatorOfColimitCocone ℬ X₁ X₂ X₃).hom ≫ cotensorHom ℬ f₁ (cotensorHom ℬ f₂ f₃) := by -/
/-   dsimp [cotensorHom] -/
/-   apply (ℬ _ _).isColimit.hom_ext -/
/-   rintro ⟨_ | _⟩ -/
/-   · simp -/
/-   apply (ℬ _ _).isColimit.hom_ext -/
/-   rintro ⟨_ | _⟩ <;> simp -/
/-  -/
/- end ofChosenFiniteCoproducts -/
/-  -/
/- open ofChosenFiniteCoproducts -/
/-  -/
/- /-- Construct an instance of `CartesianComonoidalCategory C` given an initial object and colimit cones -/
/- over arbitrary pairs of objects. -/ -/
/- abbrev ofChosenFiniteCoproducts : CartesianComonoidalCategory C := -/
/-   letI : ComonoidalCategoryStruct C := { -/
/-     cotensorUnit := 𝒯.cocone.pt -/
/-     cotensorObj := cotensorObj ℬ -/
/-     cotensorHom := cotensorHom ℬ -/
/-     whiskerLeft X {_ _} g := cotensorHom ℬ (𝟙 X) g -/
/-     whiskerRight {_ _} f Y := cotensorHom ℬ f (𝟙 Y) -/
/-     associator := BinaryCofan.associatorOfColimitCocone ℬ -/
/-     leftUnitor X := BinaryCofan.leftUnitor 𝒯.isColimit (ℬ 𝒯.cocone.pt X).isColimit -/
/-     rightUnitor X := BinaryCofan.rightUnitor 𝒯.isColimit (ℬ X 𝒯.cocone.pt).isColimit -/
/-   } -/
/-   { -/
/-   toComonoidalCategory := .ofCotensorHom -/
/-     (id_cotensorHom_id := id_cotensorHom_id ℬ) -/
/-     (cotensorHom_comp_cotensorHom := cotensorHom_comp_cotensorHom ℬ) -/
/-     (pentagon := pentagon ℬ) -/
/-     (triangle := triangle 𝒯 ℬ) -/
/-     (leftUnitor_naturality := leftUnitor_naturality 𝒯 ℬ) -/
/-     (rightUnitor_naturality := rightUnitor_naturality 𝒯 ℬ) -/
/-     (associator_naturality := associator_naturality ℬ) -/
/-   isInitialCotensorUnit := -/
/-     .ofUniqueHom (𝒯.isColimit.desc <| asEmptyCocone ·) fun _ _ ↦ 𝒯.isColimit.hom_ext (by simp) -/
/-   inl X Y := BinaryCofan.inl (ℬ X Y).cocone -/
/-   inr X Y := BinaryCofan.inr (ℬ X Y).cocone -/
/-   cotensorProductIsBinaryCoproduct X Y := BinaryCofan.IsColimit.mk _ -/
/-     (fun f g ↦ (BinaryCofan.IsColimit.desc' (ℬ X Y).isColimit f g).1) -/
/-     (fun f g ↦ (BinaryCofan.IsColimit.desc' (ℬ X Y).isColimit f g).2.1) -/
/-     (fun f g ↦ (BinaryCofan.IsColimit.desc' (ℬ X Y).isColimit f g).2.2) -/
/-     (fun f g m hf hg ↦ -/
/-       BinaryCofan.IsColimit.hom_ext (ℬ X Y).isColimit (by simpa using hf) (by simpa using hg)) -/
/-   inl_def X Y := (((ℬ X 𝒯.cocone.pt).isColimit.fac -/
/-     (BinaryCofan.mk _ _) ⟨.left⟩).trans (Category.comp_id _)).symm -/
/-   inr_def X Y := (((ℬ 𝒯.cocone.pt Y).isColimit.fac -/
/-     (BinaryCofan.mk _ _) ⟨.right⟩).trans (Category.comp_id _)).symm -/
/-   } -/
/-  -/
/- omit 𝒯 in -/
/- /-- Constructs an instance of `CartesianComonoidalCategory C` given the existence of finite coproducts -/
/- in `C`. -/ -/
/- noncomputable abbrev ofHasFiniteCoproducts [HasFiniteCoproducts C] : CartesianComonoidalCategory C := -/
/-   .ofChosenFiniteCoproducts (getColimitCone (.empty C)) (getColimitCone <| pair · ·) -/
/-  -/
/- end OfChosenFiniteCoproducts -/

variable {C : Type u} [Category.{v} C] [CartesianComonoidalCategory C]

open ComonoidalCategory SemiCartesianComonoidalCategory

/--
Constructs a morphism from the coproduct given its two components.
-/
def desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : X ⨿' Y ⟶ T :=
  (BinaryCofan.IsColimit.desc' (cotensorProductIsBinaryCoproduct X Y) f g).1

@[reassoc (attr := simp)]
lemma inl_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inl _ _ ≫ desc f g = f :=
  (BinaryCofan.IsColimit.desc' (cotensorProductIsBinaryCoproduct X Y) f g).2.1

@[reassoc (attr := simp)]
lemma inr_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inr _ _ ≫ desc f g = g :=
  (BinaryCofan.IsColimit.desc' (cotensorProductIsBinaryCoproduct X Y) f g).2.2

instance epi_desc_of_epi_left {W X Y : C} (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (desc f g) :=
  epi_of_epi_fac <| inl_desc _ _

instance epi_desc_of_epi_right {W X Y : C} (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (desc f g) :=
  epi_of_epi_fac <| inr_desc _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : X ⨿' Y ⟶ T)
    (h_inl : inl _ _ ≫ f = inl _ _ ≫ g)
    (h_inr : inr _ _ ≫ f = inr _ _ ≫ g) :
    f = g :=
  BinaryCofan.IsColimit.hom_ext (cotensorProductIsBinaryCoproduct X Y) h_inl h_inr

-- Similarly to `CategoryTheory.Limits.coprod.desc_comp`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
lemma desc_comp {V W X Y : C} (f : X ⟶ V) (g : Y ⟶ V) (h : V ⟶ W) :
    desc f g ≫ h = desc (f ≫ h) (g ≫ h) := by ext <;> simp

@[simp]
lemma desc_inl_inr {X Y : C} : desc (inl X Y) (inr X Y) = 𝟙 (X ⨿' Y) := by ext <;> simp

@[simp]
lemma inl_inr_desc {X Y Z : C} (f : X ⨿' Y ⟶ Z) :
    desc (inl _ _ ≫ f) (inr _ _ ≫ f) = f := by
  cat_disch

@[reassoc (attr := simp)]
lemma cowhiskerLeft_inl (X : C) {Y Z : C} (f : Y ⟶ Z) : inl _ _ ≫ X ◁ᵒᵖ f = inl _ _ := by
  simp [inl_def, ← cowhiskerLeft_comp]

@[reassoc (attr := simp)]
lemma cowhiskerLeft_inr (X : C) {Y Z : C} (f : Y ⟶ Z) : inr _ _ ≫ X ◁ᵒᵖ f = f ≫ inr _ _ := by
  stop
  simp [inr_def, cowhisker_exchange]

@[reassoc (attr := simp)]
lemma cowhiskerRight_inl {X Y : C} (f : X ⟶ Y) (Z : C) : inl _ _ ≫ f ▷ᵒᵖ Z = f ≫ inl _ _ := by
  stop
  simp [inl_def, ← cowhisker_exchange]

@[reassoc (attr := simp)]
lemma cowhiskerRight_inr {X Y : C} (f : X ⟶ Y) (Z : C) : inr _ _ ≫ f ▷ᵒᵖ Z = inr _ _ := by
  simp [inr_def, ← comp_cowhiskerRight]

@[reassoc (attr := simp)]
lemma cotensorHom_inl {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    inl _ _ ≫ (f ⨿'ₘ g) = f ≫ inl _ _ := by simp [cotensorHom_def]

@[reassoc (attr := simp)]
lemma cotensorHom_inr {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    inr _ _ ≫ (f ⨿'ₘ g) = g ≫ inr _ _ := by simp [cotensorHom_def]

@[reassoc (attr := simp)]
lemma desc_map {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : W ⟶ Z) (k : Y ⟶ Z) :
    (f ⨿'ₘ g) ≫ desc h k = desc (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
lemma desc_inl_comp_inr_comp {W X Y Z : C} (g : W ⟶ Z) (g' : Y ⟶ Z) :
    desc (g ≫ inl _ _) (g' ≫ inr _ _) = g ⨿'ₘ g' := by ext <;> simp

@[reassoc (attr := simp)]
lemma desc_cowhiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ Y) (h : W ⟶ X) :
    (h ▷ᵒᵖ Z) ≫ desc f g = desc (h ≫ f) g := by
  cat_disch

@[reassoc (attr := simp)]
lemma desc_cowhiskerLeft {X Y Z W : C} (f : Y ⟶ X) (g : Z ⟶ X) (h : W ⟶ Z) :
    (Y ◁ᵒᵖ h) ≫ desc f g = desc f (h ≫ g) := by
  cat_disch

@[reassoc (attr := simp)]
lemma associator_hom_inr (X Y Z : C) :
    inr _ _ ≫ (α'_ X Y Z).hom = inr _ _ ≫ inr _ _ := by
  stop
  simp [inr_def, ← cowhiskerLeft_rightUnitor, -cowhiskerLeft_rightUnitor,
    ← cowhiskerLeft_comp]

@[reassoc (attr := simp)]
lemma associator_hom_inr_inl (X Y Z : C) :
    inr _ _ ≫ inl _ _ ≫ (α'_ X Y Z).hom = inl _ _ ≫ inr _ _ := by
  stop
  simp [inl_def, ← cowhiskerLeft_rightUnitor, -cowhiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
lemma associator_hom_inr_inr (X Y Z : C) :
    inl _ _ ≫ inl _ _ ≫ (α'_ X Y Z).hom = inl _ _ := by
  stop
  simp [inr_def, ← leftUnitor_cowhiskerRight, -leftUnitor_cowhiskerRight,
    ← comp_cowhiskerRight]

-- These signatures are all wrong
@[reassoc (attr := simp)]
lemma associator_inv_inl_inl (X Y Z : C) :
    inr _ _ ≫ inr _ _ ≫ (α'_ X Y Z).inv = inr _ _ := by
  stop
  simp [inl_def, ← cowhiskerLeft_rightUnitor, -cowhiskerLeft_rightUnitor,
    ← cowhiskerLeft_comp]

@[reassoc (attr := simp)]
lemma associator_inv_inl_inr (X Y Z : C) :
    inl _ _ ≫ inr _ _ ≫ (α'_ X Y Z).inv = inr _ _ ≫ inl _ _ := by
  stop
  simp [inl_def, ← cowhiskerLeft_rightUnitor, -cowhiskerLeft_rightUnitor]

/- @[reassoc (attr := simp)] -/
/- lemma associator_inv_inr (X Y Z : C) : -/
/-     inr _ _ ≫ (α'_ X Y Z).inv = inr _ _ ≫ inl _ _ := by -/
/-   stop -/
/-   simp [inr_def, ← leftUnitor_cowhiskerRight, -leftUnitor_cowhiskerRight, -/
/-     ← comp_cowhiskerRight] -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma desc_desc_associator_hom {X Y Z W : C} (f : Y ⟶ X) (g : Z ⟶ X) (h : W ⟶ X) : -/
/-     desc (desc f g) h ≫ (α'_ Y Z W).hom = desc f (desc g h) := by -/
/-   cat_disch -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma desc_desc_associator_inv {X Y Z W : C} (f : Y ⟶ X) (g : Z ⟶ X) (h : W ⟶ X) : -/
/-     desc f (desc g h) ≫ (α'_ Y Z W).inv = desc (desc f g) h := by -/
/-   cat_disch -/
/-  -/
/- lemma leftUnitor_hom (X : C) : (λ'_ X).hom = inr _ _ := by simp [inr_def] -/
/- lemma rightUnitor_hom (X : C) : (ρ'_ X).hom = inl _ _ := by simp [inl_def] -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma leftUnitor_inv_inl (X : C) : -/
/-     (λ'_ X).inv ≫ inl _ _ = ofUnit _ := ofUnit_unique _ _ -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma leftUnitor_inv_inr (X : C) : -/
/-     (λ'_ X).inv ≫ inr _ _ = 𝟙 X := by simp [inr_def] -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma rightUnitor_inv_inl (X : C) : -/
/-     (ρ'_ X).inv ≫ inl _ _ = 𝟙 X := by simp [inl_def] -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma rightUnitor_inv_inr (X : C) : -/
/-     (ρ'_ X).inv ≫ inr _ _ = ofUnit _ := ofUnit_unique _ _ -/
/-  -/
/- @[reassoc] -/
/- lemma cowhiskerLeft_ofUnit_comp_rightUnitor_hom (X Y : C) : X ◁ᵒᵖ ofUnit Y ≫ (ρ'_ X).hom = inl X Y := by -/
/-   rw [← cancel_mono (ρ'_ X).inv]; aesop -/
/-  -/
/- @[reassoc] -/
/- lemma cowhiskerRight_ofUnit_comp_leftUnitor_hom (X Y : C) : ofUnit X ▷ᵒᵖ Y ≫ (λ'_ Y).hom = inr X Y := by -/
/-   rw [← cancel_mono (λ'_ Y).inv]; aesop -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma desc_leftUnitor_hom {X Y : C} (f : 𝟘_ C ⟶ X) (g : Y ⟶ X) : -/
/-     desc f g ≫ (λ'_ Y).hom = g := by -/
/-   rw [← Iso.eq_comp_inv] -/
/-   cat_disch -/
/-  -/
/- @[reassoc (attr := simp)] -/
/- lemma desc_rightUnitor_hom {X Y : C} (f : Y ⟶ X) (g : 𝟘_ C ⟶ X) : -/
/-     desc f g ≫ (ρ'_ Y).hom = f := by -/
/-   rw [← Iso.eq_comp_inv] -/
/-   cat_disch -/
/-  -/
/- /-- Universal property of the Cartesian product: Maps to `X ⨿' Y` correspond to pairs of maps to `X` -/
/- and to `Y`. -/ -/
/- @[simps] -/
/- def homEquivToProd {X Y Z : C} : (Z ⟶ X ⨿' Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where -/
/-   toFun f := ⟨f ≫ inl _ _, f ≫ inr _ _⟩ -/
/-   invFun f := lift f.1 f.2 -/
/-   left_inv _ := by simp -/
/-   right_inv _ := by simp -/
/-  -/
