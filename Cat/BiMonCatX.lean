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

/-!
# Categories with chosen finite products

We introduce a class, `CartesianComonoidalCategory`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

For better defeqs, we also extend `ComonoidalCategory`.

## Implementation notes

For Cartesian monoidal categories, the oplax-monoidal/monoidal/braided structure of a functor `F`
preserving finite products is uniquely determined. See the `ofChosenFiniteProducts` declarations.

We however develop the theory for any `F.OplaxComonoidal`/`F.Comonoidal`/`F.Braided` instance instead of
requiring it to be the `ofChosenFiniteProducts` one. This is to avoid diamonds: Consider
e.g. `𝟭 C` and `F ⋙ G`.

In applications requiring a finite-product-preserving functor to be
oplax-monoidal/monoidal/braided, avoid `attribute [local instance] ofChosenFiniteProducts` but
instead turn on the corresponding `ofChosenFiniteProducts` declaration for that functor only.

## Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the cotensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open ComonoidalCategory Limits

/-- A monoidal category is semicartesian if the unit for the cotensor product is a terminal object. -/
class SemiCartesianComonoidalCategory (C : Type u) [Category.{v} C] extends ComonoidalCategory C where
  /-- The cotensor unit is a terminal object. -/
  isInitialCotensorUnit : IsInitial (𝟘_ C)
  /-- The first projection from the product. -/
  inl (X Y : C) : X ⟶ X ⨿' Y
  /-- The second projection from the product. -/
  inr (X Y : C) : Y ⟶ X ⨿' Y
  inl_def (X Y : C) : inl X Y = (ρ'_ X).inv ≫ X ◁ᵒᵖ isInitialCotensorUnit.to Y := by cat_disch
  inr_def (X Y : C) : inr X Y = (λ'_ Y).inv ≫ isInitialCotensorUnit.to X ▷ᵒᵖ Y := by cat_disch

namespace SemiCartesianComonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianComonoidalCategory C]

/-- The unique map to the terminal object. -/
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
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
class CartesianComonoidalCategory (C : Type u) [Category.{v} C] extends
    SemiCartesianComonoidalCategory C where
  /-- The monoidal product is the categorical product. -/
  cotensorProductIsBinaryProduct (X Y : C) : IsColimit <| BinaryCofan.mk (inl X Y) (inr X Y)

@[deprecated (since := "2025-05-15")] alias ChosenFiniteProducts := CartesianComonoidalCategory

namespace CartesianComonoidalCategory

export SemiCartesianComonoidalCategory (isTerminalCotensorUnit inl inr inl_def inr_def ofUnit
  ofUnit_unique ofUnit_unit comp_ofUnit comp_ofUnit_assoc default_eq_ofUnit)

variable {C : Type u} [Category.{v} C]

section OfChosenFiniteProducts
variable (𝒯 : LimitCone (Functor.empty.{0} C)) (ℬ : ∀ X Y : C, LimitCone (pair X Y))
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : C}

namespace ofChosenFiniteProducts

/-- Implementation of the cotensor product for `CartesianComonoidalCategory.ofChosenFiniteProducts`. -/
abbrev cotensorObj (X Y : C) : C := (ℬ X Y).cone.pt

/-- Implementation of the cotensor product of morphisms for
`CartesianComonoidalCategory.ofChosenFiniteProducts`. -/
abbrev cotensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : cotensorObj ℬ X₁ X₂ ⟶ cotensorObj ℬ Y₁ Y₂ :=
  (BinaryFan.IsLimit.lift' (ℬ Y₁ Y₂).isLimit ((ℬ X₁ X₂).cone.π.app ⟨.left⟩ ≫ f)
      (((ℬ X₁ X₂).cone.π.app ⟨.right⟩ : (ℬ X₁ X₂).cone.pt ⟶ X₂) ≫ g)).val

lemma id_cotensorHom_id (X Y : C) : cotensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (cotensorObj ℬ X Y) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [cotensorHom]

@[deprecated (since := "2025-07-14")] alias cotensor_id := id_cotensorHom_id

lemma cotensorHom_comp_cotensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    cotensorHom ℬ f₁ f₂ ≫ cotensorHom ℬ g₁ g₂ = cotensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [cotensorHom]

lemma pentagon (W X Y Z : C) :
    cotensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y).hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ W (cotensorObj ℬ X Y) Z).hom ≫
          cotensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom =
      (BinaryFan.associatorOfLimitCone ℬ (cotensorObj ℬ W X) Y Z).hom ≫
        (BinaryFan.associatorOfLimitCone ℬ W X (cotensorObj ℬ Y Z)).hom := by
  dsimp [cotensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

lemma triangle (X Y : C) :
    (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫
        cotensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).hom =
      cotensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙 Y) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp

lemma leftUnitor_naturality (f : X₁ ⟶ X₂) :
    cotensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom =
      (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f := by
  simp [cotensorHom]

lemma rightUnitor_naturality (f : X₁ ⟶ X₂) :
    cotensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom =
      (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f := by
  simp [cotensorHom]

lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    cotensorHom ℬ (cotensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).hom =
      (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).hom ≫ cotensorHom ℬ f₁ (cotensorHom ℬ f₂ f₃) := by
  dsimp [cotensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

end ofChosenFiniteProducts

open ofChosenFiniteProducts

/-- Construct an instance of `CartesianComonoidalCategory C` given a terminal object and limit cones
over arbitrary pairs of objects. -/
abbrev ofChosenFiniteProducts : CartesianComonoidalCategory C :=
  letI : ComonoidalCategoryStruct C := {
    cotensorUnit := 𝒯.cone.pt
    cotensorObj := cotensorObj ℬ
    cotensorHom := cotensorHom ℬ
    whiskerLeft X {_ _} g := cotensorHom ℬ (𝟙 X) g
    whiskerRight {_ _} f Y := cotensorHom ℬ f (𝟙 Y)
    associator := BinaryFan.associatorOfLimitCone ℬ
    leftUnitor X := BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X).isLimit
    rightUnitor X := BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit
  }
  {
  toComonoidalCategory := .ofCotensorHom
    (id_cotensorHom_id := id_cotensorHom_id ℬ)
    (cotensorHom_comp_cotensorHom := cotensorHom_comp_cotensorHom ℬ)
    (pentagon := pentagon ℬ)
    (triangle := triangle 𝒯 ℬ)
    (leftUnitor_naturality := leftUnitor_naturality 𝒯 ℬ)
    (rightUnitor_naturality := rightUnitor_naturality 𝒯 ℬ)
    (associator_naturality := associator_naturality ℬ)
  isTerminalCotensorUnit :=
    .ofUniqueHom (𝒯.isLimit.lift <| asEmptyCone ·) fun _ _ ↦ 𝒯.isLimit.hom_ext (by simp)
  inl X Y := BinaryFan.inl (ℬ X Y).cone
  inr X Y := BinaryFan.inr (ℬ X Y).cone
  cotensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).1)
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.1)
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.2)
    (fun f g m hf hg ↦
      BinaryFan.IsLimit.hom_ext (ℬ X Y).isLimit (by simpa using hf) (by simpa using hg))
  inl_def X Y := (((ℬ X 𝒯.cone.pt).isLimit.fac
    (BinaryFan.mk _ _) ⟨.left⟩).trans (Category.comp_id _)).symm
  inr_def X Y := (((ℬ 𝒯.cone.pt Y).isLimit.fac
    (BinaryFan.mk _ _) ⟨.right⟩).trans (Category.comp_id _)).symm
  }

omit 𝒯 in
/-- Constructs an instance of `CartesianComonoidalCategory C` given the existence of finite products
in `C`. -/
noncomputable abbrev ofHasFiniteProducts [HasFiniteProducts C] : CartesianComonoidalCategory C :=
  .ofChosenFiniteProducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

@[deprecated (since := "2025-05-08")] alias ofFiniteProducts := ofHasFiniteProducts

end OfChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [CartesianComonoidalCategory C]

open ComonoidalCategory

/--
Constructs a morphism to the product given its two components.
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊗ Y :=
  (BinaryFan.IsLimit.lift' (cotensorProductIsBinaryProduct X Y) f g).1

@[reassoc (attr := simp)]
lemma lift_inl {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ inl _ _ = f :=
  (BinaryFan.IsLimit.lift' (cotensorProductIsBinaryProduct X Y) f g).2.1

@[reassoc (attr := simp)]
lemma lift_inr {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ inr _ _ = g :=
  (BinaryFan.IsLimit.lift' (cotensorProductIsBinaryProduct X Y) f g).2.2

instance mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_inl _ _

instance mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_inr _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : T ⟶ X ⊗ Y)
    (h_inl : f ≫ inl _ _ = g ≫ inl _ _)
    (h_inr : f ≫ inr _ _ = g ≫ inr _ _) :
    f = g :=
  BinaryFan.IsLimit.hom_ext (cotensorProductIsBinaryProduct X Y) h_inl h_inr

-- Similarly to `CategoryTheory.Limits.prod.comp_lift`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
lemma comp_lift {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[simp]
lemma lift_inl_inr {X Y : C} : lift (inl X Y) (inr X Y) = 𝟙 (X ⊗ Y) := by ext <;> simp

@[simp]
lemma lift_comp_inl_inr {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    lift (f ≫ inl _ _) (f ≫ inr _ _) = f := by
  cat_disch

@[reassoc (attr := simp)]
lemma whiskerLeft_inl (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ inl _ _ = inl _ _ := by
  simp [inl_def, ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma whiskerLeft_inr (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ inr _ _ = inr _ _ ≫ f := by
  simp [inr_def, whisker_exchange_assoc]

@[reassoc (attr := simp)]
lemma whiskerRight_inl {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ inl _ _ = inl _ _ ≫ f := by
  simp [inl_def, ← whisker_exchange_assoc]

@[reassoc (attr := simp)]
lemma whiskerRight_inr {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ inr _ _ = inr _ _ := by
  simp [inr_def, ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma cotensorHom_inl {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ inl _ _ = inl _ _ ≫ f := by simp [cotensorHom_def]

@[reassoc (attr := simp)]
lemma cotensorHom_inr {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ inr _ _ = inr _ _ ≫ g := by simp [cotensorHom_def]

@[reassoc (attr := simp)]
lemma lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    lift f g ≫ (h ⊗ₘ k) = lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
lemma lift_inl_comp_inr_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (inl _ _ ≫ g) (inr _ _ ≫ g') = g ⊗ₘ g' := by ext <;> simp

@[reassoc (attr := simp)]
lemma lift_whiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) :
    lift f g ≫ (h ▷ Z) = lift (f ≫ h) g := by
  cat_disch

@[reassoc (attr := simp)]
lemma lift_whiskerLeft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) :
    lift f g ≫ (Y ◁ h) = lift f (g ≫ h) := by
  cat_disch

@[reassoc (attr := simp)]
lemma associator_hom_inl (X Y Z : C) :
    (α_ X Y Z).hom ≫ inl _ _ = inl _ _ ≫ inl _ _ := by
  simp [inl_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma associator_hom_inr_inl (X Y Z : C) :
    (α_ X Y Z).hom ≫ inr _ _ ≫ inl _ _ = inl _ _ ≫ inr _ _ := by
  simp [inl_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
lemma associator_hom_inr_inr (X Y Z : C) :
    (α_ X Y Z).hom ≫ inr _ _ ≫ inr _ _ = inr _ _ := by
  simp [inr_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma associator_inv_inl_inl (X Y Z : C) :
    (α_ X Y Z).inv ≫ inl _ _ ≫ inl _ _ = inl _ _ := by
  simp [inl_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
lemma associator_inv_inl_inr (X Y Z : C) :
    (α_ X Y Z).inv ≫ inl _ _ ≫ inr _ _ = inr _ _ ≫ inl _ _ := by
  simp [inl_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
lemma associator_inv_inr (X Y Z : C) :
    (α_ X Y Z).inv ≫ inr _ _ = inr _ _ ≫ inr _ _ := by
  simp [inr_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma lift_lift_associator_hom {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift (lift f g) h ≫ (α_ Y Z W).hom = lift f (lift g h) := by
  cat_disch

@[reassoc (attr := simp)]
lemma lift_lift_associator_inv {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift f (lift g h) ≫ (α_ Y Z W).inv = lift (lift f g) h := by
  cat_disch

lemma leftUnitor_hom (X : C) : (λ_ X).hom = inr _ _ := by simp [inr_def]
lemma rightUnitor_hom (X : C) : (ρ_ X).hom = inl _ _ := by simp [inl_def]

@[reassoc (attr := simp)]
lemma leftUnitor_inv_inl (X : C) :
    (λ_ X).inv ≫ inl _ _ = ofUnit _ := ofUnit_unique _ _

@[reassoc (attr := simp)]
lemma leftUnitor_inv_inr (X : C) :
    (λ_ X).inv ≫ inr _ _ = 𝟙 X := by simp [inr_def]

@[reassoc (attr := simp)]
lemma rightUnitor_inv_inl (X : C) :
    (ρ_ X).inv ≫ inl _ _ = 𝟙 X := by simp [inl_def]

@[reassoc (attr := simp)]
lemma rightUnitor_inv_inr (X : C) :
    (ρ_ X).inv ≫ inr _ _ = ofUnit _ := ofUnit_unique _ _

@[reassoc]
lemma whiskerLeft_ofUnit_comp_rightUnitor_hom (X Y : C) : X ◁ ofUnit Y ≫ (ρ_ X).hom = inl X Y := by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]
lemma whiskerRight_ofUnit_comp_leftUnitor_hom (X Y : C) : ofUnit X ▷ Y ≫ (λ_ Y).hom = inr X Y := by
  rw [← cancel_mono (λ_ Y).inv]; aesop

@[reassoc (attr := simp)]
lemma lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) :
    lift f g ≫ (λ_ Y).hom = g := by
  rw [← Iso.eq_comp_inv]
  cat_disch

@[reassoc (attr := simp)]
lemma lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) :
    lift f g ≫ (ρ_ Y).hom = f := by
  rw [← Iso.eq_comp_inv]
  cat_disch

/-- Universal property of the Cartesian product: Maps to `X ⊗ Y` correspond to pairs of maps to `X`
and to `Y`. -/
@[simps]
def homEquivToProd {X Y Z : C} : (Z ⟶ X ⊗ Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := ⟨f ≫ inl _ _, f ≫ inr _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

section BraidedCategory

variable [BraidedCategory C]

@[reassoc (attr := simp)]
theorem braiding_hom_inl (X Y : C) : (β_ X Y).hom ≫ inl _ _ = inr _ _ := by
  simp [inl_def, inr_def, ← BraidedCategory.braiding_naturality_left_assoc]

@[reassoc (attr := simp)]
theorem braiding_hom_inr (X Y : C) : (β_ X Y).hom ≫ inr _ _ = inl _ _ := by
  simp [inl_def, inr_def, ← BraidedCategory.braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
theorem braiding_inv_inl (X Y : C) : (β_ X Y).inv ≫ inl _ _ = inr _ _ := by
  simp [inl_def, inr_def, ← BraidedCategory.braiding_inv_naturality_left_assoc]

@[reassoc (attr := simp)]
theorem braiding_inv_inr (X Y : C) : (β_ X Y).inv ≫ inr _ _ = inl _ _ := by
  simp [inl_def, inr_def, ← BraidedCategory.braiding_inv_naturality_right_assoc]

@[reassoc (attr := simp)]
lemma cotensorμ_inl (W X Y Z : C) : cotensorμ W X Y Z ≫ inl (W ⊗ Y) (X ⊗ Z) = inl W X ⊗ₘ inl Y Z := by
  ext <;> simp [cotensorμ]

@[reassoc (attr := simp)]
lemma cotensorμ_inr (W X Y Z : C) : cotensorμ W X Y Z ≫ inr (W ⊗ Y) (X ⊗ Z) = inr W X ⊗ₘ inr Y Z := by
  ext <;> simp [cotensorμ]

@[reassoc (attr := simp)]
lemma cotensorδ_inl (W X Y Z : C) : cotensorδ W X Y Z ≫ inl (W ⊗ X) (Y ⊗ Z) = inl W Y ⊗ₘ inl X Z := by
  ext <;> simp [cotensorδ]

@[reassoc (attr := simp)]
lemma cotensorδ_inr (W X Y Z : C) : cotensorδ W X Y Z ≫ inr (W ⊗ X) (Y ⊗ Z) = inr W Y ⊗ₘ inr X Z := by
  ext <;> simp [cotensorδ]

theorem lift_inr_inl {X Y : C} : lift (inr X Y) (inl X Y) = (β_ X Y).hom := by cat_disch

@[simp, reassoc]
lemma lift_inr_comp_inl_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (inr _ _ ≫ g') (inl _ _ ≫ g) = (β_ _ _).hom ≫ (g' ⊗ₘ g) := by cat_disch

@[reassoc (attr := simp)]
lemma lift_braiding_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ X Y).hom = lift g f := by aesop

@[reassoc (attr := simp)]
lemma lift_braiding_inv {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ Y X).inv = lift g f := by aesop

-- See note [lower instance priority]
instance (priority := low) toSymmetricCategory [BraidedCategory C] : SymmetricCategory C where

/-- `CartesianComonoidalCategory` implies `BraidedCategory`.
This is not an instance to prevent diamonds. -/
def _root_.CategoryTheory.BraidedCategory.ofCartesianComonoidalCategory : BraidedCategory C where
  braiding X Y := { hom := lift (inr _ _) (inl _ _), inv := lift (inr _ _) (inl _ _) }

@[deprecated (since := "2025-05-15")]
alias _root_.CategoryTheory.BraidedCategory.ofChosenFiniteProducts :=
  BraidedCategory.ofCartesianComonoidalCategory

instance : Nonempty (BraidedCategory C) := ⟨.ofCartesianComonoidalCategory⟩

instance : Subsingleton (BraidedCategory C) where
  allEq
  | ⟨e₁, a₁, b₁, c₁, d₁⟩, ⟨e₂, a₂, b₂, c₂, d₂⟩ => by
      congr
      ext
      · exact (@braiding_hom_inl C _ ‹_› ⟨e₁, a₁, b₁, c₁, d₁⟩ ..).trans
          (@braiding_hom_inl C _ ‹_› ⟨e₂, a₂, b₂, c₂, d₂⟩ ..).symm
      · exact (@braiding_hom_inr C _ ‹_› ⟨e₁, a₁, b₁, c₁, d₁⟩ ..).trans
          (@braiding_hom_inr C _ ‹_› ⟨e₂, a₂, b₂, c₂, d₂⟩ ..).symm

instance : Subsingleton (SymmetricCategory C) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; congr; exact Subsingleton.elim _ _

end BraidedCategory

instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : ∀ (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk ⟨_, cotensorProductIsBinaryProduct _ _⟩
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ C)
  hasFiniteProducts_of_has_binary_and_terminal

section CartesianComonoidalCategoryComparison

variable {D : Type u₁} [Category.{v₁} D] [CartesianComonoidalCategory D] (F : C ⥤ D)
variable {E : Type u₂} [Category.{v₂} E] [CartesianComonoidalCategory E] (G : D ⥤ E)

section terminalComparison

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`terminalComparison F` is the unique map `F (𝟙_ C) ⟶ 𝟙_ D`. -/
abbrev terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D := ofUnit _

@[reassoc]
lemma map_ofUnit_comp_terminalComparison (A : C) :
    F.map (ofUnit A) ≫ terminalComparison F = ofUnit _ := ofUnit_unique _ _

open Limits

/-- If `terminalComparison F` is an Iso, then `F` preserves terminal objects. -/
lemma preservesLimit_empty_of_isIso_terminalComparison [IsIso (terminalComparison F)] :
    PreservesLimit (Functor.empty.{0} C) F := by
  apply preservesLimit_of_preserves_limit_cone isTerminalCotensorUnit
  apply isLimitChangeEmptyCone D isTerminalCotensorUnit
  exact asIso (terminalComparison F)|>.symm

/-- If `F` preserves terminal objects, then `terminalComparison F` is an isomorphism. -/
noncomputable def preservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] :
    F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (isLimitChangeEmptyCone D (isLimitOfPreserves _ isTerminalCotensorUnit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso isTerminalCotensorUnit

@[simp]
lemma preservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] :
    (preservesTerminalIso F).hom = terminalComparison F := ofUnit_unique _ _

instance terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty.{0} C) F] :
    IsIso (terminalComparison F) := by
  rw [← preservesTerminalIso_hom]
  infer_instance

@[simp]
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  cat_disch

@[simp]
lemma preservesTerminalIso_comp [PreservesLimit (Functor.empty.{0} C) F]
    [PreservesLimit (Functor.empty.{0} D) G] [PreservesLimit (Functor.empty.{0} C) (F ⋙ G)] :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  cat_disch

end terminalComparison

section prodComparison

variable (A B : C)

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`prodComparison F A B` is the canonical comparison morphism from `F (A ⊗ B)` to `F(A) ⊗ F(B)`. -/
def prodComparison (A B : C) : F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B :=
  lift (F.map (inl A B)) (F.map (inr A B))

@[reassoc (attr := simp)]
theorem prodComparison_inl : prodComparison F A B ≫ inl _ _ = F.map (inl A B) :=
  lift_inl _ _

@[reassoc (attr := simp)]
theorem prodComparison_inr : prodComparison F A B ≫ inr _ _ = F.map (inr A B) :=
  lift_inr _ _

@[reassoc (attr := simp)]
theorem inv_prodComparison_map_inl [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (inl _ _) = inl _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem inv_prodComparison_map_inr [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (inr _ _) = inr _ _ := by simp [IsIso.inv_comp_eq]

variable {A B} {A' B' : C}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (f ⊗ₘ g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ (F.map f ⊗ₘ F.map g) := by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_inl, cotensorHom_inl, prodComparison_inl_assoc,
    prodComparison_inr, cotensorHom_inr, prodComparison_inr_assoc, ← F.map_comp]

/-- Naturality of the `prodComparison` morphism in the right argument. -/
@[reassoc]
theorem prodComparison_natural_whiskerLeft (g : B ⟶ B') :
    F.map (A ◁ g) ≫ prodComparison F A B' =
      prodComparison F A B ≫ (F.obj A ◁ F.map g) := by
  ext <;> simp [← Functor.map_comp]

/-- Naturality of the `prodComparison` morphism in the left argument. -/
@[reassoc]
theorem prodComparison_natural_whiskerRight (f : A ⟶ A') :
    F.map (f ▷ B) ≫ prodComparison F A' B =
      prodComparison F A B ≫ (F.map f ▷ F.obj B) := by
  ext <;> simp [← Functor.map_comp]

section
variable [IsIso (prodComparison F A B)]

/-- If the product comparison morphism is an iso, its inverse is natural in both argument. -/
@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (f ⊗ₘ g) =
      (F.map f ⊗ₘ F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

/-- If the product comparison morphism is an iso, its inverse is natural in the right argument. -/
@[reassoc]
theorem prodComparison_inv_natural_whiskerLeft (g : B ⟶ B') [IsIso (prodComparison F A B')] :
    inv (prodComparison F A B) ≫ F.map (A ◁ g) =
      (F.obj A ◁ F.map g) ≫ inv (prodComparison F A B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerLeft]

/-- If the product comparison morphism is an iso, its inverse is natural in the left argument. -/
@[reassoc]
theorem prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodComparison F A' B)] :
    inv (prodComparison F A B) ≫ F.map (f ▷ B) =
      (F.map f ▷ F.obj B) ≫ inv (prodComparison F A' B) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerRight]

end

lemma prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]
lemma prodComparison_id :
    prodComparison (𝟭 C) A B = 𝟙 (A ⊗ B) := lift_inl_inr

/-- The product comparison morphism from `F(A ⊗ -)` to `FA ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonNatTrans (A : C) :
    (curriedCotensor C).obj A ⋙ F ⟶ F ⋙ (curriedCotensor D).obj (F.obj A) where
  app B := prodComparison F A B
  naturality x y f := by
    apply hom_ext <;>
    simp only [Functor.comp_obj, curriedCotensor_obj_obj,
      Functor.comp_map, curriedCotensor_obj_map, Category.assoc, prodComparison_inl, whiskerLeft_inl,
      prodComparison_inr, prodComparison_inr_assoc, whiskerLeft_inr, ← F.map_comp]

theorem prodComparisonNatTrans_comp :
    prodComparisonNatTrans (F ⋙ G) A = Functor.whiskerRight (prodComparisonNatTrans F A) G ≫
      Functor.whiskerLeft F (prodComparisonNatTrans G (F.obj A)) := by
  ext; simp [prodComparison_comp]

@[simp]
lemma prodComparisonNatTrans_id :
    prodComparisonNatTrans (𝟭 C) A = 𝟙 _ := by ext; simp

/-- The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonBifunctorNatTrans :
    curriedCotensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ⟶
      F ⋙ curriedCotensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F where
  app A := prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;> simp [← Functor.map_comp]

variable {E : Type u₂} [Category.{v₂} E] [CartesianComonoidalCategory E] (G : D ⥤ E)

theorem prodComparisonBifunctorNatTrans_comp : prodComparisonBifunctorNatTrans (F ⋙ G) =
    Functor.whiskerRight
      (prodComparisonBifunctorNatTrans F) ((Functor.whiskeringRight _ _ _).obj G) ≫
        Functor.whiskerLeft F (Functor.whiskerRight (prodComparisonBifunctorNatTrans G)
          ((Functor.whiskeringLeft _ _ _).obj F)) := by
  ext; simp [prodComparison_comp]

instance (A : C) [∀ B, IsIso (prodComparison F A B)] : IsIso (prodComparisonNatTrans F A) := by
  letI : ∀ X, IsIso ((prodComparisonNatTrans F A).app X) := by assumption
  apply NatIso.isIso_of_isIso_app

instance [∀ A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctorNatTrans F) := by
  letI : ∀ X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ ↦ by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

open Limits
section PreservesLimitPairs

section
variable (A B)
variable [PreservesLimit (pair A B) F]

/-- If `F` preserves the limit of the pair `(A, B)`, then the binary fan given by
`(F.map inl A B, F.map (inr A B))` is a limit cone. -/
noncomputable def isLimitCartesianComonoidalCategoryOfPreservesLimits :
    IsLimit <| BinaryFan.mk (F.map (inl A B)) (F.map (inr A B)) :=
  mapIsLimitOfPreservesOfIsLimit F (inl _ _) (inr _ _) <|
    (cotensorProductIsBinaryProduct A B).ofIsoLimit <|
      isoBinaryFanMk (BinaryFan.mk (inl A B) (inr A B))

@[deprecated (since := "2025-05-15")]
alias isLimitChosenFiniteProductsOfPreservesLimits :=
  isLimitCartesianComonoidalCategoryOfPreservesLimits

/-- If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is an isomorphism.
-/
noncomputable def prodComparisonIso : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitCartesianComonoidalCategoryOfPreservesLimits F A B)
    (cotensorProductIsBinaryProduct _ _)

@[simp]
lemma prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B :=
  rfl

instance isIso_prodComparison_of_preservesLimit_pair : IsIso (prodComparison F A B) := by
  rw [← prodComparisonIso_hom]
  infer_instance

@[simp] lemma prodComparisonIso_id : prodComparisonIso (𝟭 C) A B = .refl _ := by ext <;> simp

@[simp]
lemma prodComparisonIso_comp [PreservesLimit (pair A B) (F ⋙ G)]
    [PreservesLimit (pair (F.obj A) (F.obj B)) G] :
    prodComparisonIso (F ⋙ G) A B =
      G.mapIso (prodComparisonIso F A B) ≪≫ prodComparisonIso G (F.obj A) (F.obj B) := by
  ext <;> simp [CartesianComonoidalCategory.prodComparison, ← G.map_comp]

end

/-- The natural isomorphism `F(A ⊗ -) ≅ FA ⊗ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes). -/
@[simps! hom inv]
noncomputable def prodComparisonNatIso (A : C) [∀ B, PreservesLimit (pair A B) F] :
    (curriedCotensor C).obj A ⋙ F ≅ F ⋙ (curriedCotensor D).obj (F.obj A) :=
  asIso (prodComparisonNatTrans F A)

/-- The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism. -/
@[simps! hom inv]
noncomputable def prodComparisonBifunctorNatIso [∀ A B, PreservesLimit (pair A B) F] :
    curriedCotensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ≅
      F ⋙ curriedCotensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F :=
  asIso (prodComparisonBifunctorNatTrans F)

end PreservesLimitPairs

section ProdComparisonIso

/-- If `prodComparison F A B` is an isomorphism, then `F` preserves the limit of `pair A B`. -/
lemma preservesLimit_pair_of_isIso_prodComparison (A B : C)
    [IsIso (prodComparison F A B)] :
    PreservesLimit (pair A B) F := by
  apply preservesLimit_of_preserves_limit_cone (cotensorProductIsBinaryProduct A B)
  refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((BinaryFan.mk (inl (F.obj A) (F.obj B)) (inr _ _)).extend (prodComparison F A B))
      (BinaryFan.ext (by exact Iso.refl _) ?_ ?_) |>.invFun
      (IsLimit.extendIso _ (cotensorProductIsBinaryProduct (F.obj A) (F.obj B)))
  · dsimp only [BinaryFan.inl]
    simp [pairComp]
  · dsimp only [BinaryFan.inr]
    simp [pairComp]

/-- If `prodComparison F A B` is an isomorphism for all `A B` then `F` preserves limits of shape
`Discrete (WalkingPair)`. -/
lemma preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    [∀ A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

end ProdComparisonIso

end prodComparison

end CartesianComonoidalCategoryComparison

/-- In a cartesian monoidal category, `cotensorLeft X` is naturally isomorphic `prod.functor.obj X`.
-/
noncomputable def cotensorLeftIsoProd [HasBinaryProducts C] (X : C) :
    ComonoidalCategory.cotensorLeft X ≅ prod.functor.obj X :=
  NatIso.ofComponents fun Y ↦
    (CartesianComonoidalCategory.cotensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit _)

open Limits

variable {P : ObjectProperty C}

-- TODO: Introduce `ClosedUnderFiniteProducts`?
/-- The restriction of a Cartesian-monoidal category along an object property that's closed under
finite products is Cartesian-monoidal. -/
@[simps!]
instance fullSubcategory
    [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
    [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)] :
    CartesianComonoidalCategory P.FullSubcategory where
  __ := ComonoidalCategory.fullSubcategory P
      (P.prop_of_isLimit isTerminalCotensorUnit (by simp))
      (fun X Y hX hY ↦ P.prop_of_isLimit (cotensorProductIsBinaryProduct X Y)
        (by rintro (_ | _) <;> assumption))
  isTerminalCotensorUnit := .ofUniqueHom (fun X ↦ ofUnit X.1) fun _ _ ↦ by ext
  inl X Y := inl X.1 Y.1
  inr X Y := inr X.1 Y.1
  cotensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (lift (C := C)) (lift_inl (C := C)) (lift_inr (C := C))
      (by rintro T f g m rfl rfl; symm; exact lift_comp_inl_inr _)
  inl_def X Y := inl_def X.1 Y.1
  inr_def X Y := inr_def X.1 Y.1

end CartesianComonoidalCategory

open ComonoidalCategory CartesianComonoidalCategory

variable
  {C : Type u₁} [Category.{v₁} C] [CartesianComonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianComonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianComonoidalCategory E]
  (F : C ⥤ D) (G : D ⥤ E) {X Y Z : C}

open Functor.LaxComonoidal Functor.OplaxComonoidal
open Limits (PreservesFiniteProducts)

namespace Functor.OplaxComonoidal
variable [F.OplaxComonoidal]

lemma η_of_cartesianComonoidalCategory :
    η F = CartesianComonoidalCategory.terminalComparison F := ofUnit_unique ..

@[reassoc (attr := simp)]
lemma δ_inl (X Y : C) :
    δ F X Y ≫ inl _ _ = F.map (inl _ _) := by
  trans F.map (X ◁ ofUnit Y) ≫ F.map (ρ_ X).hom
  · rw [← whiskerLeft_inl _ (F.map (ofUnit Y)), δ_natural_right_assoc]
    simp [← OplaxComonoidal.right_unitality_hom, rightUnitor_hom (F.obj X)]
  · simp [← Functor.map_comp, rightUnitor_hom]

@[reassoc (attr := simp)]
lemma δ_inr (X Y : C) :
    δ F X Y ≫ inr _ _ = F.map (inr _ _) := by
  trans F.map (ofUnit X ▷ Y) ≫ F.map (λ_ Y).hom
  · rw [← whiskerRight_inr (F.map (ofUnit X)), δ_natural_left_assoc]
    simp [← OplaxComonoidal.left_unitality_hom, leftUnitor_hom (F.obj Y)]
  · simp [← Functor.map_comp, leftUnitor_hom]

@[reassoc (attr := simp)]
lemma lift_δ (f : X ⟶ Y) (g : X ⟶ Z) : F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g) := by
  ext <;> simp [← map_comp]

lemma δ_of_cartesianComonoidalCategory (X Y : C) :
    δ F X Y = CartesianComonoidalCategory.prodComparison F X Y := by cat_disch

variable [PreservesFiniteProducts F]

instance : IsIso (η F) :=
  η_of_cartesianComonoidalCategory F ▸ terminalComparison_isIso_of_preservesLimits F

instance (X Y : C) : IsIso (δ F X Y) :=
  δ_of_cartesianComonoidalCategory F X Y ▸ isIso_prodComparison_of_preservesLimit_pair F X Y

omit [F.OplaxComonoidal] in
/-- Any functor between Cartesian-monoidal categories is oplax monoidal.

This is not made an instance because it would create a diamond for the oplax monoidal structure on
the identity and composition of functors. -/
def ofChosenFiniteProducts (F : C ⥤ D) : F.OplaxComonoidal where
  η := terminalComparison F
  δ X Y := prodComparison F X Y
  δ_natural_left f X := by ext <;> simp [← Functor.map_comp]
  δ_natural_right X g := by ext <;> simp [← Functor.map_comp]
  oplax_associativity _ _ _ := by ext <;> simp [← Functor.map_comp]
  oplax_left_unitality _ := by ext; simp [← Functor.map_comp]
  oplax_right_unitality _ := by ext; simp [← Functor.map_comp]

omit [F.OplaxComonoidal] in
/-- Any functor between Cartesian-monoidal categories is oplax monoidal in a unique way. -/
instance : Subsingleton F.OplaxComonoidal where
  allEq a b := by
    ext1
    · exact ofUnit_unique _ _
    · ext1; ext1; rw [δ_of_cartesianComonoidalCategory, δ_of_cartesianComonoidalCategory]

end OplaxComonoidal

namespace Comonoidal
variable [F.Comonoidal] [G.Comonoidal]

@[reassoc (attr := simp)]
lemma ofUnit_ε (X : C) : ofUnit (F.obj X) ≫ ε F = F.map (ofUnit X) := by
  rw [← cancel_mono (εIso F).inv]; exact ofUnit_unique ..

@[reassoc (attr := simp)]
lemma lift_μ (f : X ⟶ Y) (g : X ⟶ Z) : lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g) :=
  (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_inl (X Y : C) : μ F X Y ≫ F.map (inl X Y) = inl (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_inr (X Y : C) : μ F X Y ≫ F.map (inr X Y) = inr (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

attribute [-instance] Functor.LaxComonoidal.comp Functor.Comonoidal.instComp in
@[reassoc]
lemma μ_comp [(F ⋙ G).Comonoidal] (X Y : C) : μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y) := by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

variable [PreservesFiniteProducts F]

lemma ε_of_cartesianComonoidalCategory : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext

lemma μ_of_cartesianComonoidalCategory (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_cartesianComonoidalCategory F X Y

attribute [local instance] Functor.OplaxComonoidal.ofChosenFiniteProducts in
omit [F.Comonoidal] in
/-- A finite-product-preserving functor between Cartesian monoidal categories is monoidal.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Comonoidal :=
  .ofOplaxComonoidal F

instance : Subsingleton F.Comonoidal := (toOplaxComonoidal_injective F).subsingleton

end Comonoidal

namespace Comonoidal

instance [F.Comonoidal] : PreservesFiniteProducts F :=
  have (A B : _) : IsIso (CartesianComonoidalCategory.prodComparison F A B) :=
    δ_of_cartesianComonoidalCategory F A B ▸ inferInstance
  have : IsIso (CartesianComonoidalCategory.terminalComparison F) :=
    η_of_cartesianComonoidalCategory F ▸ inferInstance
  have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison F
  have := preservesLimit_empty_of_isIso_terminalComparison F
  have := Limits.preservesLimitsOfShape_pempty_of_preservesTerminal F
  .of_preserves_binary_and_terminal _

attribute [local instance] OplaxComonoidal.ofChosenFiniteProducts in
/--
A functor between Cartesian monoidal categories is monoidal iff it preserves finite products.
-/
lemma nonempty_monoidal_iff_preservesFiniteProducts :
    Nonempty F.Comonoidal ↔ PreservesFiniteProducts F :=
  ⟨fun ⟨_⟩ ↦ inferInstance, fun _ ↦ ⟨ofChosenFiniteProducts F⟩⟩

end Comonoidal

namespace Braided
variable [BraidedCategory C] [BraidedCategory D]

attribute [local instance] Functor.Comonoidal.ofChosenFiniteProducts in
/-- A finite-product-preserving functor between Cartesian monoidal categories is braided.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Braided where
  braided X Y := by rw [← cancel_mono (Comonoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]

instance : Subsingleton F.Braided := (Braided.toComonoidal_injective F).subsingleton

end Braided

@[deprecated (since := "2025-04-24")]
alias oplaxComonoidalOfChosenFiniteProducts := OplaxComonoidal.ofChosenFiniteProducts

@[deprecated (since := "2025-04-24")]
alias monoidalOfChosenFiniteProducts := Comonoidal.ofChosenFiniteProducts

@[deprecated (since := "2025-04-24")]
alias braidedOfChosenFiniteProducts := Braided.ofChosenFiniteProducts

namespace EssImageSubcategory
variable [F.Full] [F.Faithful] [PreservesFiniteProducts F] {T X Y Z : F.EssImageSubcategory}

lemma cotensor_obj (X Y : F.EssImageSubcategory) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

lemma lift_def (f : T ⟶ X) (g : T ⟶ Y) : lift f g = lift (T := T.1) f g := rfl

lemma associator_hom_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := rfl

lemma associator_inv_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv := rfl

lemma ofUnit_def (X : F.EssImageSubcategory) : ofUnit X = ofUnit X.obj := ofUnit_unique ..

end Functor.EssImageSubcategory

namespace NatTrans
variable (F G : C ⥤ D) [F.Comonoidal] [G.Comonoidal]

instance IsComonoidal.of_cartesianComonoidalCategory (α : F ⟶ G) : IsComonoidal α where
  unit := (cancel_mono (Functor.Comonoidal.εIso _).inv).1 (ofUnit_unique _ _)
  cotensor {X Y} := by
    rw [← cancel_mono (Functor.Comonoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Comonoidal.μIso _ _ _).inv]
    apply CartesianComonoidalCategory.hom_ext <;> simp

end NatTrans

end CategoryTheory
