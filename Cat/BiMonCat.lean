/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Basic

/-!
# Monoidal categories

A monoidal category is a category equipped with a cotensor product, unitors, and an associator.
In the definition, we provide the cotensor product as a pair of functions
* `cotensorObj : C → C → C`
* `cotensorHom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⨿' X₂) ⟶ (Y₁ ⨿' Y₂))`
and allow use of the overloaded notation `⨿'` for both.
The unitors and associator are provided componentwise.

The cotensor product can be expressed as a functor via `cotensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `leftUnitor_nat_iso`, `rightUnitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files after proving the coherence theorem,
e.g. `(λ'_ (𝟘_ C)).hom = (ρ'_ (𝟘_ C)).hom` in `CategoryTheory.Monoidal.CoherenceLemmas`.

## Implementation notes

In the definition of monoidal categories, we also provide the whiskering operators:
* `cowhiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⨿' Y₁ ⟶ X ⨿' Y₂`, denoted by `X ◁ᵒᵖ f`,
* `cowhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : X₁ ⨿' Y ⟶ X₂ ⨿' Y`, denoted by `f ▷ᵒᵖ Y`.
These are products of an object and a morphism (the terminology "whiskering"
is borrowed from 2-category theory). The cotensor product of morphisms `cotensorHom` can be defined
in terms of the whiskerings. There are two possible such definitions, which are related by
the exchange property of the whiskerings. These two definitions are accessed by `cotensorHom_def`
and `cotensorHom_def'`. By default, `cotensorHom` is defined so that `cotensorHom_def` holds
definitionally.

If you want to provide `cotensorHom` and define `cowhiskerLeft` and `cowhiskerRight` in terms of it,
you can use the alternative constructor `CategoryTheory.ComonoidalCategory.ofTensorHom`.

The whiskerings are useful when considering simp-normal forms of morphisms in monoidal categories.

### Simp-normal form for morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any morphisms into the simp-normal
form defined below. Rewriting into simp-normal form is especially useful in preprocessing
performed by the `coherence` tactic.

The simp-normal form of morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of morphisms like `f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅` such that each `fᵢ` is
  either a structural morphism (morphisms made up only of identities, associators, unitors)
  or a non-structural morphism, and
2. each non-structural morphism in the composition is of the form `X₁ ◁ᵒᵖ X₂ ◁ᵒᵖ X₃ ◁ᵒᵖ f ▷ᵒᵖ X₄ ▷ᵒᵖ X₅`,
  where each `Xᵢ` is an object that is not the identity or a cotensor and `f` is a non-structural
  morphism that is not the identity or a composite.

Note that `X₁ ◁ᵒᵖ X₂ ◁ᵒᵖ X₃ ◁ᵒᵖ f ▷ᵒᵖ X₄ ▷ᵒᵖ X₅` is actually `X₁ ◁ᵒᵖ (X₂ ◁ᵒᵖ (X₃ ◁ᵒᵖ ((f ▷ᵒᵖ X₄) ▷ᵒᵖ X₅)))`.

Currently, the simp lemmas don't rewrite `𝟙 X ⨿'ₘ f` and `f ⨿'ₘ 𝟙 Y` into `X ◁ᵒᵖ f` and `f ▷ᵒᵖ Y`,
respectively, since it requires a huge refactoring. We hope to add these simp lemmas soon.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/

universe v u

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`ComonoidalCategory`. -/
class ComonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried cotensor product of objects -/
  cotensorObj : C → C → C
  /-- left whiskering for morphisms -/
  cowhiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : cotensorObj X Y₁ ⟶ cotensorObj X Y₂
  /-- right whiskering for morphisms -/
  cowhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : cotensorObj X₁ Y ⟶ cotensorObj X₂ Y
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⨿'ₘ 𝟙 X₂ = 𝟙 (X₁ ⨿' X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  cotensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (cotensorObj X₁ X₂ ⟶ cotensorObj Y₁ Y₂) :=
    cowhiskerRight f X₂ ≫ cowhiskerLeft Y₁ g
  /-- The cotensor unity in the monoidal structure `𝟘_ C` -/
  cotensorUnit (C) : C
  /-- The associator isomorphism `(X ⨿' Y) ⨿' Z ≃ X ⨿' (Y ⨿' Z)` -/
  associator : ∀ X Y Z : C, cotensorObj (cotensorObj X Y) Z ≅ cotensorObj X (cotensorObj Y Z)
  /-- The left unitor: `𝟘_ C ⨿' X ≃ X` -/
  leftUnitor : ∀ X : C, cotensorObj cotensorUnit X ≅ X
  /-- The right unitor: `X ⨿' 𝟘_ C ≃ X` -/
  rightUnitor : ∀ X : C, cotensorObj X cotensorUnit ≅ X

namespace ComonoidalCategory

export ComonoidalCategoryStruct
  (cotensorObj cowhiskerLeft cowhiskerRight cotensorHom cotensorUnit associator leftUnitor rightUnitor)

end ComonoidalCategory

namespace ComonoidalCategory

/-- Notation for `cotensorObj`, the cotensor product of objects in a monoidal category -/
scoped infixr:70 " ⨿' " => ComonoidalCategoryStruct.cotensorObj

/-- Notation for the `cowhiskerLeft` operator of monoidal categories -/
scoped infixr:81 " ◁ᵒᵖ " => ComonoidalCategoryStruct.cowhiskerLeft

/-- Notation for the `cowhiskerRight` operator of monoidal categories -/
scoped infixl:81 " ▷ᵒᵖ " => ComonoidalCategoryStruct.cowhiskerRight

/-- Notation for `cotensorHom`, the cotensor product of morphisms in a monoidal category -/
scoped infixr:70 " ⨿'ₘ " => ComonoidalCategoryStruct.cotensorHom
-- TODO: Try setting this notation to `⨿'` if the elaborator is improved and performs
-- better than currently on overloaded notations.

/-- Notation for `cotensorUnit`, the two-sided identity of `⨿'` -/
scoped notation "𝟘_ " C:arg => ComonoidalCategoryStruct.cotensorUnit C

/-- Notation for the monoidal `associator`: `(X ⨿' Y) ⨿' Z ≃ X ⨿' (Y ⨿' Z)` -/
scoped notation "α'_" => ComonoidalCategoryStruct.associator

/-- Notation for the `leftUnitor`: `𝟘_C ⨿' X ≃ X` -/
scoped notation "λ'_" => ComonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⨿' 𝟘_C ≃ X` -/
scoped notation "ρ'_" => ComonoidalCategoryStruct.rightUnitor

/-- The property that the pentagon relation is satisfied by four objects
in a category equipped with a `ComonoidalCategoryStruct`. -/
def Pentagon {C : Type u} [Category.{v} C] [ComonoidalCategoryStruct C]
    (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  (α'_ Y₁ Y₂ Y₃).hom ▷ᵒᵖ Y₄ ≫ (α'_ Y₁ (Y₂ ⨿' Y₃) Y₄).hom ≫ Y₁ ◁ᵒᵖ (α'_ Y₂ Y₃ Y₄).hom =
    (α'_ (Y₁ ⨿' Y₂) Y₃ Y₄).hom ≫ (α'_ Y₁ Y₂ (Y₃ ⨿' Y₄)).hom

end ComonoidalCategory

open ComonoidalCategory

/--
In a monoidal category, we can take the cotensor product of objects, `X ⨿' Y` and of morphisms
`f ⨿'ₘ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α'_ X Y Z : (X ⨿' Y) ⨿' Z ≅ X ⨿' (Y ⨿' Z)`. There is a cotensor unit `𝟘_ C`,
with specified left and right unitor isomorphisms `λ'_ X : 𝟘_ C ⨿' X ≅ X` and `ρ'_ X : X ⨿' 𝟘_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations. -/
@[stacks 0FFK]
-- Porting note: The Mathport did not translate the temporary notation
class ComonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends ComonoidalCategoryStruct C where
  cotensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⨿'ₘ g = (f ▷ᵒᵖ X₂) ≫ (Y₁ ◁ᵒᵖ g) := by
      cat_disch
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⨿'ₘ 𝟙 X₂ = 𝟙 (X₁ ⨿' X₂)` -/
  id_cotensorHom_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⨿'ₘ 𝟙 X₂ = 𝟙 (X₁ ⨿' X₂) := by cat_disch
  /--
  Composition of cotensor products is cotensor product of compositions:
  `(f₁ ⨿'ₘ f₂) ≫ (g₁ ⨿'ₘ g₂) = (f₁ ≫ g₁) ⨿'ₘ (f₂ ≫ g₂)`
  -/
  cotensorHom_comp_cotensorHom :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⨿'ₘ f₂) ≫ (g₁ ⨿'ₘ g₂) = (f₁ ≫ g₁) ⨿'ₘ (f₂ ≫ g₂) := by
    cat_disch
  cowhiskerLeft_id : ∀ (X Y : C), X ◁ᵒᵖ 𝟙 Y = 𝟙 (X ⨿' Y) := by
    cat_disch
  id_cowhiskerRight : ∀ (X Y : C), 𝟙 X ▷ᵒᵖ Y = 𝟙 (X ⨿' Y) := by
    cat_disch
  /-- Naturality of the associator isomorphism: `(f₁ ⨿'ₘ f₂) ⨿'ₘ f₃ ≃ f₁ ⨿'ₘ (f₂ ⨿'ₘ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⨿'ₘ f₂) ⨿'ₘ f₃) ≫ (α'_ Y₁ Y₂ Y₃).hom = (α'_ X₁ X₂ X₃).hom ≫ (f₁ ⨿'ₘ (f₂ ⨿'ₘ f₃)) := by
    cat_disch
  /--
  Naturality of the left unitor, commutativity of `𝟘_ C ⨿' X ⟶ 𝟘_ C ⨿' Y ⟶ Y` and `𝟘_ C ⨿' X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟘_ _ ◁ᵒᵖ f ≫ (λ'_ Y).hom = (λ'_ X).hom ≫ f := by
    cat_disch
  /--
  Naturality of the right unitor: commutativity of `X ⨿' 𝟘_ C ⟶ Y ⨿' 𝟘_ C ⟶ Y` and `X ⨿' 𝟘_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ᵒᵖ 𝟘_ _ ≫ (ρ'_ Y).hom = (ρ'_ X).hom ≫ f := by
    cat_disch
  /--
  The pentagon identity relating the isomorphism between `X ⨿' (Y ⨿' (Z ⨿' W))` and `((X ⨿' Y) ⨿' Z) ⨿' W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      (α'_ W X Y).hom ▷ᵒᵖ Z ≫ (α'_ W (X ⨿' Y) Z).hom ≫ W ◁ᵒᵖ (α'_ X Y Z).hom =
        (α'_ (W ⨿' X) Y Z).hom ≫ (α'_ W X (Y ⨿' Z)).hom := by
    cat_disch
  /--
  The identity relating the isomorphisms between `X ⨿' (𝟘_ C ⨿' Y)`, `(X ⨿' 𝟘_ C) ⨿' Y` and `X ⨿' Y`
  -/
  triangle :
    ∀ X Y : C, (α'_ X (𝟘_ _) Y).hom ≫ X ◁ᵒᵖ (λ'_ Y).hom = (ρ'_ X).hom ▷ᵒᵖ Y := by
    cat_disch

attribute [reassoc] ComonoidalCategory.cotensorHom_def
attribute [reassoc, simp] ComonoidalCategory.cowhiskerLeft_id
attribute [reassoc, simp] ComonoidalCategory.id_cowhiskerRight
attribute [reassoc (attr := simp)] ComonoidalCategory.cotensorHom_comp_cotensorHom
attribute [reassoc] ComonoidalCategory.associator_naturality
attribute [reassoc] ComonoidalCategory.leftUnitor_naturality
attribute [reassoc] ComonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] ComonoidalCategory.pentagon
attribute [reassoc (attr := simp)] ComonoidalCategory.triangle

namespace ComonoidalCategory

variable {C : Type u} [𝒞 : Category.{v} C] [ComonoidalCategory C]

@[simp]
theorem id_cotensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⨿'ₘ f = X ◁ᵒᵖ f := by
  simp [cotensorHom_def]

@[simp]
theorem cotensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⨿'ₘ 𝟙 Y = f ▷ᵒᵖ Y := by
  simp [cotensorHom_def]

@[reassoc, simp]
theorem cowhiskerLeft_comp (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    W ◁ᵒᵖ (f ≫ g) = W ◁ᵒᵖ f ≫ W ◁ᵒᵖ g := by
  simp [← id_cotensorHom]

@[reassoc, simp]
theorem id_cowhiskerLeft {X Y : C} (f : X ⟶ Y) :
    𝟘_ C ◁ᵒᵖ f = (λ'_ X).hom ≫ f ≫ (λ'_ Y).inv := by
  rw [← assoc, ← leftUnitor_naturality]; simp

@[reassoc, simp]
theorem cotensor_cowhiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⨿' Y) ◁ᵒᵖ f = (α'_ X Y Z).hom ≫ X ◁ᵒᵖ Y ◁ᵒᵖ f ≫ (α'_ X Y Z').inv := by
  simp only [← id_cotensorHom]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc, simp]
theorem comp_cowhiskerRight {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) :
    (f ≫ g) ▷ᵒᵖ Z = f ▷ᵒᵖ Z ≫ g ▷ᵒᵖ Z := by
  simp [← cotensorHom_id]

@[reassoc, simp]
theorem cowhiskerRight_id {X Y : C} (f : X ⟶ Y) :
    f ▷ᵒᵖ 𝟘_ C = (ρ'_ X).hom ≫ f ≫ (ρ'_ Y).inv := by
  rw [← assoc, ← rightUnitor_naturality]; simp

@[reassoc, simp]
theorem cowhiskerRight_cotensor {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ᵒᵖ (Y ⨿' Z) = (α'_ X Y Z).inv ≫ f ▷ᵒᵖ Y ▷ᵒᵖ Z ≫ (α'_ X' Y Z).hom := by
  simp only [← cotensorHom_id]
  rw [associator_naturality]
  simp

@[reassoc, simp]
theorem whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ᵒᵖ f) ▷ᵒᵖ Z = (α'_ X Y Z).hom ≫ X ◁ᵒᵖ f ▷ᵒᵖ Z ≫ (α'_ X Y' Z).inv := by
  simp only [← id_cotensorHom, ← cotensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc]
theorem whisker_exchange {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ᵒᵖ g ≫ f ▷ᵒᵖ Z = f ▷ᵒᵖ Y ≫ X ◁ᵒᵖ g := by
  simp [← id_cotensorHom, ← cotensorHom_id]

@[reassoc]
theorem cotensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⨿'ₘ g = X₁ ◁ᵒᵖ g ≫ f ▷ᵒᵖ Y₂ :=
  whisker_exchange f g ▸ cotensorHom_def f g

@[reassoc]
theorem cowhiskerLeft_comp_cotensorHom {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (V ◁ᵒᵖ g) ≫ (f ⨿'ₘ h) = f ⨿'ₘ (g ≫ h) := by
  simp [cotensorHom_def']

@[reassoc]
theorem cowhiskerRight_comp_cotensorHom {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ▷ᵒᵖ V) ≫ (g ⨿'ₘ h) = (f ≫ g) ⨿'ₘ h := by
  simp [cotensorHom_def]

@[reassoc]
theorem cotensorHom_comp_cowhiskerLeft {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⨿'ₘ g) ≫ (W ◁ᵒᵖ h) = f ⨿'ₘ (g ≫ h) := by
  simp [cotensorHom_def]

@[reassoc]
theorem cotensorHom_comp_cowhiskerRight {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ⨿'ₘ h) ≫ (g ▷ᵒᵖ W) = (f ≫ g) ⨿'ₘ h := by
  simp [cotensorHom_def, whisker_exchange]

@[reassoc] lemma leftUnitor_inv_comp_cotensorHom {X Y Z : C} (f : 𝟘_ C ⟶ Y) (g : X ⟶ Z) :
    (λ'_ X).inv ≫ (f ⨿'ₘ g) = g ≫ (λ'_ Z).inv ≫ f ▷ᵒᵖ Z := by simp [cotensorHom_def']

@[reassoc] lemma rightUnitor_inv_comp_cotensorHom {X Y Z : C} (f : X ⟶ Y) (g : 𝟘_ C ⟶ Z) :
    (ρ'_ X).inv ≫ (f ⨿'ₘ g) = f ≫ (ρ'_ Y).inv ≫ Y ◁ᵒᵖ g := by simp [cotensorHom_def]

@[reassoc (attr := simp)]
theorem cowhiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ᵒᵖ f.hom ≫ X ◁ᵒᵖ f.inv = 𝟙 (X ⨿' Y) := by
  rw [← cowhiskerLeft_comp, hom_inv_id, cowhiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_cowhiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.hom ▷ᵒᵖ Z ≫ f.inv ▷ᵒᵖ Z = 𝟙 (X ⨿' Z) := by
  rw [← comp_cowhiskerRight, hom_inv_id, id_cowhiskerRight]

@[reassoc (attr := simp)]
theorem cowhiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ᵒᵖ f.inv ≫ X ◁ᵒᵖ f.hom = 𝟙 (X ⨿' Z) := by
  rw [← cowhiskerLeft_comp, inv_hom_id, cowhiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_cowhiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.inv ▷ᵒᵖ Z ≫ f.hom ▷ᵒᵖ Z = 𝟙 (Y ⨿' Z) := by
  rw [← comp_cowhiskerRight, inv_hom_id, id_cowhiskerRight]

@[reassoc (attr := simp)]
theorem cowhiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ᵒᵖ f ≫ X ◁ᵒᵖ inv f = 𝟙 (X ⨿' Y) := by
  rw [← cowhiskerLeft_comp, IsIso.hom_inv_id, cowhiskerLeft_id]

@[reassoc (attr := simp)]
theorem hom_inv_cowhiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    f ▷ᵒᵖ Z ≫ inv f ▷ᵒᵖ Z = 𝟙 (X ⨿' Z) := by
  rw [← comp_cowhiskerRight, IsIso.hom_inv_id, id_cowhiskerRight]

@[reassoc (attr := simp)]
theorem cowhiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ᵒᵖ inv f ≫ X ◁ᵒᵖ f = 𝟙 (X ⨿' Z) := by
  rw [← cowhiskerLeft_comp, IsIso.inv_hom_id, cowhiskerLeft_id]

@[reassoc (attr := simp)]
theorem inv_hom_cowhiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    inv f ▷ᵒᵖ Z ≫ f ▷ᵒᵖ Z = 𝟙 (Y ⨿' Z) := by
  rw [← comp_cowhiskerRight, IsIso.inv_hom_id, id_cowhiskerRight]

/-- The left whiskering of an isomorphism is an isomorphism. -/
@[simps]
def cowhiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X ⨿' Y ≅ X ⨿' Z where
  hom := X ◁ᵒᵖ f.hom
  inv := X ◁ᵒᵖ f.inv

instance cowhiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ᵒᵖ f) :=
  (cowhiskerLeftIso X (asIso f)).isIso_hom

@[simp]
theorem inv_cowhiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ᵒᵖ f) = X ◁ᵒᵖ inv f := by
  cat_disch

@[simp]
lemma cowhiskerLeftIso_refl (W X : C) :
    cowhiskerLeftIso W (Iso.refl X) = Iso.refl (W ⨿' X) :=
  Iso.ext (cowhiskerLeft_id W X)

@[simp]
lemma cowhiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
    cowhiskerLeftIso W (f ≪≫ g) = cowhiskerLeftIso W f ≪≫ cowhiskerLeftIso W g :=
  Iso.ext (cowhiskerLeft_comp W f.hom g.hom)

@[simp]
lemma cowhiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) :
    (cowhiskerLeftIso W f).symm = cowhiskerLeftIso W f.symm := rfl

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[simps!]
def cowhiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X ⨿' Z ≅ Y ⨿' Z where
  hom := f.hom ▷ᵒᵖ Z
  inv := f.inv ▷ᵒᵖ Z

instance cowhiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ᵒᵖ Z) :=
  (cowhiskerRightIso (asIso f) Z).isIso_hom

@[simp]
theorem inv_cowhiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ᵒᵖ Z) = inv f ▷ᵒᵖ Z := by
  cat_disch

@[simp]
lemma cowhiskerRightIso_refl (X W : C) :
    cowhiskerRightIso (Iso.refl X) W = Iso.refl (X ⨿' W) :=
  Iso.ext (id_cowhiskerRight X W)

@[simp]
lemma cowhiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) :
    cowhiskerRightIso (f ≪≫ g) W = cowhiskerRightIso f W ≪≫ cowhiskerRightIso g W :=
  Iso.ext (comp_cowhiskerRight f.hom g.hom W)

@[simp]
lemma cowhiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) :
    (cowhiskerRightIso f W).symm = cowhiskerRightIso f.symm W := rfl

/-- The cotensor product of two isomorphisms is an isomorphism. -/
@[simps]
def cotensorIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⨿' X' ≅ Y ⨿' Y' where
  hom := f.hom ⨿'ₘ g.hom
  inv := f.inv ⨿'ₘ g.inv
  hom_inv_id := by simp [Iso.hom_inv_id, Iso.hom_inv_id]
  inv_hom_id := by simp [Iso.inv_hom_id, Iso.inv_hom_id]

/-- Notation for `cotensorIso`, the cotensor product of isomorphisms -/
scoped infixr:70 " ⨿'ᵢ " => cotensorIso
-- TODO: Try setting this notation to `⨿'` if the elaborator is improved and performs
-- better than currently on overloaded notations.

theorem cotensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⨿'ᵢ g = cowhiskerRightIso f X' ≪≫ cowhiskerLeftIso Y g :=
  Iso.ext (cotensorHom_def f.hom g.hom)

theorem cotensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⨿'ᵢ g = cowhiskerLeftIso X g ≪≫ cowhiskerRightIso f Y' :=
  Iso.ext (cotensorHom_def' f.hom g.hom)

instance cotensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⨿'ₘ g) :=
  (asIso f ⨿'ᵢ asIso g).isIso_hom

@[simp]
theorem inv_cotensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⨿'ₘ g) = inv f ⨿'ₘ inv g := by
  simp [cotensorHom_def, whisker_exchange]

variable {W X Y Z : C}

theorem cowhiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P → (Y ⟶ Z)) (f' : ¬P → (Y ⟶ Z)) :
      X ◁ᵒᵖ (if h : P then f h else f' h) = if h : P then X ◁ᵒᵖ f h else X ◁ᵒᵖ f' h := by
  split_ifs <;> rfl

theorem dite_cowhiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (Z : C) :
      (if h : P then f h else f' h) ▷ᵒᵖ Z = if h : P then f h ▷ᵒᵖ Z else f' h ▷ᵒᵖ Z := by
  split_ifs <;> rfl

theorem cotensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⨿'ₘ if h : P then g h else g' h) =
    if h : P then f ⨿'ₘ g h else f ⨿'ₘ g' h := by split_ifs <;> rfl

theorem dite_cotensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⨿'ₘ f =
    if h : P then g h ⨿'ₘ f else g' h ⨿'ₘ f := by split_ifs <;> rfl

@[simp]
theorem cowhiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) :
    X ◁ᵒᵖ eqToHom f = eqToHom (congr_arg₂ cotensorObj rfl f) := by
  cases f
  simp only [cowhiskerLeft_id, eqToHom_refl]

@[simp]
theorem eqToHom_cowhiskerRight {X Y : C} (f : X = Y) (Z : C) :
    eqToHom f ▷ᵒᵖ Z = eqToHom (congr_arg₂ cotensorObj f rfl) := by
  cases f
  simp only [id_cowhiskerRight, eqToHom_refl]

@[reassoc]
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ᵒᵖ Y ▷ᵒᵖ Z ≫ (α'_ X' Y Z).hom = (α'_ X Y Z).hom ≫ f ▷ᵒᵖ (Y ⨿' Z) := by simp

@[reassoc]
theorem associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ᵒᵖ (Y ⨿' Z) ≫ (α'_ X' Y Z).inv = (α'_ X Y Z).inv ≫ f ▷ᵒᵖ Y ▷ᵒᵖ Z := by simp

@[reassoc]
theorem cowhiskerRight_cotensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ᵒᵖ Y ▷ᵒᵖ Z = (α'_ X Y Z).hom ≫ f ▷ᵒᵖ (Y ⨿' Z) ≫ (α'_ X' Y Z).inv := by simp

@[reassoc]
theorem associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ᵒᵖ f) ▷ᵒᵖ Z ≫ (α'_ X Y' Z).hom = (α'_ X Y Z).hom ≫ X ◁ᵒᵖ f ▷ᵒᵖ Z := by simp

@[reassoc]
theorem associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ᵒᵖ f ▷ᵒᵖ Z ≫ (α'_ X Y' Z).inv = (α'_ X Y Z).inv ≫ (X ◁ᵒᵖ f) ▷ᵒᵖ Z := by simp

@[reassoc]
theorem whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ᵒᵖ f ▷ᵒᵖ Z = (α'_ X Y Z).inv ≫ (X ◁ᵒᵖ f) ▷ᵒᵖ Z ≫ (α'_ X Y' Z).hom := by simp

@[reassoc]
theorem associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⨿' Y) ◁ᵒᵖ f ≫ (α'_ X Y Z').hom = (α'_ X Y Z).hom ≫ X ◁ᵒᵖ Y ◁ᵒᵖ f := by simp

@[reassoc]
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ᵒᵖ Y ◁ᵒᵖ f ≫ (α'_ X Y Z').inv = (α'_ X Y Z).inv ≫ (X ⨿' Y) ◁ᵒᵖ f := by simp

@[reassoc]
theorem cotensor_cowhiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ᵒᵖ Y ◁ᵒᵖ f = (α'_ X Y Z).inv ≫ (X ⨿' Y) ◁ᵒᵖ f ≫ (α'_ X Y Z').hom := by simp

@[reassoc]
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (λ'_ Y).inv = (λ'_ X).inv ≫ _ ◁ᵒᵖ f := by simp

@[reassoc]
theorem id_cowhiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (λ'_ X).inv ≫ 𝟘_ C ◁ᵒᵖ f ≫ (λ'_ X').hom := by
  simp only [id_cowhiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ'_ X').inv = (ρ'_ X).inv ≫ f ▷ᵒᵖ _ := by simp

@[reassoc]
theorem cowhiskerRight_id_symm {X Y : C} (f : X ⟶ Y) :
    f = (ρ'_ X).inv ≫ f ▷ᵒᵖ 𝟘_ C ≫ (ρ'_ Y).hom := by
  simp

theorem cowhiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟘_ C ◁ᵒᵖ f = 𝟘_ C ◁ᵒᵖ g ↔ f = g := by simp

theorem cowhiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ᵒᵖ 𝟘_ C = g ▷ᵒᵖ 𝟘_ C ↔ f = g := by simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/

section

@[reassoc (attr := simp)]
theorem pentagon_inv :
    W ◁ᵒᵖ (α'_ X Y Z).inv ≫ (α'_ W (X ⨿' Y) Z).inv ≫ (α'_ W X Y).inv ▷ᵒᵖ Z =
      (α'_ W X (Y ⨿' Z)).inv ≫ (α'_ (W ⨿' X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_hom_inv :
    (α'_ W (X ⨿' Y) Z).inv ≫ (α'_ W X Y).inv ▷ᵒᵖ Z ≫ (α'_ (W ⨿' X) Y Z).hom =
      W ◁ᵒᵖ (α'_ X Y Z).hom ≫ (α'_ W X (Y ⨿' Z)).inv := by
  rw [← cancel_epi (W ◁ᵒᵖ (α'_ X Y Z).inv), ← cancel_mono (α'_ (W ⨿' X) Y Z).inv]
  simp

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_inv :
    (α'_ (W ⨿' X) Y Z).inv ≫ (α'_ W X Y).hom ▷ᵒᵖ Z ≫ (α'_ W (X ⨿' Y) Z).hom =
      (α'_ W X (Y ⨿' Z)).hom ≫ W ◁ᵒᵖ (α'_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_inv :
    W ◁ᵒᵖ (α'_ X Y Z).hom ≫ (α'_ W X (Y ⨿' Z)).inv ≫ (α'_ (W ⨿' X) Y Z).inv =
      (α'_ W (X ⨿' Y) Z).inv ≫ (α'_ W X Y).inv ▷ᵒᵖ Z := by
  simp [← cancel_epi (W ◁ᵒᵖ (α'_ X Y Z).inv)]

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_hom_hom :
    (α'_ (W ⨿' X) Y Z).hom ≫ (α'_ W X (Y ⨿' Z)).hom ≫ W ◁ᵒᵖ (α'_ X Y Z).inv =
      (α'_ W X Y).hom ▷ᵒᵖ Z ≫ (α'_ W (X ⨿' Y) Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_hom_inv_inv_inv_hom :
    (α'_ W X (Y ⨿' Z)).hom ≫ W ◁ᵒᵖ (α'_ X Y Z).inv ≫ (α'_ W (X ⨿' Y) Z).inv =
      (α'_ (W ⨿' X) Y Z).inv ≫ (α'_ W X Y).hom ▷ᵒᵖ Z := by
  rw [← cancel_epi (α'_ W X (Y ⨿' Z)).inv, ← cancel_mono ((α'_ W X Y).inv ▷ᵒᵖ Z)]
  simp

@[reassoc (attr := simp)]
theorem pentagon_hom_hom_inv_inv_hom :
    (α'_ W (X ⨿' Y) Z).hom ≫ W ◁ᵒᵖ (α'_ X Y Z).hom ≫ (α'_ W X (Y ⨿' Z)).inv =
      (α'_ W X Y).inv ▷ᵒᵖ Z ≫ (α'_ (W ⨿' X) Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem pentagon_inv_hom_hom_hom_hom :
    (α'_ W X Y).inv ▷ᵒᵖ Z ≫ (α'_ (W ⨿' X) Y Z).hom ≫ (α'_ W X (Y ⨿' Z)).hom =
      (α'_ W (X ⨿' Y) Z).hom ≫ W ◁ᵒᵖ (α'_ X Y Z).hom := by
  simp [← cancel_epi ((α'_ W X Y).hom ▷ᵒᵖ Z)]

@[reassoc (attr := simp)]
theorem pentagon_inv_inv_hom_inv_inv :
    (α'_ W X (Y ⨿' Z)).inv ≫ (α'_ (W ⨿' X) Y Z).inv ≫ (α'_ W X Y).hom ▷ᵒᵖ Z =
      W ◁ᵒᵖ (α'_ X Y Z).inv ≫ (α'_ W (X ⨿' Y) Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right (X Y : C) :
    (α'_ X (𝟘_ C) Y).inv ≫ ((ρ'_ X).hom ▷ᵒᵖ Y) = X ◁ᵒᵖ (λ'_ Y).hom := by
  rw [← triangle, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_right_inv (X Y : C) :
    (ρ'_ X).inv ▷ᵒᵖ Y ≫ (α'_ X (𝟘_ C) Y).hom = X ◁ᵒᵖ (λ'_ Y).inv := by
  simp [← cancel_mono (X ◁ᵒᵖ (λ'_ Y).hom)]

@[reassoc (attr := simp)]
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (X ◁ᵒᵖ (λ'_ Y).inv) ≫ (α'_ X (𝟘_ C) Y).inv = (ρ'_ X).inv ▷ᵒᵖ Y := by
  simp [← cancel_mono ((ρ'_ X).hom ▷ᵒᵖ Y)]

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_cowhiskerRight X Y : 𝟙 X ▷ᵒᵖ Y = 𝟙 (X ⨿' Y)`.
-/
@[reassoc, simp]
theorem leftUnitor_cowhiskerRight (X Y : C) :
    (λ'_ X).hom ▷ᵒᵖ Y = (α'_ (𝟘_ C) X Y).hom ≫ (λ'_ (X ⨿' Y)).hom := by
  rw [← cowhiskerLeft_iff, cowhiskerLeft_comp, ← cancel_epi (α'_ _ _ _).hom, ←
      cancel_epi ((α'_ _ _ _).hom ▷ᵒᵖ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_cowhiskerRight_assoc, triangle, associator_naturality_left]

@[reassoc, simp]
theorem leftUnitor_inv_cowhiskerRight (X Y : C) :
    (λ'_ X).inv ▷ᵒᵖ Y = (λ'_ (X ⨿' Y)).inv ≫ (α'_ (𝟘_ C) X Y).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
theorem cowhiskerLeft_rightUnitor (X Y : C) :
    X ◁ᵒᵖ (ρ'_ Y).hom = (α'_ X Y (𝟘_ C)).inv ≫ (ρ'_ (X ⨿' Y)).hom := by
  rw [← cowhiskerRight_iff, comp_cowhiskerRight, ← cancel_epi (α'_ _ _ _).inv, ←
      cancel_epi (X ◁ᵒᵖ (α'_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← cowhiskerLeft_comp_assoc, triangle_assoc_comp_right,
      associator_inv_naturality_right]

@[reassoc, simp]
theorem cowhiskerLeft_rightUnitor_inv (X Y : C) :
    X ◁ᵒᵖ (ρ'_ Y).inv = (ρ'_ (X ⨿' Y)).inv ≫ (α'_ X Y (𝟘_ C)).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc]
theorem leftUnitor_cotensor_hom (X Y : C) :
    (λ'_ (X ⨿' Y)).hom = (α'_ (𝟘_ C) X Y).inv ≫ (λ'_ X).hom ▷ᵒᵖ Y := by simp

@[deprecated (since := "2025-06-24")] alias leftUnitor_cotensor := leftUnitor_cotensor_hom

@[reassoc]
theorem leftUnitor_cotensor_inv (X Y : C) :
    (λ'_ (X ⨿' Y)).inv = (λ'_ X).inv ▷ᵒᵖ Y ≫ (α'_ (𝟘_ C) X Y).hom := by simp

@[reassoc]
theorem rightUnitor_cotensor_hom (X Y : C) :
    (ρ'_ (X ⨿' Y)).hom = (α'_ X Y (𝟘_ C)).hom ≫ X ◁ᵒᵖ (ρ'_ Y).hom := by simp

@[deprecated (since := "2025-06-24")] alias rightUnitor_cotensor := rightUnitor_cotensor_hom

@[reassoc]
theorem rightUnitor_cotensor_inv (X Y : C) :
    (ρ'_ (X ⨿' Y)).inv = X ◁ᵒᵖ (ρ'_ Y).inv ≫ (α'_ X Y (𝟘_ C)).inv := by simp

end

@[reassoc]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⨿'ₘ g ⨿'ₘ h) ≫ (α'_ X' Y' Z').inv = (α'_ X Y Z).inv ≫ ((f ⨿'ₘ g) ⨿'ₘ h) := by
  simp [cotensorHom_def]

@[reassoc, simp]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⨿'ₘ g) ⨿'ₘ h = (α'_ X Y Z).hom ≫ (f ⨿'ₘ g ⨿'ₘ h) ≫ (α'_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

@[reassoc]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⨿'ₘ g ⨿'ₘ h = (α'_ X Y Z).inv ≫ ((f ⨿'ₘ g) ⨿'ₘ h) ≫ (α'_ X' Y' Z').hom := by
  rw [associator_naturality, inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
theorem id_cotensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⨿' Y) ⨿'ₘ h) ≫ (α'_ X Y Z').hom = (α'_ X Y Z).hom ≫ (𝟙 X ⨿'ₘ 𝟙 Y ⨿'ₘ h) := by
  rw [← id_cotensorHom_id, associator_naturality]

@[reassoc]
theorem id_cotensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⨿'ₘ 𝟙 (Y ⨿' Z)) ≫ (α'_ X' Y Z).inv = (α'_ X Y Z).inv ≫ ((f ⨿'ₘ 𝟙 Y) ⨿'ₘ 𝟙 Z) := by
  rw [← id_cotensorHom_id, associator_inv_naturality]

@[reassoc]
theorem hom_inv_id_cotensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⨿'ₘ g) ≫ (f.inv ⨿'ₘ h) = (𝟙 V ⨿'ₘ g) ≫ (𝟙 V ⨿'ₘ h) := by simp

@[reassoc]
theorem inv_hom_id_cotensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⨿'ₘ g) ≫ (f.hom ⨿'ₘ h) = (𝟙 W ⨿'ₘ g) ≫ (𝟙 W ⨿'ₘ h) := by simp

@[reassoc]
theorem cotensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⨿'ₘ f.hom) ≫ (h ⨿'ₘ f.inv) = (g ⨿'ₘ 𝟙 V) ≫ (h ⨿'ₘ 𝟙 V) := by simp

@[reassoc]
theorem cotensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⨿'ₘ f.inv) ≫ (h ⨿'ₘ f.hom) = (g ⨿'ₘ 𝟙 W) ≫ (h ⨿'ₘ 𝟙 W) := by simp

@[reassoc]
theorem hom_inv_id_cotensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⨿'ₘ g) ≫ (inv f ⨿'ₘ h) = (𝟙 V ⨿'ₘ g) ≫ (𝟙 V ⨿'ₘ h) := by simp

@[reassoc]
theorem inv_hom_id_cotensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⨿'ₘ g) ≫ (f ⨿'ₘ h) = (𝟙 W ⨿'ₘ g) ≫ (𝟙 W ⨿'ₘ h) := by simp

@[reassoc]
theorem cotensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⨿'ₘ f) ≫ (h ⨿'ₘ inv f) = (g ⨿'ₘ 𝟙 V) ≫ (h ⨿'ₘ 𝟙 V) := by simp

@[reassoc]
theorem cotensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⨿'ₘ inv f) ≫ (h ⨿'ₘ f) = (g ⨿'ₘ 𝟙 W) ≫ (h ⨿'ₘ 𝟙 W) := by simp

/--
A constructor for monoidal categories that requires `cotensorHom` instead of `cowhiskerLeft` and
`cowhiskerRight`.
-/
abbrev ofTensorHom [ComonoidalCategoryStruct C]
    (id_cotensorHom_id : ∀ X₁ X₂ : C, cotensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (cotensorObj X₁ X₂) := by
      cat_disch)
    (id_cotensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), cotensorHom (𝟙 X) f = cowhiskerLeft X f := by
      cat_disch)
    (cotensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), cotensorHom f (𝟙 Y) = cowhiskerRight f Y := by
      cat_disch)
    (cotensorHom_comp_cotensorHom :
      ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        (f₁ ⨿'ₘ f₂) ≫ (g₁ ⨿'ₘ g₂) = (f₁ ≫ g₁) ⨿'ₘ (f₂ ≫ g₂) := by
          cat_disch)
    (associator_naturality :
      ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        cotensorHom (cotensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ cotensorHom f₁ (cotensorHom f₂ f₃) := by
            cat_disch)
    (leftUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        cotensorHom (𝟙 (𝟘_ C)) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
          cat_disch)
    (rightUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        cotensorHom f (𝟙 (𝟘_ C)) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
          cat_disch)
    (pentagon :
      ∀ W X Y Z : C,
        cotensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (cotensorObj X Y) Z).hom ≫ cotensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (cotensorObj W X) Y Z).hom ≫ (associator W X (cotensorObj Y Z)).hom := by
            cat_disch)
    (triangle :
      ∀ X Y : C,
        (associator X (𝟘_ C) Y).hom ≫ cotensorHom (𝟙 X) (leftUnitor Y).hom =
          cotensorHom (rightUnitor X).hom (𝟙 Y) := by
            cat_disch) :
      ComonoidalCategory C where
  cotensorHom_def := by intros; simp [← id_cotensorHom, ← cotensorHom_id, cotensorHom_comp_cotensorHom]
  cowhiskerLeft_id := by intros; simp [← id_cotensorHom, ← id_cotensorHom_id]
  id_cowhiskerRight := by intros; simp [← cotensorHom_id, id_cotensorHom_id]
  pentagon := by intros; simp [← id_cotensorHom, ← cotensorHom_id, pentagon]
  triangle := by intros; simp [← id_cotensorHom, ← cotensorHom_id, triangle]

@[reassoc]
theorem comp_cotensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⨿'ₘ 𝟙 Z = (f ⨿'ₘ 𝟙 Z) ≫ (g ⨿'ₘ 𝟙 Z) := by
  simp

@[reassoc]
theorem id_cotensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⨿'ₘ f ≫ g = (𝟙 Z ⨿'ₘ f) ≫ (𝟙 Z ⨿'ₘ g) := by
  simp

@[reassoc]
theorem id_cotensor_comp_cotensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⨿'ₘ f) ≫ (g ⨿'ₘ 𝟙 X) = g ⨿'ₘ f := by
  simp [cotensorHom_def']

@[reassoc]
theorem cotensor_id_comp_id_cotensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⨿'ₘ 𝟙 W) ≫ (𝟙 Z ⨿'ₘ f) = g ⨿'ₘ f := by
  simp [cotensorHom_def]

theorem cotensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟘_ C) ⨿'ₘ f = 𝟙 (𝟘_ C) ⨿'ₘ g ↔ f = g := by simp

theorem cotensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⨿'ₘ 𝟙 (𝟘_ C) = g ⨿'ₘ 𝟙 (𝟘_ C) ↔ f = g := by simp

section

variable (C)

attribute [local simp] whisker_exchange

/-- The cotensor product expressed as a functor. -/
@[simps]
def cotensor : C × C ⥤ C where
  obj X := X.1 ⨿' X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⨿'ₘ f.2

/-- The left-associated triple cotensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C where
  obj X := (X.1 ⨿' X.2.1) ⨿' X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⨿'ₘ f.2.1) ⨿'ₘ f.2.2

@[simp]
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⨿' X.2.1) ⨿' X.2.2 :=
  rfl

@[simp]
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) :
    (leftAssocTensor C).map f = (f.1 ⨿'ₘ f.2.1) ⨿'ₘ f.2.2 :=
  rfl

/-- The right-associated triple cotensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C where
  obj X := X.1 ⨿' X.2.1 ⨿' X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⨿'ₘ f.2.1 ⨿'ₘ f.2.2

@[simp]
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⨿' X.2.1 ⨿' X.2.2 :=
  rfl

@[simp]
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) :
    (rightAssocTensor C).map f = f.1 ⨿'ₘ f.2.1 ⨿'ₘ f.2.2 :=
  rfl

/-- The cotensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category. -/
@[simps]
def curriedTensor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨿' Y
      map := fun g => X ◁ᵒᵖ g }
  map f :=
    { app := fun Y => f ▷ᵒᵖ Y }

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
abbrev cotensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X

/-- Tensoring on the right with a fixed object, as a functor. -/
abbrev cotensorRight (X : C) : C ⥤ C := (curriedTensor C).flip.obj X

variable (C)

/-- The functor `fun X ↦ 𝟘_ C ⨿' X`. -/
abbrev cotensorUnitLeft : C ⥤ C := cotensorLeft (𝟘_ C)

/-- The functor `fun X ↦ X ⨿' 𝟘_ C`. -/
abbrev cotensorUnitRight : C ⥤ C := cotensorRight (𝟘_ C)

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
/-- The associator as a natural isomorphism. -/
@[simps!]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents (fun _ => ComonoidalCategory.associator _ _ _)

/-- The left unitor as a natural isomorphism. -/
@[simps!]
def leftUnitorNatIso : cotensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents ComonoidalCategory.leftUnitor

/-- The right unitor as a natural isomorphism. -/
@[simps!]
def rightUnitorNatIso : cotensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents ComonoidalCategory.rightUnitor

/-- The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/
@[simps!]
def curriedAssociatorNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedTensor C) ≅
      bifunctorComp₂₃ (curriedTensor C) (curriedTensor C) :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α'_ X₁ X₂ X₃)))

section

variable {C}

/-- Tensoring on the left with `X ⨿' Y` is naturally isomorphic to
cotensoring on the left with `Y`, and then again with `X`.
-/
def cotensorLeftTensor (X Y : C) : cotensorLeft (X ⨿' Y) ≅ cotensorLeft Y ⋙ cotensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]
theorem cotensorLeftTensor_hom_app (X Y Z : C) :
    (cotensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl

@[simp]
theorem cotensorLeftTensor_inv_app (X Y Z : C) :
    (cotensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [cotensorLeftTensor]

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
abbrev cotensoringLeft : C ⥤ C ⥤ C := curriedTensor C

instance : (cotensoringLeft C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟘_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
abbrev cotensoringRight : C ⥤ C ⥤ C := (curriedTensor C).flip

instance : (cotensoringRight C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟘_ C)
    simpa using h

variable {C}

/-- Tensoring on the right with `X ⨿' Y` is naturally isomorphic to
cotensoring on the right with `X`, and then again with `Y`.
-/
def cotensorRightTensor (X Y : C) : cotensorRight (X ⨿' Y) ≅ cotensorRight X ⋙ cotensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]
theorem cotensorRightTensor_hom_app (X Y Z : C) :
    (cotensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl

@[simp]
theorem cotensorRightTensor_inv_app (X Y Z : C) :
    (cotensorRightTensor X Y).inv.app Z = (associator Z X Y).hom := by simp [cotensorRightTensor]

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [ComonoidalCategory.{v₁} C₁]
variable (C₂ : Type u₂) [Category.{v₂} C₂] [ComonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

@[simps! cotensorObj cotensorHom cotensorUnit cowhiskerLeft cowhiskerRight associator]
instance prodMonoidal : ComonoidalCategory (C₁ × C₂) where
  cotensorObj X Y := (X.1 ⨿' Y.1, X.2 ⨿' Y.2)
  cotensorHom f g := (f.1 ⨿'ₘ g.1, f.2 ⨿'ₘ g.2)
  cowhiskerLeft X _ _ f := (cowhiskerLeft X.1 f.1, cowhiskerLeft X.2 f.2)
  cowhiskerRight f X := (cowhiskerRight f.1 X.1, cowhiskerRight f.2 X.2)
  cotensorHom_def := by simp [cotensorHom_def]
  cotensorUnit := (𝟘_ C₁, 𝟘_ C₂)
  associator X Y Z := (α'_ X.1 Y.1 Z.1).prod (α'_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ'_ X₁).prod (λ'_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ'_ X₁).prod (ρ'_ X₂)

@[simp]
theorem prodMonoidal_leftUnitor_hom_fst (X : C₁ × C₂) :
    ((λ'_ X).hom : 𝟘_ _ ⨿' X ⟶ X).1 = (λ'_ X.1).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_hom_snd (X : C₁ × C₂) :
    ((λ'_ X).hom : 𝟘_ _ ⨿' X ⟶ X).2 = (λ'_ X.2).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_inv_fst (X : C₁ × C₂) :
    ((λ'_ X).inv : X ⟶ 𝟘_ _ ⨿' X).1 = (λ'_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_leftUnitor_inv_snd (X : C₁ × C₂) :
    ((λ'_ X).inv : X ⟶ 𝟘_ _ ⨿' X).2 = (λ'_ X.2).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_hom_fst (X : C₁ × C₂) :
    ((ρ'_ X).hom : X ⨿' 𝟘_ _ ⟶ X).1 = (ρ'_ X.1).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_hom_snd (X : C₁ × C₂) :
    ((ρ'_ X).hom : X ⨿' 𝟘_ _ ⟶ X).2 = (ρ'_ X.2).hom := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_inv_fst (X : C₁ × C₂) :
    ((ρ'_ X).inv : X ⟶ X ⨿' 𝟘_ _).1 = (ρ'_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prodMonoidal_rightUnitor_inv_snd (X : C₁ × C₂) :
    ((ρ'_ X).inv : X ⟶ X ⨿' 𝟘_ _).2 = (ρ'_ X.2).inv := by
  cases X
  rfl

end

end ComonoidalCategory

namespace NatTrans

variable {J : Type*} [Category J] {C : Type*} [Category C] [ComonoidalCategory C]
  {F G F' G' : J ⥤ C} (α : F ⟶ F') (β : G ⟶ G')

@[reassoc]
lemma cotensor_naturality {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⨿'ₘ G.map g) ≫ (α.app Y ⨿'ₘ β.app Y') =
      (α.app X ⨿'ₘ β.app X') ≫ (F'.map f ⨿'ₘ G'.map g) := by simp

@[reassoc]
lemma cowhiskerRight_app_cotensor_app {X Y : J} (f : X ⟶ Y) (X' : J) :
    F.map f ▷ᵒᵖ G.obj X' ≫ (α.app Y ⨿'ₘ β.app X') =
      (α.app X ⨿'ₘ β.app X') ≫ F'.map f ▷ᵒᵖ (G'.obj X') := by
  simpa using cotensor_naturality α β f (𝟙 X')

@[reassoc]
lemma cowhiskerLeft_app_cotensor_app {X' Y' : J} (f : X' ⟶ Y') (X : J) :
    F.obj X ◁ᵒᵖ G.map f ≫ (α.app X ⨿'ₘ β.app Y') =
      (α.app X ⨿'ₘ β.app X') ≫ F'.obj X ◁ᵒᵖ G'.map f := by
  simpa using cotensor_naturality α β (𝟙 X) f

end NatTrans

section ObjectProperty

/-- The restriction of a monoidal category along an object property
that's closed under the monoidal structure. -/
-- See note [reducible non-instances]
abbrev ComonoidalCategory.fullSubcategory
    {C : Type u} [Category.{v} C] [ComonoidalCategory C] (P : ObjectProperty C)
    (cotensorUnit : P (𝟘_ C))
    (cotensorObj : ∀ X Y, P X → P Y → P (X ⨿' Y)) :
    ComonoidalCategory P.FullSubcategory where
  cotensorObj X Y := ⟨X.1 ⨿' Y.1, cotensorObj X.1 Y.1 X.2 Y.2⟩
  cowhiskerLeft X _ _ f := X.1 ◁ᵒᵖ f
  cowhiskerRight f X := ComonoidalCategoryStruct.cowhiskerRight (C := C) f X.1
  cotensorHom f g := ComonoidalCategoryStruct.cotensorHom (C := C) f g
  cotensorUnit := ⟨𝟘_ C, cotensorUnit⟩
  associator X Y Z := P.fullyFaithfulι.preimageIso (α'_ X.1 Y.1 Z.1)
  leftUnitor X := P.fullyFaithfulι.preimageIso (λ'_ X.1)
  rightUnitor X := P.fullyFaithfulι.preimageIso (ρ'_ X.1)
  cotensorHom_def := cotensorHom_def (C := C)
  id_cotensorHom_id X Y := id_cotensorHom_id X.1 Y.1
  cotensorHom_comp_cotensorHom := cotensorHom_comp_cotensorHom (C := C)
  cowhiskerLeft_id X Y := ComonoidalCategory.cowhiskerLeft_id X.1 Y.1
  id_cowhiskerRight X Y := ComonoidalCategory.id_cowhiskerRight X.1 Y.1
  associator_naturality := associator_naturality (C := C)
  leftUnitor_naturality := leftUnitor_naturality (C := C)
  rightUnitor_naturality := rightUnitor_naturality (C := C)
  pentagon W X Y Z := pentagon W.1 X.1 Y.1 Z.1
  triangle X Y := triangle X.1 Y.1

end ObjectProperty

end CategoryTheory
