import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open CategoryTheory

variable (C : Type _) [ccat : Category C]

structure DiGrap where
  n : C
  e : C

  es : e ⟶ n
  ee : e ⟶ n

structure DiGrap.Hom (x y : DiGrap C) : Type _ where
  he : x.e ⟶ y.e
  hn : x.n ⟶ y.n

  eqa : (x.es ≫ hn = he ≫ y.es)
  eqb : (x.ee ≫ hn = he ≫ y.ee)

def DiGrap.comp {X Y Z : DiGrap C} : DiGrap.Hom C X Y → DiGrap.Hom C Y Z → DiGrap.Hom C X Z
  | ⟨he₁, hn₁, d₁₁, d₁₂⟩, ⟨he₂, hn₂, d₂₁, d₂₂⟩ =>
    ⟨he₁ ≫ he₂, hn₁ ≫ hn₂,
      calc
        X.es ≫ hn₁ ≫ hn₂
          = (X.es ≫ hn₁) ≫ hn₂ := (Category.assoc _ _ _).symm
        _ = (he₁ ≫ Y.es) ≫ hn₂ := by rw [d₁₁]
        _ = he₁ ≫ (Y.es ≫ hn₂) := (Category.assoc _ _ _)
        _ = he₁ ≫ he₂ ≫ Z.es   := by rw [d₂₁]
        _ = (he₁ ≫ he₂) ≫ Z.es := (Category.assoc _ _ _).symm,
      calc
        X.ee ≫ hn₁ ≫ hn₂
          = (X.ee ≫ hn₁) ≫ hn₂ := (Category.assoc _ _ _).symm
        _ = (he₁ ≫ Y.ee) ≫ hn₂ := by rw [d₁₂]
        _ = he₁ ≫ (Y.ee ≫ hn₂) := (Category.assoc _ _ _)
        _ = he₁ ≫ he₂ ≫ Z.ee   := by rw [d₂₂]
        _ = (he₁ ≫ he₂) ≫ Z.ee := (Category.assoc _ _ _).symm,
      ⟩

instance : Category (DiGrap C) where
  Hom := DiGrap.Hom C
  id := fun x => ⟨
    𝟙 x.e,
    𝟙 x.n,
    by rw [Category.comp_id, Category.id_comp],
    by rw [Category.comp_id, Category.id_comp]
  ⟩
  comp := DiGrap.comp C
  id_comp := fun f => by
    change DiGrap.Hom.mk _ _ _ _ = f
    simp only [Category.id_comp]
  comp_id := fun f => by
    change DiGrap.Hom.mk _ _ _ _ = f
    simp only [Category.comp_id]
  assoc := fun f g h => by
    change DiGrap.Hom.mk _ _ _ _ = DiGrap.Hom.mk _ _ _ _
    simp only [Category.assoc]


