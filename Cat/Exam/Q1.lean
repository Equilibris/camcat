import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

open CategoryTheory

universe u

variable {C : Type u} [Category C]
    [MonoidalCategory C] [MonoidalClosed C]
    (R : C)

open scoped MonoidalCategory
open scoped MonoidalClosed

section

variable {X Y Z W : C}

open MonoidalClosed

def app : X ⊗ (X ⟶[_] Y) ⟶ Y := uncurry <| 𝟙 _

theorem app_ev : (app : X ⊗ _ ⟶ Y) = (ihom.ev _).app _ := by
  rw [app, MonoidalClosed.uncurry_id_eq_ev]

@[simp]
theorem app_curry : curry app = 𝟙 (X ⟶[_] Y) := by
  rw [app, curry_eq_iff]

@[simp]
theorem curry_appl (f : X ⊗ Y ⟶ Z) : X ◁ curry f ≫ app = f := by 
  rw [app_ev]
  rw [←uncurry_eq]
  rw [←@eq_curry_iff]

@[simp]
theorem curry_appr {g : W ⟶ Y} (f : Y ⊗ X ⟶ Z) : (g ⊗ₘ curry f) ≫ app = (g ▷ _) ≫ f := by
  rw [MonoidalCategory.tensorHom_def_assoc]
  rw [app_ev]
  rw [← @uncurry_eq]
  rw [@uncurry_curry]

end

variable [SymmetricCategory C]
open BraidedCategory MonoidalCategory

def pre : Cᵒᵖ ⥤ C where
  obj v := (ihom v.unop).obj R
  map f := (MonoidalClosed.pre f.unop).app R

open MonoidalClosed in
def adj : C ⥤ Cᵒᵖ where
  obj X := .op <| X ⟶[_] R
  map f := .op <| curry <| (f ▷ _) ≫ app
  map_id X := by
    rw [id_whiskerRight, Category.id_comp, app_curry, op_id]
  map_comp {X Y Z} f g := by
    apply (Opposite.op.injEq _ _).mpr
    apply (curry_eq_iff _ _).mpr
    calc
      (f ≫ g) ▷ (Z ⟶[_] R) ≫ app
        = f ▷ (Z ⟶[_] R) ≫ g ▷ (Z ⟶[_] R) ≫ app
                                                := by rw [comp_whiskerRight_assoc]
      _ = (f ⊗ₘ curry (g ▷ (Z ⟶[_] R) ≫ app)) ≫ app
                                                := by rw [curry_appr]
      _ = X ◁ curry (g ▷ (Z ⟶[_] R) ≫ app) ≫ f ▷ (Y ⟶[_] R) ≫ app
                                                := by rw [tensorHom_def'_assoc]
      _ = X ◁ curry (g ▷ (Z ⟶[_] R) ≫ app) ≫ uncurry (curry (f ▷ (Y ⟶[_] R) ≫ app))
                                                := by rw [uncurry_curry]
      _ = uncurry (curry (g ▷ (Z ⟶[_] R) ≫ app) ≫ curry (f ▷ (Y ⟶[_] R) ≫ app))
                                                := by rw [uncurry_natural_left]

example : adj R ⊣ pre R := by
  exact .mkOfUnitCounit {
    unit := {
      app X := show X ⟶ (ihom ((ihom X).obj R)).obj R
               from MonoidalClosed.curry ((β_ _ _).hom ≫ app)
      naturality X Y f := by
        dsimp [pre, adj]
        rw [MonoidalClosed.curry_pre_app]
        rw [braiding_naturality_left_assoc, curry_appl]
        rw [←braiding_naturality_right_assoc]
        rw [MonoidalClosed.curry_natural_left]
    }
    counit := {
      app := fun ⟨X⟩ => .op 
        <| show X ⟶ (X ⟶[_] R) ⟶[_] R from MonoidalClosed.curry ((β_ _ _).hom ≫ app)
      naturality X Y f := by
        apply (Opposite.op.injEq _ _).mpr
        dsimp [adj, pre]
        rw [← MonoidalClosed.curry_pre_app]
        rw [@app_curry, Category.id_comp]
        rw [MonoidalClosed.curry_pre_app]
        rw [←MonoidalClosed.curry_natural_left]
        rw [braiding_naturality_left_assoc]
        rw [braiding_naturality_right_assoc]
        apply (MonoidalClosed.curry_eq_iff _ _).mpr
        rw [MonoidalClosed.uncurry_curry, Iso.cancel_iso_hom_left]
        rw [app_ev, app_ev]
        rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
    }
    left_triangle := by
      ext
      apply (Opposite.op.injEq _ _).mpr
      dsimp [adj, pre]
      rw [←MonoidalClosed.curry_natural_left]
      apply (MonoidalClosed.curry_eq_iff _ _).mpr
      change _ = app
      rw [Category.comp_id]
      rw [←tensorHom_def'_assoc]
      rw [curry_appr]
      rw [braiding_naturality_left_assoc, curry_appl]
      rw [SymmetricCategory.symmetry_assoc]
    right_triangle := by
      ext ⟨X⟩
      dsimp [pre, adj]
      rw [Category.id_comp]
      rw [MonoidalClosed.curry_pre_app]
      rw [braiding_naturality_left_assoc, curry_appl]
      rw [SymmetricCategory.symmetry_assoc, app_curry]
  }

