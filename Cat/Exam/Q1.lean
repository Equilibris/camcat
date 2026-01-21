import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

open CategoryTheory

universe u

variable {C : Type u} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] [SymmetricCategory C]
    (R : C)

open scoped MonoidalCategory

section

variable {X Y Z W : C}

open MonoidalClosed

#check MonoidalClosed.uncurry_id_eq_ev
def app : X ⊗ (X ⟶[_] Y) ⟶ Y := uncurry <| 𝟙 _

theorem app_ev : (app : X ⊗ _ ⟶ Y) = (ihom.ev _).app _ := by
  rw [app, MonoidalClosed.uncurry_id_eq_ev]

@[simp]
theorem app_curry : curry app = 𝟙 (X ⟶[_] Y) := by
  rw [app, curry_eq_iff]

@[simp]
theorem curry_appl (f : X ⊗ Y ⟶ Z) : X ◁ curry f ≫ app = f := by 
  dsimp [app]
  rw [uncurry_id_eq_ev]
  rw [←uncurry_eq]
  rw [←@eq_curry_iff]

@[simp]
theorem curry_appr {g : W ⟶ Y} (f : Y ⊗ X ⟶ Z) : (g ⊗ₘ curry f) ≫ app = (g ▷ _) ≫ f := by
  dsimp [app]
  rw [MonoidalCategory.tensorHom_def_assoc]
  rw [@uncurry_id_eq_ev]
  rw [← @uncurry_eq]
  rw [@uncurry_curry]

end

def pre : Cᵒᵖ ⥤ C where
  obj v := (ihom v.unop).obj R
  map f := (MonoidalClosed.pre f.unop).app R

def adj : C ⥤ Cᵒᵖ where
  obj X := .op <| (ihom X).obj R
  map f := .op <| MonoidalClosed.curry <| (f ▷ _) ≫ app
  map_id X := by
    simp
  map_comp f g := by
    apply (Opposite.op.injEq _ _).mpr
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
      Quiver.Hom.unop_op]
    apply (MonoidalClosed.curry_eq_iff _ _).mpr
    rw [MonoidalClosed.uncurry_natural_left]
    rw [MonoidalClosed.uncurry_curry]
    rw [←MonoidalCategory.tensorHom_def'_assoc]
    simp only [curry_appr]

example : adj R ⊣ pre R := by
  exact .mkOfUnitCounit {
    unit := {
      app X := by
        dsimp [pre, adj]
        refine MonoidalClosed.curry ?_
        refine (β_ _ _).hom ≫ app
      naturality X Y f := by
        dsimp [pre, adj]
        rw [MonoidalClosed.curry_pre_app]
        rw [BraidedCategory.braiding_naturality_left_assoc, curry_appl]
        rw [←BraidedCategory.braiding_naturality_right_assoc]
        rw [MonoidalClosed.curry_natural_left]
    }
    counit := {
      app := fun ⟨X⟩ => .op <| by
        dsimp [pre, adj]
        refine MonoidalClosed.curry ?_
        refine (β_ _ _).hom ≫ app
      naturality X Y f := by
        apply (Opposite.op.injEq _ _).mpr
        dsimp [adj, pre]
        rw [← MonoidalClosed.curry_pre_app]
        rw [@app_curry, Category.id_comp]
        rw [MonoidalClosed.curry_pre_app]
        rw [←MonoidalClosed.curry_natural_left]
        simp only [BraidedCategory.braiding_naturality_left_assoc,
          BraidedCategory.braiding_naturality_right_assoc]
        apply (MonoidalClosed.curry_eq_iff _ _).mpr
        simp only [MonoidalClosed.uncurry_curry, Iso.cancel_iso_hom_left]
        dsimp [app]
        rw [@MonoidalClosed.uncurry_id_eq_ev, @MonoidalClosed.uncurry_id_eq_ev]
        simp
    }
    left_triangle := by
      ext
      apply (Opposite.op.injEq _ _).mpr
      simp only [adj, Functor.comp_obj, Functor.id_obj, pre, Opposite.op_unop, id_eq,
        NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
        Quiver.Hom.unop_op, Functor.whiskerRight_app]
      rw [←MonoidalClosed.curry_natural_left]
      apply (MonoidalClosed.curry_eq_iff _ _).mpr
      change _ = app
      rw [← @MonoidalCategory.tensorHom_def'_assoc]
      simp
    right_triangle := by
      ext ⟨X⟩
      simp only [pre, Functor.comp_obj, Functor.id_obj, adj, id_eq, Opposite.op_unop,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
        Functor.whiskerRight_app, Quiver.Hom.unop_op, Category.id_comp, NatTrans.id_app']
      rw [MonoidalClosed.curry_pre_app]
      simp
  }

