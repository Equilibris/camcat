import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C] -- [MonoidalCategory C] [MonoidalClosed C]

structure FamHom (S : Type u) where
  v : S → Type u

def H : (C ⥤ Type u) ⥤ (C → Type u) where
  obj := Functor.obj
  map := NatTrans.app

def HL : (C → Type u) ⥤ (C ⥤ Type u) where
  obj X := {
    /- obj V := Σ U, (U ⟶ V) × (X V) -/
    /- obj V := Σ U, (U ⟶ V) × (X U → X V) -/
    /- obj V := Σ U, (U ⟶ V) × X V -/
    obj V := Σ U, (U ⟶ V) × X U
    map f := fun ⟨U, m, x⟩ => ⟨U, m ≫ f, x⟩
    /- obj V := X V -/
    /- map f := -/
    /-   sorry -/
  }
  map {X Y} f := {
    app V := fun ⟨U, h, y⟩ => ⟨U, h, f _ y⟩
  }

instance : HL ⊣ H (C := C) := .mkOfUnitCounit {
    unit := {
      app X v Xv := ⟨_, 𝟙 _, Xv⟩
      /- naturality X Y f := by -/
      /-   ext U v -/
      /-   rfl -/
    }
    counit := {
      app X := {
        app Y v := X.map v.2.1 v.2.2
        naturality U V f := by
          ext v
          dsimp [H, HL, Functor.map] at v ⊢
          rw [Functor.map_comp]
          rfl
      }
      naturality U V f := by
        ext X h
        dsimp [H, HL] at h ⊢
        have := funext_iff.mp (f.naturality h.snd.1) h.snd.2
        dsimp at this
        rw [this]
    }
    left_triangle := by
      ext U V v
      dsimp [HL, H, CategoryStruct.id] at v ⊢
      rw [Category.id_comp]
    right_triangle := by 
      ext V U v
      dsimp [HL, H, CategoryStruct.id] at v ⊢
      rw [V.map_id]
      rfl
  }

def HR : (C → Type u) ⥤ (C ⥤ Type u) where
  obj X := {
    obj V := (U : C) → (V ⟶ U) → X U
    map f := fun h U v => h U (f ≫ v)
  }
  map {X Y} f := {
    app U h V h' := f _ (h V h')
  }

instance : H (C := C) ⊣ HR :=
  .mkOfUnitCounit {
    unit := {
      app X := {
        app Y v U m := X.map m v
        naturality U V f := by
          ext o
          dsimp [HR, H]
          ext U v
          rw [X.map_comp]
          rfl
      }
      naturality U V f := by
        ext X x
        dsimp [HR, H]
        ext Y m
        change (f.app X ≫ V.map m) x = (U.map m ≫ f.app Y) x
        rw [f.naturality]
    }
    counit := {
      app X V h := h V (𝟙 _)
    }
    left_triangle := by
      ext V U v
      dsimp [H, HR] at v ⊢
      rw [V.map_id]
      rfl
    right_triangle := by
      ext U V v
      dsimp [H, HR] at v ⊢
      ext X m
      rw [Category.comp_id]
  }
  /- .mkOfHomEquiv { -/
  /-   homEquiv X Y := { -/
  /-     toFun o := { -/
  /-       app V v U := by  -/
  /-         dsimp [H, HR, Quiver.Hom] at o ⊢ -/
  /-         have := o _ v -/
  /-         sorry -/
  /-     } -/
  /-     invFun _ := sorry -/
  /-     left_inv := sorry -/
  /-     right_inv := sorry -/
  /-   } -/
  /- } -/
  /-  -/
