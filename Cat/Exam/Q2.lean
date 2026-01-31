import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C]

def H : (C ⥤ Type u) ⥤ (C → Type u) where
  obj := Functor.obj
  map := NatTrans.app

def HL : (C → Type u) ⥤ (C ⥤ Type u) where
  obj X := {
    obj V := Σ U, (U ⟶ V) × X U
    map f := fun ⟨U, m, x⟩ => ⟨U, m ≫ f, x⟩
  }
  map {X Y} f := {
    app V := fun ⟨U, m, x⟩ => ⟨U, m, f _ x⟩
  }

def HR : (C → Type u) ⥤ (C ⥤ Type u) where
  obj X := {
    obj V := (U : C) → (V ⟶ U) → X U
    map f o U m := o U (f ≫ m)
  }
  map {X Y} f := {
    app V o U m := f _ (o U m)
  }

instance : HL ⊣ H (C := C) := .mkOfUnitCounit {
    unit := {
      app X V v := ⟨V, 𝟙 _, v⟩
    }
    counit := {
      app X := {
        app Y v := X.map v.2.1 v.2.2
        naturality U V f := by
          ext v
          calc
            X.map (v.2.1 ≫ f) v.2.2
              = (X.map v.snd.1 ≫ X.map f) v.snd.2  := by rw [Functor.map_comp]
            _ = X.map f (X.map v.snd.1 v.snd.2)    := rfl
      }
      naturality U V f := by
        ext X h
        calc
          (f.app h.fst ≫ V.map h.snd.1) h.snd.2
            = (U.map h.snd.1 ≫ f.app X) h.snd.2 := by rw [f.naturality]
    }
    left_triangle := by
      ext U V v
      change (U_1 : C) × (U_1 ⟶ V) × U U_1 at v
      calc
        (⟨v.fst, (𝟙 v.fst ≫ v.snd.1, v.snd.2)⟩ : (U_1 : C) × (U_1 ⟶ V) × U U_1)
          = ⟨v.fst, (v.snd.1, v.snd.2)⟩ := by rw [Category.id_comp]
        _ = v := rfl
    right_triangle := by 
      ext V U v
      change V.obj U at v
      calc
        V.map (𝟙 U) v
          = 𝟙 (V.obj U) v := by rw [V.map_id]
        _ = v             := rfl
  }

instance : H (C := C) ⊣ HR :=
  .mkOfUnitCounit {
    unit := {
      app X := {
        app Y v U m := X.map m v
        naturality U V f := by
          ext o
          funext U v
          change (X.map f ≫ X.map v) o = X.map (f ≫ v) o
          rw [X.map_comp]
      }
      naturality U V f := by
        ext X x
        funext Y m
        change (f.app X ≫ V.map m) x = (U.map m ≫ f.app Y) x
        rw [f.naturality]
    }
    counit := {
      app X V h := h V (𝟙 _)
    }
    left_triangle := by
      ext V U v
      change V.map (𝟙 U) v = (𝟙 (V.obj U)) v
      rw [V.map_id]
    right_triangle := by
      ext U V v
      funext X m
      change v X (m ≫ 𝟙 X) = v X m
      rw [Category.comp_id]
  }

