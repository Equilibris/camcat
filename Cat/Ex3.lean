import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Nat
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.SimpleMonCat
import Cat.BiMonCatX
import Cat.Ex2

open CategoryTheory
open CartesianClosed
open Limits
open scoped MonoidalCategory

universe u v

variable {𝓒 : Type u}
  [Category.{v, u} 𝓒]
  [CartesianMonoidalCategory 𝓒]
  [CartesianClosed 𝓒]
  {A B X Y Z W X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝓒}

instance : CartesianClosed (Type u) where
  closed X := {
    rightAdj := {
      obj Y := X → Y
      map {X' Y'} m' mx x := m' (mx x)
    }
    adj := .mkOfHomEquiv {
      homEquiv A B := {
        toFun unc a b := unc ⟨b, a⟩
        invFun f := fun ⟨a,b⟩ => f b a
        right_inv := fun _ => rfl
        left_inv := fun _ => rfl
      }
    }
  }

@[simp]
theorem curry_wisk {f : Y ⟶ Z} : curry (X ◁ f) = f ≫ curry (𝟙 _) := by
  rw [@curry_eq_iff]
  rw [@uncurry_natural_left]
  rw [uncurry_curry]
  rw [Category.comp_id]

instance : SimpleCartesianMonoidalCategory.{u+1, u} (Sigma PartialOrder) where
  tensorUnit := ⟨PUnit, inferInstance⟩
  isTerminalTensorUnit := .ofUniqueHom
    (fun X => ⟨fun _ => .unit, fun _ _ _ => le_refl _⟩)
    fun X ⟨m, mm⟩ => rfl
  tensorObj X Y := ⟨X.fst × Y.fst, inferInstance⟩
  fst X Y := ⟨Prod.fst, monotone_fst⟩
  snd X Y := ⟨Prod.snd, monotone_snd⟩
  tensorProductIsBinaryProduct X Y := .ofUniqueHom
    (fun f g => ⟨
      fun x => ⟨f.1 x, g.1 x⟩,
      fun a b h => Prod.mk_le_mk.mpr ⟨f.2 h, g.2 h⟩
    ⟩)
    (fun f g => rfl) (fun f g => rfl)
    (fun _ _ m => by rintro rfl rfl; rfl)

instance : CartesianClosed (Sigma PartialOrder) where
  closed X := {
    rightAdj := {
      obj Y := ⟨X.1 →o Y.1, inferInstance⟩
      map {X' Y'} (oh : _ →o _) := {
        toFun a := OrderHom.comp oh a
        monotone' a b le x := oh.monotone (le x)
      }
      map_id X := rfl
      map_comp f g := rfl
    }
    adj := .mkOfHomEquiv {
      homEquiv X' Y := show (X.fst × X'.fst →o Y.fst) ≃ (X'.fst →o X.fst →o Y.fst) from {
        toFun h := {
          toFun x' := {
            toFun := fun x => h ⟨x,x'⟩
            monotone' := fun a b le => h.mono <| Prod.GCongr.mk_le_mk_left le
          }
          monotone' := fun a b le x => h.mono <| Prod.GCongr.mk_le_mk_right le
        }
        invFun h := {
          toFun := fun ⟨x, x'⟩ => h x' x
          monotone' := fun ⟨xa,x'a⟩ ⟨xb,x'b⟩ ⟨lex, leb⟩ =>
            le_trans ((h x'a).mono lex) <| OrderHom.apply_mono (h.mono leb) (le_refl _)
        }
        right_inv _ := rfl
        left_inv _ := rfl
      }
    }
  }

-- RAPL LAPC

section Ex2

def ciel (h : X ⟶ Y) : (𝟙_ 𝓒 ⟶ Y ^^ X) :=
  CartesianClosed.curry ((ρ_ _).hom ≫ h)

def bar (h : 𝟙_ 𝓒 ⟶ Y ^^ X) : X ⟶ Y :=
  (ρ_ _).inv ≫ CartesianClosed.uncurry h

example : (X ⟶ Y) ≃ (𝟙_ 𝓒 ⟶ Y ^^ X) where
  toFun := ciel
  invFun := bar

  left_inv f := by
    dsimp [bar, ciel]
    rw [CartesianClosed.uncurry_curry, Iso.inv_comp_eq]
  right_inv f := by
    dsimp [bar, ciel]
    rw [←Category.assoc, Iso.hom_inv_id, Category.id_comp, CartesianClosed.curry_eq_iff]

end Ex2

section Ex3

end Ex3

section Ex4

open CartesianClosed

example {g : W ⟶ Y} {f : X ⊗ Y ⟶ Z}
    : CartesianClosed.curry ((𝟙 X ⊗ₘ g ) ≫ f)
    = g ≫ CartesianClosed.curry f := by
  rw [curry_eq_iff, uncurry_natural_left, uncurry_curry, MonoidalCategory.id_tensorHom]

end Ex4

section Ex5

def app : X ⊗ (X ⟹ Y) ⟶ Y := uncurry <| 𝟙 (X ⟹ Y)

theorem app_curry : curry app = 𝟙 (X ⟹ Y) := by
  rw [app, curry_eq_iff]

theorem curry_appl (f : X ⊗ Y ⟶ Z) : X ◁ curry f ≫ app = f := by 
  dsimp [app]
  rw [uncurry_id_eq_ev]
  rw [←uncurry_eq]
  rw [←@eq_curry_iff]

theorem curry_appr {g : W ⟶ Y} (f : Y ⊗ X ⟶ Z) : (g ⊗ₘ curry f) ≫ app = (g ▷ _) ≫ f := by
  dsimp [app]
  rw [MonoidalCategory.tensorHom_def_assoc]
  rw [@uncurry_id_eq_ev]
  rw [← @uncurry_eq]
  rw [@uncurry_curry]

def iret X (f : Y ⟶ Z) : Y ^^ X ⟶ Z ^^ X := curry (app ≫ f)

theorem iret.id : iret X (𝟙 Y) = 𝟙 (Y ^^ X) := by 
  dsimp [iret, app]
  rw [curry_eq_iff, Category.comp_id]

theorem iret.compv (g : Z ⟶ W) (f : X ⊗ Y ⟶ Z)
    : curry (f ≫ g) = curry f ≫ iret X g := by
  rw [curry_eq_iff, uncurry_natural_left,
    iret, uncurry_curry, ←Category.assoc,
    curry_appl]

theorem iret.comp
    (u : Y ⟶ Z) (v : Z ⟶ W)
    : iret X (u ≫ v) = iret X u ≫ iret X v := by
  rw [←Category.id_comp (iret X (u ≫ v))]
  rw [←app_curry]
  rw [←compv]
  rw [curry_eq_iff]
  rw [uncurry_natural_left, iret, iret]
  rw [uncurry_curry]
  nth_rw 2 [←Category.assoc]
  rw [curry_appl]
  rw [Category.assoc]

end Ex5

section Ex6

def iarg X (f : Y ⟶ Z) : X ^^ Z ⟶ X ^^ Y := 
  curry (f ▷ _ ≫ app)

def iarg.id : iarg X (𝟙 Y) = 𝟙 (Y ⟹ X) := by 
  rw [iarg]
  rw [MonoidalCategory.id_whiskerRight_assoc]
  rw [app_curry]

theorem iarg.compv (g : W ⟶ X) (f : X ⊗ Y ⟶ Z)
    : curry ((g ⊗ₘ 𝟙 _) ≫ f) = curry f ≫ iarg _ g := by
  rw [curry_eq_iff, uncurry_natural_left]
  rw [iarg, uncurry_curry]
  rw [MonoidalCategory.whisker_exchange_assoc]
  rw [←Category.assoc]
  rw [←MonoidalCategory.tensorHom_def]
  rw [curry_appr]
  rw [@MonoidalCategory.tensorHom_id]

theorem iarg.comp
    (u : Y ⟶ Z) (v : Z ⟶ W)
    : iarg X (u ≫ v) = iarg X v ≫ iarg X u := by
  rw [←Category.id_comp (iarg X (u ≫ v))]
  rw [←app_curry]
  rw [←compv]
  rw [curry_eq_iff]
  rw [uncurry_natural_left, iarg, iarg, uncurry_curry]
  rw [←MonoidalCategory.tensorHom_def'_assoc]
  rw [curry_appr]
  rw [← @MonoidalCategory.comp_whiskerRight_assoc]
  rw [@MonoidalCategory.tensorHom_id]

end Ex6

section Ex7

theorem iarg_iret_comm
    (g : B ⟶ A)
    (f : X ⟶ Y)
    : iarg X g ≫ iret B f = iret A f ≫ iarg Y g := by
  rw [iarg, ←iret.compv]
  rw [iret, ←iarg.compv]
  rw [eq_curry_iff, uncurry_curry, Category.assoc]
  rw [@MonoidalCategory.tensorHom_id]

def ie (g : A ⟶ B) (f : Y ⟶ X) : A ^^ X ⟶ B ^^ Y := 
  curry ((f ⊗ₘ 𝟙 _) ≫ app ≫ g)

theorem ie.of_iarg_iret
    (f' : B ⟶ A)
    (f : X ⟶ Y)
    : iarg X f' ≫ iret B f = ie f f' := by
  rw [iarg, ←iret.compv, ie]
  rw [eq_curry_iff, uncurry_curry]
  rw [@Category.assoc]
  rw [@MonoidalCategory.tensorHom_id]

end Ex7

section Ex8

open scoped ComonoidalCategory

variable [CartesianComonoidalCategory 𝓒]

open CartesianComonoidalCategory
open CartesianMonoidalCategory

def commOx : X ⊗ Y ≅ Y ⊗ X where
  hom := lift (snd _ _) (fst _ _)
  inv := lift (snd _ _) (fst _ _)

def ex8.v : Y ⨿' Z ⟶ X ⟹ (X ⊗ Y) ⨿' X ⊗ Z := 
  (desc
    (curry (inl _ _))
    (curry (inr _ _)))

def ex8 : (X ⊗ Y) ⨿' (X ⊗ Z) ≅  X ⊗ (Y ⨿' Z) where
  hom := desc
    (lift (fst _ _) (snd _ _ ≫ inl _ _))
    (lift (fst _ _) (snd _ _ ≫ inr _ _))
  inv := (X ◁ ex8.v) ≫ app
  hom_inv_id := by
    apply CartesianComonoidalCategory.hom_ext
    <;> simp
    <;> rw [← lift_whiskerLeft_assoc, lift_fst_snd]
    <;> simp [ex8.v]
    <;> rw [@curry_appl]
  inv_hom_id := by
    rw [←Category.comp_id (fst X Y), ←Category.comp_id (fst X Z)]
    rw [←lift_map, ←lift_map, lift_fst_snd, lift_fst_snd]
    simp only [MonoidalCategory.id_tensorHom, Category.id_comp, Category.assoc]
    rw [←uncurry_curry (𝟙 _)]
    rw [←curry_eq_iff]
    rw [@curry_natural_left, curry_natural_right]
    rw [app, curry_uncurry, Category.id_comp]
    rw [ex8.v, desc_comp]
    rw [←curry_natural_right, ←curry_natural_right]
    rw [inl_desc, inr_desc]
    rw [curry_wisk, curry_wisk]
    rw [inl_inr_desc]

end Ex8

