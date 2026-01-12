import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
/- import Mathlib.CategoryTheory.Monoidal.Closed.Types -/
import Mathlib.CategoryTheory.Yoneda
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.Ex2
import Cat.Ex4
import Cat.HEq

open CategoryTheory

universe u

section

variable {𝓒 : Type} [Category 𝓒]
  [MonoidalCategory 𝓒]
  [MonoidalClosed 𝓒]

#check MonoidalClosed.curry

def original (C : 𝓒) : 𝓒ᵒᵖ ⥤ 𝓒 where
  obj X := (ihom X.unop).obj C
  map {X Y} f := (MonoidalClosed.pre f.unop).app C

open scoped MonoidalCategory

def adj (C : 𝓒) : 𝓒 ⥤ 𝓒ᵒᵖ where
  obj X := .op ((ihom C).obj X)
  map f := .op sorry

example (C : 𝓒) : adj C ⊣ original C := 
  .mkOfHomEquiv {
    homEquiv X := fun ⟨Y⟩ => {
      toFun v := by
        have v := MonoidalClosed.uncurry v.unop
        dsimp [adj, original] at v ⊢
        refine MonoidalClosed.curry ?_
        sorry
      invFun v := by 
        apply Opposite.op
        dsimp [adj, original] at v ⊢
        refine MonoidalClosed.curry ?_
        sorry
    }
  }

end

section

variable {𝓒 : Type} [SmallCategory 𝓒]
  [MonoidalCategory 𝓒]
  [MonoidalClosed 𝓒]
  {X Y : 𝓒ᵒᵖ ⥤ Type}
  {f g : X ⟶ Y}
  (c : 𝓒)

#check yonedaEquiv

open scoped MonoidalCategory

instance : CartesianMonoidalCategory (𝓒ᵒᵖ ⥤ Type) :=
  .ofChosenFiniteProducts (by sorry) (by sorry)
  /- .mk  -/

noncomputable abbrev expf : (𝓒ᵒᵖ ⥤  Type) ⥤ (𝓒ᵒᵖ ⥤  Type) :=
  (ihom (yoneda.obj c))

noncomputable abbrev adjf : (𝓒ᵒᵖ ⥤  Type) ⥤ (𝓒ᵒᵖ ⥤  Type) where
  obj X := (X ⊗ yoneda.obj c)
  map f := f ▷ _

example : expf c ⊣ adjf c := 
  .mkOfHomEquiv {
    homEquiv X Y := {
      toFun X := {
        app V := by 
          dsimp [expf] at X ⊢
          have := X.app V
          sorry
      }
        /- by  -/
        /- dsimp [expf] -/
        /- intro x -/
        /- have := x.app -/
        /- #check MonoidalClosed.uncurry -/
        /- #check yonedaEquiv -/
        /- sorry -/
      invFun := sorry
      left_inv := sorry
      right_inv := sorry
    }
  }

end

