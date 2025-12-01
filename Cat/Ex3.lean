import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Nat
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Iso
import Cat.L1
import Cat.L2Live
import Cat.Product

open CategoryTheory 
open Limits

universe u v

variable {𝓒 : Type u} [Category.{v, u} 𝓒] {A B X Y Z X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝓒}

instance : SimpleCartesianMonoidalCategory (Sigma Preorder) where
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


instance : CartesianClosed (Sigma Preorder) where
  closed X := sorry

