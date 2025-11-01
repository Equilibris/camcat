import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Cat.L1
import Cat.Product

open CategoryTheory

universe u

section terminal

@[grind]
structure PSTrans where
  S : Type u
  σ : S → Option S

@[grind]
structure PSHom (S T : PSTrans) where
  f : S.S → T.S
  h : (Option.map f) ∘ S.σ = T.σ ∘ f

instance : Category PSTrans where
  Hom := PSHom
  id X := ⟨id, funext fun v => by grind⟩
  comp {X Y Z} A B := ⟨B.f ∘ A.f, calc
    _ = Option.map B.f ∘ Option.map A.f ∘ X.σ := by rw [←Option.map_comp_map, Function.comp_assoc]
    _ = (Option.map B.f ∘ Y.σ) ∘ A.f          := by rw [A.h, ←Function.comp_assoc]
    _ = Z.σ ∘ B.f ∘ A.f                       := by rw [B.h, Function.comp_assoc]⟩

instance : Limits.HasTerminal PSTrans :=
  Limits.IsTerminal.hasTerminal 
    (X := ⟨Option PUnit, fun | .some _ => .some (.some .unit) | .none => .none⟩) 
    <| Limits.IsTerminal.ofUniqueHom
      (fun x => ⟨
        fun v => match x.σ v with | .some _ => .up .true | .none => .up .false,
        funext fun v => by
          simp [Option.map]
          cases h : x.σ v
          · rfl
          · apply (Option.some.injEq _ _).mpr
            dsimp
            sorry
          ⟩)
      sorry

-- ex 2 proven in L2Live

end terminal

section initial

instance : Limits.HasInitial PSTrans :=
  Limits.IsInitial.hasInitial 
    (X := ⟨Option PUnit, fun | .some _ => .some (.some .unit) | .none => .none⟩)
    <| Limits.IsInitial.ofUniqueHom
      sorry
      sorry



end initial

