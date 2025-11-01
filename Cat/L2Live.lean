import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Cat.L1
import Cat.L3
import Cat.L4

open CategoryTheory

universe u

variable {𝓒 : Type u} [Category 𝓒]


class WellPointed (𝓒 : Type u) [Category 𝓒] [Limits.HasTerminal 𝓒] : Prop where
  wp : ∀ X Y : 𝓒, ∀ f g : X ⟶ Y, (∀ x : ⊤_ 𝓒 ⟶ X, x ≫ f = x ≫ g) → f = g

def emptyIsInitial : Limits.IsInitial PEmpty :=
  Limits.IsInitial.ofUniqueHom (fun _ => PEmpty.elim) fun _ _ => funext (·.elim)

instance : Limits.HasInitial (Type u) := Limits.IsInitial.hasInitial emptyIsInitial

instance wpType : WellPointed (Type u) where
  wp _X _Y _f _g h :=
    funext (fun v =>
      funext_iff.mp (h (fun _ => v))
        <| (Limits.IsTerminal.uniqueUpToIso isTerminalPUnit Limits.terminalIsTerminal).hom .unit)

theorem nwpCoType (x : WellPointed (Type u)ᵒᵖ) : False :=
  x.wp
    (.op (ULift Bool))
    (.op PUnit)
    (.op fun _ => .up .true)
    (.op fun _ => .up .false)
    (fun x =>
      (Limits.IsTerminal.uniqueUpToIso
          Limits.terminalIsTerminal
          (CategoryTheory.Limits.terminalOpOfInitial emptyIsInitial)
      |>.inv.unop) (x.unop (.up .true))
      |>.elim
    )
    |> (Opposite.op.injEq _ _).mp
    |> (funext_iff.mp · .unit)
    |> (ULift.up.injEq _ _).mp
    |> Bool.noConfusion



