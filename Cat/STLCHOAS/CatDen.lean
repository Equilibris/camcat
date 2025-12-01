import Mathlib.CategoryTheory.Closed.Cartesian
import Cat.STLCHOAS.Stx
import Cat.Product

namespace STLCHOAS

universe u

open CategoryTheory MonoidalCategory 

variable {𝓒 : Type u}
    [Category 𝓒]
    [cmc : CartesianMonoidalCategory 𝓒]
    [ccc : CartesianClosed 𝓒]

inductive Sccc : List Ty → Ty → Type
  | id {X} : Sccc [X] X
  | proj {Γ} {X : Fin _} : Sccc Γ (Γ.get X)
  | curry {X C Γ} : Sccc (X :: Γ) C → Sccc (Γ) (.arr X C)

@[simp]
def Ty.denote : Ty → 𝓒
  | .arr t1 t2 => t1.denote ⟹ t2.denote

  | .prod t1 t2 => t1.denote ⊗ t2.denote
  | .unit => (𝟙_ 𝓒)

def denGamma : List 𝓒 → 𝓒
  | [] => 𝟙_ _
  | hd :: tl => hd ⊗ denGamma tl

open CartesianClosed in
@[simp]
def Term'.denote {ty : Ty} (Γ : List (Sigma (Sccc []))) : Term' (fun v => Nat) ty → Sccc Γ ty
  | .var v => sorry
  | .app t1 t2 =>
    have v1 := uncurry (t1.denote Γ)
    have v2 := t2.denote Γ
    Limits.IsBinaryProduct.lift (cmc.tensorProductIsBinaryProduct _ _)  v2 (𝟙 _) ≫ v1
  | .lam (A := A) (B := B) f => by
    refine .curry ?_
    have := (f <| .curry sorry)
    apply curry
    refine 
    /- have := (exp.adjunction this) -/
    dsimp
    sorry
    /- fun x => Term'.denote (f x) -/
  | .snd a => a.denote ≫ CartesianMonoidalCategory.snd _ _
  | .fst a => a.denote ≫ CartesianMonoidalCategory.fst _ _
  | .mkP a b => 
    /- ⟨a.denote, b.denote⟩ -/
    sorry
  | .unit => 𝟙 _

def same {ty : Ty} (t1 t2 : Term ty) : Prop :=
  Term'.denote t1 = Term'.denote t2

