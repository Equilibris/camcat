import Mathlib.CategoryTheory.Closed.Cartesian
import Cat.STLCI.Stx
import Cat.Product

namespace STLC

universe u

open CategoryTheory MonoidalCategory 

variable {𝓒 : Type u}
    [Category 𝓒]
    [cmc : CartesianMonoidalCategory 𝓒]
    [ccc : CartesianClosed 𝓒]

@[simp]
def Ty.denote : Ty → 𝓒
  | .arr t1 t2 => t1.denote ⟹ t2.denote
  | .prod t1 t2 => t1.denote ⊗ t2.denote
  | .unit => (𝟙_ 𝓒)

def ctx_denote : List Ty → 𝓒
  | [] => 𝟙_ 𝓒
  | hd :: tl => hd.denote ⊗ ctx_denote tl

abbrev proj {t : Ty}
    : {Γ : _} → List.MemT t Γ → (ctx_denote Γ ⟶ t.denote (𝓒 := 𝓒)) 
  | _ :: _, .hd => cmc.fst _ _
  | _ :: _, .tl h => cmc.snd _ _ ≫ proj h

open CartesianMonoidalCategory in
open CartesianClosed in
def ITerm.denote : {Γ t : _} → ITerm Γ t → (ctx_denote (𝓒 := 𝓒) Γ ⟶ t.denote)
  | _, _, .var v => proj v
  | _, _, .lam v => curry v.denote
  | _, _, .app f v => lift v.denote (𝟙 _) ≫ uncurry f.denote

  | _, _, .unit => toUnit _

  | _, _, .mk a b => lift a.denote b.denote
  | _, _, .fst v => v.denote ≫ cmc.fst _ _
  | _, _, .snd v => v.denote ≫ cmc.snd _ _

end STLC

