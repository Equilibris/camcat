import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
/- import Mathlib.CategoryTheory.Monoidal.Closed.Types -/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Yoneda
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.Ex2
import Cat.Ex4
import Cat.HEq

open CategoryTheory

universe u v w

section

variable {𝓒 : Type} [Category 𝓒]
  [MonoidalCategory 𝓒]
  [MonoidalClosed 𝓒]

open Limits

#check Fan.mk

variable {β : Type w} {C : Type u} [Category.{v, u} C] {f : β → C} (P : C)
  (p : (b : β) → P ⟶ f b)

def IsProduct := IsLimit (Fan.mk P p)

namespace IsProduct

/--
info: CategoryTheory.Limits.mkFanLimit.{w, v, u} {β : Type w} {C : Type u} [Category.{v, u} C] {f : β → C} (t : Fan f)
  (lift : (s : Fan f) → s.pt ⟶ t.pt) (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by cat_disch)
  (uniq : ∀ (s : Fan f) (m : s.pt ⟶ t.pt), (∀ (j : β), m ≫ t.proj j = s.proj j) → m = lift s := by cat_disch) :
  IsLimit t
-/
#guard_msgs in
#check mkFanLimit

example
    {β : Type}
    (f : β → Type)
    : IsLimit (Fan.mk ((x : _) → f x) (fun x v => v x)) :=
  mkFanLimit _
    (fun s v x => s.proj x v)
    (fun _ _ => funext fun _ => rfl)
    fun _ _ h => funext fun x => funext fun y =>
      funext_iff.mp (h y) x

example
    {β : Type}
    (f : β → Type)
    : IsColimit (Cofan.mk (Sigma f) (fun a b => Sigma.mk a b)) :=
  mkCofanColimit _
    (fun s ⟨h, v⟩ => s.inj h v)
    (fun _ _ => funext fun _ => rfl)
    fun _ _ h => funext fun v =>
      funext_iff.mp (h v.fst) v.snd

end IsProduct

end

