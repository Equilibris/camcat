import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Order.Hom.Basic

open CategoryTheory

universe u

instance : Category (Type u) where
  Hom := (· → ·)
  id v := id
  comp f g := g ∘ f

instance {X : Sigma Preorder} : Preorder X.fst := X.snd
instance {X : Sigma PartialOrder} : PartialOrder X.fst := X.snd

instance preOrd : Category (Sigma Preorder) where
  Hom := fun s t => (f : s.fst → t.fst) ×' Monotone f
  id v := ⟨id, fun _ _ => id⟩
  comp := fun f g => ⟨g.fst ∘ f.fst, Monotone.comp g.snd f.snd⟩

instance poOrd : Category.{u, u + 1} (Sigma PartialOrder : Type (u+1)) where
  Hom a b := a.1 →o b.1
  id v := OrderHom.id
  comp a b := OrderHom.comp b a

instance poset {t : Type u} [Preorder t] : Category t where
  Hom a b := PLift (a ≤ b)
  id t := .up (le_refl t)
  comp := fun | .up f, .up g => .up <| le_trans f g

instance hmon : Category (Sigma Monoid) where
  Hom := fun ⟨s, is⟩ ⟨t, it⟩ => MonoidHom s t
  id  := fun ⟨v, iv⟩ => MonoidHom.id v
  comp := fun {a b c} f g =>
    have ⟨a, ia⟩ := a
    have ⟨b, ib⟩ := b
    have ⟨c, ic⟩ := c
    (MonoidHom.comp (g : _ →* _) (f : _ →* _) : _ →* _)

instance {X : Sigma Monoid} : Monoid X.fst := X.snd

/- instance emon {α} : Category (Monoid α) where -/
/-   Hom := fun s t => @MonoidHom α α s.toMulOneClass t.toMulOneClass -/
/-   id  := fun X => MonoidHom.id α -/
/-   comp := fun {X Y Z} f g => @MonoidHom.comp _ _ _ -/
/-     X.toMulOneClass Y.toMulOneClass Z.toMulOneClass g f -/

