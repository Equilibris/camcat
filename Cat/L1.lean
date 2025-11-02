import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open CategoryTheory

universe u

instance : Category (Type u) where
  Hom := (· → ·)
  id v := id
  comp f g := g ∘ f

instance preOrd : Category (Sigma Preorder) where
  Hom := fun ⟨s, is⟩ ⟨t, it⟩ => (f : s → t) ×' Monotone f
  id v := ⟨id, fun _ _ => id⟩
  comp := fun {a b c} ⟨f, fm⟩ ⟨g, gm⟩ =>
    have ⟨a, ia⟩ := a
    have ⟨b, ib⟩ := b
    have ⟨c, ic⟩ := c
    ⟨g ∘ f, Monotone.comp gm fm⟩

instance poOrd : Category (Sigma PartialOrder) where
  Hom := fun ⟨s, is⟩ ⟨t, it⟩ => (f : s → t) ×' Monotone f
  id v := ⟨id, fun x y a ↦ a⟩
  comp := fun {a b c} ⟨f, fm⟩ ⟨g, gm⟩ =>
    have ⟨a, ia⟩ := a
    have ⟨b, ib⟩ := b
    have ⟨c, ic⟩ := c
    ⟨g ∘ f, Monotone.comp gm fm⟩

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

instance emon {α} : Category (Monoid α) where
  Hom := fun s t => @MonoidHom α α s.toMulOneClass t.toMulOneClass
  id  := fun X => MonoidHom.id α
  comp := fun {X Y Z} f g => @MonoidHom.comp _ _ _
    X.toMulOneClass Y.toMulOneClass Z.toMulOneClass g f


