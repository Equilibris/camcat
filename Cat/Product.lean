import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Iso

namespace CategoryTheory.Limits

universe u

variable {𝓒 : Type u} [Category 𝓒] {X Y P : 𝓒} (fst : P ⟶ X) (snd : P ⟶ Y)

def IsBinaryProduct :=
  Limits.IsLimit (Limits.BinaryFan.mk fst snd)

def IsBinaryProduct.ofUniqueHom {fst snd}
    (lift : {T : 𝓒} → (T ⟶ X) → (T ⟶ Y) → (T ⟶ P))
    (hl₁ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ fst = f)
    (hl₂ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ snd = g)
    (uniq : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ P), m ≫ fst = f → m ≫ snd = g → m = lift f g)
    : IsBinaryProduct fst snd :=
  Limits.BinaryFan.IsLimit.mk _ lift hl₁ hl₂ uniq

theorem IsBinaryProduct.hasBinaryProduct (h : IsBinaryProduct fst snd) : HasBinaryProduct X Y :=
  ⟨⟨{ cone := BinaryFan.mk fst snd, isLimit := h }⟩⟩

noncomputable def productIsBinaryProduct [HasBinaryProduct X Y]
    : IsBinaryProduct (prod.fst : X ⨯ Y ⟶ X) prod.snd :=
  IsBinaryProduct.ofUniqueHom 
    prod.lift
    prod.lift_fst
    prod.lift_snd
    (fun {T} f g m hf hg => by
      dsimp
      ext
      · rw [hf, prod.lift_fst f g]
      · rw [hg, prod.lift_snd f g])


end CategoryTheory.Limits

