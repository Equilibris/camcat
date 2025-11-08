/- import Mathlib.CategoryTheory.Category.Cat.Terminal -/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace CategoryTheory.Limits

universe u

variable
    {𝓒 : Type u}
    [Category 𝓒]
    {U V W X Y P T : 𝓒}

section prod

variable 
    (fst : P ⟶ X)
    (snd : P ⟶ Y)

def IsBinaryProduct :=
  IsLimit (BinaryFan.mk fst snd)

def IsBinaryProduct.ofUniqueHom {fst snd}
    (lift : {T : 𝓒} → (T ⟶ X) → (T ⟶ Y) → (T ⟶ P))
    (hl₁ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ fst = f)
    (hl₂ : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ snd = g)
    (uniq : ∀ {T} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ P), m ≫ fst = f → m ≫ snd = g → m = lift f g)
    : IsBinaryProduct fst snd :=
  BinaryFan.IsLimit.mk _ lift hl₁ hl₂ uniq

theorem IsBinaryProduct.hasBinaryProduct (h : IsBinaryProduct fst snd) : HasBinaryProduct X Y :=
  ⟨⟨{ cone := BinaryFan.mk fst snd, isLimit := h }⟩⟩

variable {fst snd}

def IsBinaryProduct.lift
    (h : IsBinaryProduct fst snd)
    {T : 𝓒}
    (f : T ⟶ X)
    (g : T ⟶ Y)
    : T ⟶ P :=
  IsLimit.lift h { pt := T, π := mapPair f g}

@[simp]
theorem IsBinaryProduct.lift_fst
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    : h.lift f g ≫ fst = f :=
  h.fac { pt := T, π := mapPair f g } (.mk .left)

@[simp]
theorem IsBinaryProduct.lift_snd
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    : h.lift f g ≫ snd = g :=
  h.fac { pt := T, π := mapPair f g } (.mk .right)

theorem IsBinaryProduct.uniq
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    (m : T ⟶ P)
    (hf : m ≫ fst = f)
    (hg : m ≫ snd = g)
    : m = h.lift f g :=
  IsLimit.uniq h { pt := T, π := mapPair f g } m fun
    | .mk .left => hf
    | .mk .right => hg

theorem IsBinaryProduct.hom_ext
    (h : IsBinaryProduct fst snd)
    {f g : T ⟶ P}
    (hl : f ≫ fst = g ≫ fst)
    (hr : f ≫ snd = g ≫ snd)
    : f = g :=
  BinaryFan.IsLimit.hom_ext h hl hr

@[simp]
theorem IsBinaryProduct.lift_fst_snd
    (h : IsBinaryProduct fst snd)
    : h.lift fst snd = 𝟙 _ :=
  h.hom_ext
    ((h.lift_fst _ _).trans (Category.id_comp _).symm)
    ((h.lift_snd _ _).trans (Category.id_comp _).symm)

@[simp]
theorem IsBinaryProduct.lift_comp 
    (h : IsBinaryProduct fst snd)
    (f : T ⟶ X)
    (g : T ⟶ Y)
    (v : V ⟶ T)
    : v ≫ h.lift f g = h.lift (v ≫ f) (v ≫ g) :=
  h.hom_ext
    (by simp)
    (by simp)

def IsBinaryProduct.iso
    {X Y P₁ P₂ : 𝓒}
    {fst₁ : P₁ ⟶ X} {snd₁ : P₁ ⟶ Y}
    {fst₂ : P₂ ⟶ X} {snd₂ : P₂ ⟶ Y}
    (h₁ : IsBinaryProduct fst₁ snd₁)
    (h₂ : IsBinaryProduct fst₂ snd₂)
    : P₁ ≅ P₂ where
  hom := h₂.lift fst₁ snd₁
  inv := h₁.lift fst₂ snd₂
  hom_inv_id := hom_ext h₁ (by simp) (by simp)
  inv_hom_id := hom_ext h₂ (by simp) (by simp)

noncomputable def productIsBinaryProduct [HasBinaryProduct X Y]
    : IsBinaryProduct (prod.fst : X ⨯ Y ⟶ X) prod.snd :=
  prodIsProd X Y

end prod

section coprod

variable
    (inl : X ⟶ P)
    (inr : Y ⟶ P)

def IsBinaryCoproduct :=
  IsColimit (BinaryCofan.mk inl inr)

def IsBinaryCoproduct.ofUniqueHom {inl inr}
    (desc : {T : _} → (X ⟶ T) → (Y ⟶ T) → (P ⟶ T))
    (hd₁ : ∀ {T : _} (f : X ⟶ T) (g : Y ⟶ T), inl ≫ desc f g = f)
    (hd₂ : ∀ {T : _} (f : X ⟶ T) (g : Y ⟶ T), inr ≫ desc f g = g)
    (uniq : ∀ {T : _} (f : X ⟶ T) (g : Y ⟶ T) (m : P ⟶ T), inl ≫ m = f → inr ≫ m = g → m = desc f g)
    : IsBinaryCoproduct inl inr :=
  BinaryCofan.IsColimit.mk _ desc  hd₁ hd₂ uniq

theorem IsBinaryCoproduct.hasBinaryCoproduct
    (h : IsBinaryCoproduct inl inr)
    : HasBinaryCoproduct X Y :=
  ⟨⟨{ cocone := BinaryCofan.mk inl inr, isColimit := h }⟩⟩

variable {inl inr}

def IsBinaryCoproduct.desc
    (h : IsBinaryCoproduct inl inr)
    {T : 𝓒}
    (f : X ⟶ T)
    (g : Y ⟶ T)
    : P ⟶ T :=
  IsColimit.desc h { pt := T, ι := mapPair f g }

@[simp]
theorem IsBinaryCoproduct.inl_desc
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    : inl ≫ h.desc f g = f :=
  h.fac { pt := T, ι := mapPair f g } (.mk .left)

@[simp]
theorem IsBinaryCoproduct.inr_desc
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    : inr ≫ h.desc f g = g :=
  h.fac { pt := T, ι := mapPair f g } (.mk .right)

theorem IsBinaryCoproduct.uniq
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    (m : P ⟶ T)
    (hf : inl ≫ m = f)
    (hg : inr ≫ m = g)
    : m = h.desc f g :=
  IsColimit.uniq h { pt := T, ι := mapPair f g } m fun
    | .mk .left => hf
    | .mk .right => hg

def IsBinaryCoproduct.hom_ext
    (h : IsBinaryCoproduct inl inr)
    {f g : P ⟶ T}
    (hl : inl ≫ f = inl ≫ g)
    (hr : inr ≫ f = inr ≫ g)
    : f = g :=
  BinaryCofan.IsColimit.hom_ext h hl hr

@[simp]
theorem IsBinaryCoproduct.inl_inr_desc
    (h : IsBinaryCoproduct inl inr)
    : h.desc inl inr = 𝟙 _ :=
  h.hom_ext
    ((h.inl_desc _ _).trans (Category.comp_id _).symm)
    ((h.inr_desc _ _).trans (Category.comp_id _).symm)

@[simp]
theorem IsBinaryCoproduct.desc_comp
    (h : IsBinaryCoproduct inl inr)
    (f : X ⟶ T)
    (g : Y ⟶ T)
    (v : T ⟶ V)
    : h.desc f g ≫ v = h.desc (f ≫ v) (g ≫ v) :=
  h.hom_ext
    (by rw [← Category.assoc]; simp)
    (by rw [← Category.assoc]; simp)

def IsBinaryCoproduct.iso
    {X Y P₁ P₂ : 𝓒}
    {inl₁ : X ⟶ P₁} {inr₁ : Y ⟶ P₁}
    {inl₂ : X ⟶ P₂} {inr₂ : Y ⟶ P₂}
    (h₁ : IsBinaryCoproduct inl₁ inr₁)
    (h₂ : IsBinaryCoproduct inl₂ inr₂)
    : P₁ ≅ P₂ where
  hom := h₁.desc inl₂ inr₂
  inv := h₂.desc inl₁ inr₁
  hom_inv_id := hom_ext h₁ (by simp) (by simp)
  inv_hom_id := hom_ext h₂ (by simp) (by simp)

noncomputable def coproductIsBinaryCoproduct [HasBinaryCoproduct X Y]
    : IsBinaryCoproduct (coprod.inl : X ⟶ X ⨿ Y) coprod.inr :=
  coprodIsCoprod X Y

end coprod

end CategoryTheory.Limits

