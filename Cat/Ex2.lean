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
import Cat.L2Live
import Cat.Product

open CategoryTheory Limits

universe u

variable {𝓒 : Type u} [Category 𝓒] {A B X Y Z X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝓒}

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

instance : HasTerminal PSTrans :=
  IsTerminal.hasTerminal 
    (X := ⟨Option PUnit, fun | .some _ => .some (.some .unit) | .none => .none⟩) 
    <| IsTerminal.ofUniqueHom
      (fun x => by
          stop
          exact ⟨
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

instance : HasInitial PSTrans :=
  IsInitial.hasInitial 
    (X := ⟨Option PUnit, fun | .some _ => .some (.some .unit) | .none => .none⟩)
    <| IsInitial.ofUniqueHom
      sorry
      sorry

end initial

section product

section ex1

variable
    [HasBinaryProduct X₁ X₂]
    [HasBinaryProduct Y₁ Y₂]
    [HasBinaryProduct Z₁ Z₂]

theorem ex1.a (f : X ⟶ Y) (g₁ : Y ⟶ Z₁) (g₂ : Y ⟶ Z₂)
    : f ≫ prod.lift g₁ g₂ = prod.lift (f ≫ g₁) (f ≫ g₂) := by
  ext
  · calc
      (f ≫ prod.lift g₁ g₂) ≫ prod.fst
        = f ≫ (prod.lift g₁ g₂ ≫ prod.fst)        := Category.assoc _ _ _
      _ = f ≫ g₁                                  := by rw [prod.lift_fst]
      _ = prod.lift (f ≫ g₁) (f ≫ g₂) ≫ prod.fst  := by rw [prod.lift_fst]
  · calc
      (f ≫ prod.lift g₁ g₂) ≫ prod.snd
        = f ≫ (prod.lift g₁ g₂ ≫ prod.snd)        := Category.assoc _ _ _
      _ = f ≫ g₂                                  := by rw [prod.lift_snd]
      _ = prod.lift (f ≫ g₁) (f ≫ g₂) ≫ prod.snd  := by rw [prod.lift_snd]

lemma map_def
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    : prod.map f₁ f₂ = prod.lift (prod.fst ≫ f₁) (prod.snd ≫ f₂) := 
  (prod.lift_fst_comp_snd_comp f₁ f₂).symm

theorem ex1.b
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Z ⟶ X₁) (g₂ : Z ⟶ X₂)
    : prod.lift g₁ g₂ ≫ prod.map f₁ f₂ = prod.lift (g₁ ≫ f₁) (g₂ ≫ f₂) := by
  rw [
    map_def,
    ex1.a,
    ←Category.assoc, ←Category.assoc,
    prod.lift_fst, prod.lift_snd]

theorem ex1.c1
    (f₁ : Y₁ ⟶ Z₁) (f₂ : Y₂ ⟶ Z₂)
    (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂)
    : prod.map g₁ g₂ ≫ prod.map f₁ f₂ = prod.map (g₁ ≫ f₁) (g₂ ≫ f₂) := by
  rw [
    map_def,
    map_def,
    ex1.a,
    ←Category.assoc, ←Category.assoc,
    prod.lift_fst, prod.lift_snd,
    Category.assoc, Category.assoc,
    ←map_def,
  ]

theorem ex1.c2
    : prod.map (𝟙 X₁) (𝟙 X₂) = 𝟙 _ := by
  rw [
    map_def,
    Category.comp_id, Category.comp_id,
    prod.lift_fst_snd
  ]

def AnUnit (_x : Type u) := PUnit

instance {α : Type u} [Monoid α] : Category (AnUnit α) where
  Hom a b := α
  id x := 1
  comp a b := b * a
  assoc f g h := Eq.symm (mul_assoc h g f)

end ex1

theorem ex2 {α}
    [Monoid α]
    (op : α → α → α)
    (p₁ p₂ : α)
    (h₁ : ∀ x y, p₁ * (op x y) = x)
    (h₂ : ∀ x y, p₂ * (op x y) = y)
    (h₃ : op p₁ p₂ = 1)
    (h₄ : ∀ x y z, (op x y) * z = op (x * z) (y * z))
    (a b : AnUnit α)
    : HasBinaryProduct a b :=
  IsBinaryProduct.hasBinaryProduct (P := .unit) p₁ p₂
  <| IsBinaryProduct.ofUniqueHom op h₁ h₂
    fun (f g m : α) (hf : p₁ * m = f) (hg : p₂ * m = g) => calc
      m = 1 * m                 := Eq.symm (one_mul m)
      _ = op p₁ p₂ * m          := by rw [h₃]
      _ = op (p₁ * m) (p₂ * m)  := by rw [h₄]
      _ = op f g                := by rw [hf, hg]

noncomputable section ex3

variable (X Y Z)
    [HasBinaryProduct X Y]
    [HasBinaryProduct Y Z]
    [HasBinaryProduct X (Y ⨯ Z)]
    [HasBinaryProduct (X ⨯ Y) Z]
    [HasTerminal 𝓒]
    [HasBinaryProduct X (⊤_ 𝓒)]
    [HasBinaryProduct (⊤_ 𝓒) X]
    [HasBinaryProduct Y X]

def α : (X ⨯ Y) ⨯ Z ≅ X ⨯ (Y ⨯ Z) where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.map prod.snd (𝟙 _))
  inv := prod.lift (prod.map (𝟙 _) prod.fst) (prod.snd ≫ prod.snd)

def «λ» : X ⨯ ⊤_ _ ≅ X where
  hom := prod.fst
  inv := prod.lift (𝟙 X) (terminal.from X)

def ρ : (⊤_ _) ⨯ X ≅ X where
  hom := prod.snd
  inv := prod.lift (terminal.from X) (𝟙 X)

def τ : X ⨯ Y ≅ Y ⨯ X where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

end ex3

section ex4

variable
  [HasBinaryProducts 𝓒]

noncomputable def pow (O : 𝓒) : Nat → 𝓒
  | 0 => O
  | n+1 => O ⨯ pow O n

lemma finsetGeneration'
    {A : Type u}
    [Fintype A]
    (f : Nat → A)
    : ∃ n, ∃ k, n ≠ k ∧ f n = f k := by
  by_contra! h
  exact not_injective_infinite_finite f
    <| Function.injective_iff_pairwise_ne.mpr h

lemma finsetGeneration
    {A : Type u}
    [Fintype A]
    (f : Nat → A)
    : ∃ n, ∃ k, n < k ∧ f n = f k := by
  have ⟨a, b, hneq, heq⟩:= finsetGeneration' f
  by_cases hlt : a < b
  · use a, b
  · have hlt : b < a := by omega
    use b, a
    exact ⟨hlt, heq.symm⟩

noncomputable def pow_list (ls : Finset (A ⟶ B)) : (n : Nat) → Finset (A ⟶ pow B n)
  | 0 => ls
  | n+1 =>
    ls.disjiUnion (fun f => (pow_list ls n).map ⟨
      (prod.lift f),
      fun x y heq => by 
        have ⟨_, heq⟩:= Limits.prod.hom_ext_iff.mp heq
        rwa [prod.lift_snd, prod.lift_snd] at heq
    ⟩) fun a amem b bmem hneq v vamem vbmem z zmem => by
        exfalso
        specialize vamem zmem
        specialize vbmem zmem
        simp at vamem vbmem
        rcases vamem with ⟨wa, wamem, rfl⟩
        rcases vbmem with ⟨wb, wbmem, hFalse⟩
        have ⟨hFalse, _⟩ := Limits.prod.hom_ext_iff.mp hFalse
        simp at hFalse
        exact hneq hFalse.symm

theorem pow_list.card
    (ls : Finset (A ⟶ B))
    : (n : Nat) → (pow_list ls n).card = ls.card ^ n.succ
  | 0 => by simp [pow_list]
  | n+1 => by simp [pow_list, pow_list.card _ n, ←Nat.pow_add_one']

theorem pow_list.allMem
    (ls : Finset (A ⟶ B))
    (hAll : ∀ v, v ∈ ls)
    : (n : Nat) → ∀ v, v ∈ (pow_list ls n)
  | 0,   v => hAll v
  | n+1, v => by
    simp only [pow_list, Finset.mem_disjiUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
    use v ≫ prod.fst, hAll _, v ≫ prod.snd, pow_list.allMem _ hAll n _
    calc
      _ = _                       := by rw [← @prod.comp_lift]
      _ = v ≫ 𝟙 (pow B (n + 1))   := by rw [@prod.lift_fst_snd]; rfl
      _ = v                       := by rw [Category.comp_id v]

theorem ex4
    [objFin : Fintype 𝓒]
    [morphFin : ∀ A B : 𝓒, Fintype (A ⟶ B)]
    : ∀ A B : 𝓒, Subsingleton (A ⟶ B) := by
  have deq : DecidableEq 𝓒 := Classical.typeDecidableEq 𝓒
  by_contra! h
  simp only [subsingleton_iff, not_forall] at h
  rcases h with ⟨A,B,f,g,hneq⟩
  have deqhom: DecidableEq (A ⟶ B) := Classical.typeDecidableEq _
  have mf := morphFin A B
  have ⟨n, k, hlt, heq⟩:= finsetGeneration (pow B)
  have hLpln := pow_list.card mf.elems n
  have hLplk := pow_list.card mf.elems k
  have hMpln := pow_list.allMem mf.elems Fintype.complete n
  have hMplk := pow_list.allMem mf.elems Fintype.complete k
  have : (pow_list mf.elems n).card = (pow_list mf.elems k).card := by
    apply Finset.card_bijective (· ≫ eqToHom heq) 
    · refine Function.bijective_iff_has_inverse.mpr ?_
      use (· ≫ eqToHom (Eq.symm heq))
      constructor <;> intro _ <;> simp
    · intro i
      exact ⟨fun a ↦ hMplk _, fun a ↦ hMpln _⟩
  have mfLenNT : 2 ≤ mf.elems.card := by 
    rw [←Finset.card_pair hneq]
    apply Finset.card_le_card
    exact fun x _ => Fintype.complete x
  have hFalse : Nat.pow _ _ = Nat.pow _ _ := hLpln.symm.trans this |>.trans hLplk
  generalize mf.elems.card = c at *
  clear *-hFalse mfLenNT hlt
  have := (Nat.pow_right_inj (by omega)).mp hFalse
  omega

end ex4

end product

