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

noncomputable def pow_list (ls : List (A ⟶ B)) : (n : Nat) → List (A ⟶ pow B n)
  | 0 => ls
  | n+1 =>
    ls.flatMap fun f =>
    (pow_list ls n).map (prod.lift f)

theorem pow_list.nodup
    (ls : List (A ⟶ B))
    (hNd : ls.Nodup)
    : (n : Nat) → (pow_list ls n).Nodup
  | 0 => hNd
  | n+1 => by
    have := pow_list.nodup _ hNd n
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro h hmem
      refine List.Nodup.map ?_ this
      intro f₁ f₂ heq
      have ⟨_, heq⟩:= Limits.prod.hom_ext_iff.mp heq
      rwa [prod.lift_snd, prod.lift_snd] at heq
    · apply List.pairwise_of_forall_sublist
      intro a b subl
      change (List.map _ _).Disjoint (List.map _ _)
      intro v vamem vbmem
      simp at vamem vbmem
      rcases vamem with ⟨wa, wamem, rfl⟩
      rcases vbmem with ⟨wb, wbmem, hFalse⟩
      have ⟨hFalse, _⟩ := Limits.prod.hom_ext_iff.mp hFalse
      rw [prod.lift_fst, prod.lift_fst] at hFalse
      have : b ≠ a := by
        rintro rfl
        have := List.Nodup.sublist subl hNd
        simp at this
      exact this hFalse

theorem pow_list.length
    (ls : List (A ⟶ B))
    (hNd : ls.Nodup)
    : (n : Nat) → (pow_list ls n).length = ls.length ^ n.succ
  | 0 => by simp [pow_list]
  | n+1 => by
    simp [pow_list, pow_list.length _ hNd n, ←Nat.pow_add_one']

theorem pow_list.allMem
    (ls : List (A ⟶ B))
    (hAll : ∀ v, v ∈ ls)
    : (n : Nat) → ∀ v, v ∈ (pow_list ls n)
  | 0,   v => hAll v
  | n+1, v => by
    simp only [pow_list, List.mem_flatMap, List.mem_map]
    use v ≫ prod.fst, hAll _, v ≫ prod.snd, pow_list.allMem _ hAll n _
    calc
      _ = _                       := by rw [← @prod.comp_lift]
      _ = v ≫ 𝟙 (pow B (n + 1))   := by rw [@prod.lift_fst_snd]; rfl
      _ = v                       := by rw [Category.comp_id v]

lemma length_eq_of_bij
    {A B : Type _}
    {X : List A}
    {Y : List B}
    (f : A → B)
    (g : B → A)
    (hMemF : ∀ v ∈ X, f v ∈ Y)
    (hMemG : ∀ v ∈ Y, g v ∈ X)
    (hL : f ∘ g = id)
    (hR : g ∘ f = id)
    (ndX : X.Nodup)
    (ndY : Y.Nodup)
    : X.length = Y.length :=
  match X, Y with
  | [], [] => rfl
  | [], hb :: tb | ha :: ta, [] => by
    simp_all only [List.not_mem_nil, List.mem_cons]
    grind
  | ha :: ta, b => by
    have decEq : DecidableEq B := Classical.typeDecidableEq B

    have injF : Function.Injective f := Function.LeftInverse.injective (congrFun hR)

    have hMemF' : ∀ v ∈ ta, f v ∈ b.erase (f ha) := fun v hv => by
      have x := hMemF v (List.mem_cons_of_mem ha hv)
      clear *-injF x ndX ndY
      induction b
      · grind
      case cons hd tl ih =>
        by_cases h : f v = hd
        · subst h
          sorry
        · grind
    have hMemG' : ∀ v ∈ b.erase (f ha), g v ∈ ta := sorry
    have := length_eq_of_bij f g hMemF' hMemG' hL hR
    dsimp
    rw [this]
    exact List.length_erase_add_one (hMemF ha List.mem_cons_self)

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
  have : ∀ v, v ∈ mf.elems.toList :=
    (Finset.mem_toList.mpr <| mf.complete ·)
  have hLpln := pow_list.length mf.elems.toList (Finset.nodup_toList Fintype.elems) n
  have hLplk := pow_list.length mf.elems.toList (Finset.nodup_toList Fintype.elems) k
  have hMpln := pow_list.allMem mf.elems.toList this n
  have hMplk := pow_list.allMem mf.elems.toList this k
  have memBoth : ∀ (v : A ⟶ pow B n), v ∈ pow_list Fintype.elems.toList n
      ↔ (v ≫ eqToHom heq) ∈ pow_list Fintype.elems.toList k
      :=
    fun _ => ⟨fun _ => hMplk _, fun _ => hMpln _⟩
  have : (pow_list mf.elems.toList n).length = (pow_list mf.elems.toList k).length := by
    apply length_eq_of_bij (fun x => x ≫ eqToHom heq) (fun x => x ≫ eqToHom heq.symm)
    · exact fun v a ↦ hMplk (v ≫ eqToHom heq)
    · exact fun v a ↦ hMpln (v ≫ eqToHom (Eq.symm heq))
    · funext v
      dsimp
      rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    · funext v
      dsimp
      rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    · exact pow_list.nodup _ (Finset.nodup_toList Fintype.elems) _
    · exact pow_list.nodup _ (Finset.nodup_toList Fintype.elems) _
  have mfLenNT : 2 ≤ mf.elems.toList.length := by 
    rw [Finset.length_toList]
    rw [←Finset.card_pair hneq]
    apply Finset.card_le_card
    exact fun x _ => Fintype.complete x
  have := hLpln.symm.trans this |>.trans hLplk
  sorry

end ex4

end product

