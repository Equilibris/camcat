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

universe u v

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

section examples

def us : PSTrans where
  S := PUnit
  σ := Option.some

def un : PSTrans where
  S := PUnit
  σ := fun _ => Option.none

example : PSHom us un where
  f := id
  h := funext fun | .unit => by simp [un, us]

example : PSHom un us where
  f := id
  h := funext fun | .unit => by simp [un, us]

def bSsSs : PSTrans where
  S := Bool
  σ := Option.some

def bNN : PSTrans where
  S := Bool
  σ := fun _ => Option.none

def bSsN : PSTrans where
  S := Bool
  σ := fun | .true => .some .true | .false => .none

def bSdN : PSTrans where
  S := Bool
  σ := fun | .true => .some .false | .false => .none

def bNSs : PSTrans where
  S := Bool
  σ := fun | .false => .some .false | .true => .none

def bNSd : PSTrans where
  S := Bool
  σ := fun | .false => .some .true | .true => .none

example : PSHom bSdN bNSd where
  f := not
  h := funext fun | .true | .false => by simp [bSdN, bNSd]

example : PSHom bSsN bNSs where
  f := not
  h := funext fun | .true | .false => by simp [bSsN, bNSs]

example : PSHom bNN bSsN where
  f := fun _ => .false
  h := funext fun | .true | .false => rfl

end examples

instance : Category PSTrans where
  Hom := PSHom
  id X := ⟨id, funext fun v => by grind⟩
  comp {X Y Z} A B := ⟨B.f ∘ A.f, calc
    _ = Option.map B.f ∘ Option.map A.f ∘ X.σ := by rw [←Option.map_comp_map, Function.comp_assoc]
    _ = (Option.map B.f ∘ Y.σ) ∘ A.f          := by rw [A.h, ←Function.comp_assoc]
    _ = Z.σ ∘ B.f ∘ A.f                       := by rw [B.h, Function.comp_assoc]⟩

@[grind]
structure Conat : Type u where
  f : Nat → Bool
  stops : ∀ n, (f n) = .false → (f n.succ) = .false

namespace Conat

def step (x : Conat.{u}) : Conat.{u} where
  f := x.f ∘ .succ
  stops n h := x.stops n.succ h

theorem step_many {x : Conat}
    : {n : Nat} → n.repeat step x = ⟨(x.f <| n + ·), fun _ h => x.stops _ h⟩
  | 0 => by simp [Nat.repeat]
  | n+1 => by
    simp only [Nat.repeat, step, step_many, mk.injEq]
    grind

def dest (x : Conat.{u}) : Option Conat.{u} :=
  match x.f 0 with
  | .true => .some x.step
  | .false => .none

def corec.f {X : Type v}
    (gen : X → Option X)
    (g : X)
    : Nat → Bool 
  | 0   => 
    match gen g with 
    | .some _ => .true
    | .none   => .false
  | n+1 => match gen g with 
    | .some g => corec.f gen g n
    | .none   => .false

def corec {X : Type v}
    (gen : X → Option X)
    (g : X)
    : Conat where
  f := corec.f gen g
  stops n h := by 
    induction n generalizing g
    · dsimp [corec.f] at h ⊢
      grind
    case succ ih => 
      dsimp [corec.f] at h ⊢
      split at h
      · specialize ih _ h
        dsimp [corec.f] at ih
        split at ih
        · exact ih
        · rfl
      · rfl

def corec_dest
    {X : Type v}
    (gen : X → Option X)
    (g : X)
    : (Conat.corec gen g).dest = Option.map (Conat.corec gen) (gen g) := by
  dsimp [dest, corec, Option.map, corec.f]
  cases h : gen g
  · rfl
  · rename_i val
    simp only [step, Option.some.injEq, mk.injEq]
    funext n
    dsimp
    induction n
    · simp [corec.f, h]
    case succ ih => 
      dsimp [corec.f] at ih
      conv =>
        lhs
        dsimp [corec.f]
        rw [h]
        dsimp
      split at ih
      <;> rename_i heq
      · obtain rfl := (Option.some.injEq _ _).mp (h.symm.trans heq)
        rfl
      · exact Option.noConfusion (h.symm.trans heq)

def Bisim.Is (R : Conat → Conat → Prop) : Prop :=
  ∀ a b, R a b → Option.Rel R a.dest b.dest

def Bisim (a b : Conat) : Prop := ∃ R, Bisim.Is R ∧ R a b

theorem bisim {a b : Conat}
    (h : Bisim a b) : a = b := by
  rcases h with ⟨R, his, rab⟩
  obtain h := his _ _ rab
  have : ∀ n : Nat, Option.Rel R
      (n.repeat Conat.step a).dest
      (n.repeat Conat.step b).dest := by
    intro n
    induction n
    · exact h
    case succ n ih =>
      dsimp [Nat.repeat, dest, step] at ih
      split at ih
      <;> rename_i heq
      · split at ih
        case h_2 => cases ih
        rcases ih with ⟨ih⟩
        exact his _ _ ih
      · dsimp [dest, step, Nat.repeat]
        rw [(Nat.repeat step n a).stops 0 heq]
        split at ih
        · cases ih
        rename_i heq
        rw [(Nat.repeat step n b).stops 0 heq]
        exact .none
  clear h
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  refine (mk.injEq _ _ _ _).mpr <| funext fun n => ?_
  induction n
  · specialize this 0
    dsimp [dest] at this
    split at this
    all_goals split at this
    any_goals cases this
    all_goals simp_all only [Nat.repeat]
  case succ n ih =>
    specialize this n
    simp only [dest, step_many, add_zero] at this
    split at this
    · rename_i heq
      rw [←ih, heq] at this
      rcases this with ⟨this⟩
      have := his _ _ this
      simp [dest, step] at this
      clear *-this
      split at this
      <;> split at this
      <;> simp_all only [Option.rel_some_some,
        Option.not_rel_some_none, Option.not_rel_none_some,
        Option.rel_none_none]
    · grind

end Conat

instance : HasTerminal PSTrans :=
  IsTerminal.hasTerminal
    (X := ⟨Conat, Conat.dest⟩)
    <| IsTerminal.ofUniqueHom
      (fun x => {
        f := Conat.corec x.σ
        h := funext fun v => (Conat.corec_dest x.σ v).symm
      })
      fun x ⟨m, h⟩ => (PSHom.mk.injEq _ _ _ _).mpr
        (funext fun v => Conat.bisim 
          ⟨
            (∃ u, · = m u ∧ · = Conat.corec x.σ u), 
            by
              rintro a b ⟨w, rfl, rfl⟩
              rw [ Conat.corec_dest,
                ← show Option.map _ _ = (m w).dest from funext_iff.mp h w]
              cases x.σ w
              · exact .none
              · exact .some ⟨_, rfl, rfl⟩,
            ⟨v, rfl, rfl⟩
          ⟩
        )

end terminal

section initial

instance : HasInitial PSTrans :=
  IsInitial.hasInitial
    (X := ⟨PEmpty, fun _ => .none⟩)
    <| IsInitial.ofUniqueHom
      (fun _ => ⟨fun v => v.elim, funext fun v => v.elim⟩)
      (fun _ ⟨_, _⟩ =>
        (PSHom.mk.injEq _ _ _ _).mpr (funext fun v => v.elim))

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

section ex4a

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

theorem ex4.a
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

end ex4a

section ex4b

instance : Category (Sigma Fintype) where
  Hom a b := a.fst → b.fst
  id X := _root_.id
  comp a b := Function.comp b a

variable {X Y : Sigma Fintype}

instance : Fintype X.fst := X.snd

noncomputable instance : Fintype (X ⟶ Y) := by 
  have : DecidableEq X.fst := Classical.typeDecidableEq _
  have : DecidableEq Y.fst := Classical.typeDecidableEq _
  change Fintype (X.fst → Y.fst)
  infer_instance

instance : HasBinaryProduct X Y := 
  IsBinaryProduct.hasBinaryProduct (P := ⟨ X.fst × Y.fst, inferInstance ⟩)
    Prod.fst Prod.snd <|
  IsBinaryProduct.ofUniqueHom 
    (fun x y v => ⟨x v, y v⟩)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun f g m hf hg => by 
      funext v
      ext
      · change (Prod.fst ∘ m) _ = f v
        exact congrFun hf v
      · change (Prod.snd ∘ m) _ = g v
        exact congrFun hg v)

instance : HasBinaryProducts (Sigma Fintype) :=
  hasBinaryProducts_of_hasLimit_pair _

end ex4b

end product

section coproduct

section ex1

instance hamon : Category (Sigma AddCommMonoid) where
  Hom := fun ⟨s, is⟩ ⟨t, it⟩ => AddMonoidHom s t
  id  := fun ⟨v, iv⟩ => AddMonoidHom.id v
  comp := fun {a b c} f g =>
    have ⟨a, ia⟩ := a
    have ⟨b, ib⟩ := b
    have ⟨c, ic⟩ := c
    (AddMonoidHom.comp (g : _ →+ _) (f : _ →+ _) : _ →+ _)

variable {A B : Sigma AddCommMonoid} {X Y : Type _}
    [AddMonoid X] [AddMonoid Y]

instance : AddCommMonoid A.fst := A.snd

instance : HasBinaryProduct A B := 
  IsBinaryProduct.hasBinaryProduct (P := ⟨ A.fst × B.fst, by infer_instance⟩)
    (.fst _ _) (.snd _ _) <|.ofUniqueHom
    (fun f g => AddMonoidHom.prod f g)
    (fun f g => rfl)
    (fun f g => rfl)
    (fun f g m => by
      rintro rfl rfl; dsimp
      exact AddMonoidHom.prod_unique m)

def amInl : X →+ X × Y where
  toFun x := ⟨x, 0⟩
  map_zero':= rfl
  map_add' x y := by simp

def amInr : Y →+ X × Y where
  toFun x := ⟨0, x⟩
  map_zero':= rfl
  map_add' x y := by simp


instance : HasBinaryCoproduct A B := 
  IsBinaryCoproduct.hasBinaryCoproduct (P := ⟨ A.fst × B.fst, by infer_instance⟩)
    amInl amInr <|.ofUniqueHom
      (fun a b => {
        toFun := fun ⟨x, y⟩ => a.toFun x + b.toFun y
        map_add' := by 
          rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
          dsimp
          calc 
            a.toFun (x₁ + y₁) + b.toFun (x₂ + y₂)
              = a.toFun x₁ + a.toFun y₁ + (b.toFun x₂ + b.toFun y₂) := by simp
            _ = a.toFun x₁ + (a.toFun y₁ + b.toFun x₂) + b.toFun y₂ := by simp only [add_assoc]
            _ = a.toFun x₁ + (b.toFun x₂ + a.toFun y₁) + b.toFun y₂ := by nth_rw 3 [add_comm]
            _ = a.toFun x₁ + b.toFun x₂ + (a.toFun y₁ + b.toFun y₂) := by simp only [add_assoc]
        map_zero' := by simp
      })
      (fun f g => AddMonoidHom.ext fun x => by 
        simp [CategoryStruct.comp, amInl])
      (fun f g => AddMonoidHom.ext fun x => by 
        simp [CategoryStruct.comp, amInr])
      (fun f g m => by
        rintro rfl rfl; refine AddMonoidHom.ext fun ⟨x, y⟩ => ?_
        calc
          m.toFun (x, y)
            = m.toFun ((x, 0) + (0, y))        := by simp
          _ = m.toFun (x, 0) + m.toFun (0, y)  := m.map_add _ _)

end ex1

class Distributive 𝓒 [Category 𝓒] [HasBinaryProducts 𝓒] [HasBinaryCoproducts 𝓒] where
  dist : ∀ X Y Z : 𝓒, (X ⨯ Y) ⨿ (X ⨯ Z) ⟶ X ⨯ (Y ⨿ Z)
  dist_uniq : ∀ X Y Z d,
    prod.map (𝟙 X) coprod.inl = coprod.inl ≫ d →
      prod.map (𝟙 X) coprod.inr = coprod.inr ≫ d →
        dist X Y Z = d

section ex2

variable [Category 𝓒] [HasBinaryProducts 𝓒] [HasBinaryCoproducts 𝓒] [Distributive 𝓒]

end ex2

end coproduct

