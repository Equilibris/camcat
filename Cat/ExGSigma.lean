import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic.Group
import Mathlib.Tactic.DepRewrite
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Basic
import Mathlib.Logic.Relation
import Cat.L1
import Cat.L2Live
import Cat.Product

universe u v

namespace List

variable {n : Nat} {A B : Type u}

structure σ (n : Nat) where
  f : Fin n → Fin n
  bij : Function.Bijective f

-- Working with these is extremely painful as they are not what multisets expect
-- Therefore this following section justifies how these are equivilent to an inductive definition.
-- The point of this is to change the definition to talk about perms,
-- rather than using sigmas directly.
-- The definition of Perm is as follows:

/--
info: inductive List.Perm.{u} : {α : Type u} → List α → List α → Prop
number of parameters: 1
constructors:
List.Perm.nil : ∀ {α : Type u}, [] ~ []
List.Perm.cons : ∀ {α : Type u} (x : α) {l₁ l₂ : List α}, l₁ ~ l₂ → x :: l₁ ~ x :: l₂
List.Perm.swap : ∀ {α : Type u} (x y : α) (l : List α), y :: x :: l ~ x :: y :: l
List.Perm.trans : ∀ {α : Type u} {l₁ l₂ l₃ : List α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
-/
#guard_msgs in
#print List.Perm

-- Notably this isnt data-carrying.
-- As shown in a proof bellow, whenever you have a perm, you can construct a σ.
-- I would almost ignore this section as it is just gruntwork and pure De Bruijn factor


-- We define sigma application as expected
def apply_sig (l : List A) (s : σ l.length) : List A := List.ofFn (l.get ∘ s.f)

section sigma_is_permunation

-- Any function along with a proof that it is bijective,
-- is equivilent to an equivelence from and onto iteself (A ≃ A).
-- In lean we alias A ≃ A as Equiv.Perm A
noncomputable def sigmaBij_equiv_EquivPerm
    : ((f : A → A) ×' Function.Bijective f) ≃ Equiv.Perm A where
  toFun := fun ⟨f, bij⟩ =>
    have eq := (Function.bijective_iff_has_inverse.mp bij)
    let inv := Classical.choose eq
    let eqs := Classical.choose_spec eq
    {
      toFun := f
      invFun := inv
      left_inv := eqs.1
      right_inv := eqs.2
    }
  invFun := fun ⟨f, inv, ha, hb⟩ =>
    ⟨f, Function.bijective_iff_has_inverse.mpr ⟨inv, ha, hb⟩⟩
  left_inv := by
    rintro ⟨x, bij⟩
    simp
  right_inv := by
    rintro ⟨f, inv, ha, hb⟩
    simp
    generalize_proofs p
    funext v 
    obtain ⟨a, rfl, -⟩ := Function.Bijective.existsUnique
      (Function.bijective_iff_has_inverse.mpr p) v
    have ⟨hl, _⟩ := Classical.choose_spec p
    rw [ha, hl]

def σ.unfold : σ n ≃ ((f : Fin n → Fin n) ×' Function.Bijective f) := {
  toFun := fun ⟨f,bij⟩ => ⟨f, bij⟩
  invFun := fun ⟨f,bij⟩ => ⟨f, bij⟩
}

noncomputable def σ.isEquivPerm {n} : σ n ≃ Equiv.Perm (Fin n) :=
  σ.unfold.trans sigmaBij_equiv_EquivPerm

-- supprisingly easy theorem using the a proof from mathlib.
theorem apply_sig_Perm {l : List A} {s : σ _} : List.Perm (l.apply_sig s) l := by
  dsimp [List.apply_sig]
  let x := σ.isEquivPerm.toFun s
  have : s.f = x := rfl
  rw [this]
  have eq := Equiv.Perm.ofFn_comp_perm x (List.get l)
  rw [List.ofFn_get] at eq
  exact eq

@[simp]
theorem apply_sig_length {l : List A} {s : σ _} : (l.apply_sig s).length = l.length :=
  List.Perm.length_eq List.apply_sig_Perm

-- This is in mathlib, I actually pushed it there
-- The problem is my mathlib is too out of date so i copied it here.
theorem dcongr_heq
    {α₁ α₂ : Sort u}
    {β₁ : α₁ → Sort v} {β₂ : α₂ → Sort v}
    {f₁ : ∀ a, β₁ a} {f₂ : ∀ a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hargs : a₁ ≍ a₂)
    (ht : ∀ t₁ t₂, t₁ ≍ t₂ → β₁ t₁ = β₂ t₂)
    (hf : α₁ = α₂ → β₁ ≍ β₂ → f₁ ≍ f₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl

-- This proof could be made constructive by transforming Perm to reside in Type
-- This is by far the most gruntworky section component of the proof.
theorem Perm_apply_sig : {l₁ l₂ : List A} → l₁.Perm l₂ → ∃ s, l₁.apply_sig s = l₂ := by
  intro l₁ l₂ perm
  induction perm
  · exact ⟨⟨_, Function.bijective_id⟩, rfl⟩
  case cons ih =>
    have ⟨⟨f, ⟨finj, fsur⟩⟩, feq⟩ := ih
    exact ⟨
      ⟨
        (fun
          | Fin.mk 0 h => Fin.mk 0 h
          | Fin.mk (n+1) h => Fin.succ (f ⟨n, Nat.succ_lt_succ_iff.mp h⟩)),
        ⟨
          fun a b h => by
            dsimp at h
            split at h
            <;> split at h
            <;> simp_all [Fin.succ]
            · rename_i n₁ hn₁ _ n₂ hn₂
              have := finj (Fin.eq_of_val_eq h)
              simp_all
            ,
          fun
            | ⟨0, h⟩ => ⟨⟨0, h⟩, rfl⟩
            | ⟨n+1, h⟩ => by
              have ⟨w, h⟩ := fsur ⟨n, Nat.succ_lt_succ_iff.mp h⟩
              use (.succ w)
              simp [Fin.succ, h]
        ⟩
      ⟩,
      by
        rw [←feq]
        simp only [List.apply_sig, List.length_cons, Fin.zero_eta, List.ofFn_succ,
          Function.comp_apply, List.get_eq_getElem, List.cons.injEq, List.ofFn_inj]
        constructor
        · rfl
        · rfl
    ⟩
  case swap =>
    exact ⟨
      ⟨
        fun 
          | ⟨0,_⟩ => ⟨1, by simp⟩
          | ⟨1,_⟩ => ⟨0, by simp⟩
          | x@⟨n+2,_⟩ => x,
        ⟨
          fun a b h => by
            dsimp at h
            split at h
            <;> split at h
            <;> simp_all,
          fun
            | ⟨0,_⟩ => ⟨⟨1, by simp⟩, rfl⟩
            | ⟨1,_⟩ => ⟨⟨0, by simp⟩, rfl⟩
            | ⟨n+2, h⟩ => ⟨⟨n+2, h⟩, rfl⟩,
        ⟩,
      ⟩,
      by
        simp only [List.apply_sig, List.length_cons, Fin.mk_one, Fin.zero_eta, List.ofFn_succ,
          Function.comp_apply, List.get_eq_getElem, Fin.succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          zero_add, Nat.succ_eq_add_one, List.getElem_cons_succ, List.ofFn_getElem, List.cons.injEq,
          and_true]
        refine ⟨rfl, rfl⟩,
    ⟩
  case trans x y z p₁ _ iha ihb=>
  /- | x, z, .trans (l₂ := y) p₁ p₂ =>  -/
    have ⟨⟨f, fbij⟩, hEqf⟩ := iha
    have ⟨⟨g, gbij⟩, hEqg⟩ := ihb
    have := List.Perm.length_eq p₁
    exact ⟨
      ⟨
        f ∘ (this ▸ g),
        Function.Bijective.comp fbij (by grind)
      ⟩,
      by
        simp only [List.apply_sig] at hEqf hEqg ⊢
        rw [←List.ofFn_get z] at hEqg ⊢
        rw [←List.ofFn_get y] at hEqf
        have hEqg' := List.ofFn_inj'.mp hEqg
        have hEqf' := List.ofFn_inj'.mp hEqf
        clear *-hEqg' hEqf'
        apply List.ofFn_inj'.mpr
        simp only [Sigma.mk.injEq] at hEqg' hEqf' ⊢
        refine ⟨by simp_all, ?_⟩
        change (_ ∘ f) ∘ _ ≍ _
        rw! [hEqf'.2, ←hEqg'.2]
        simp only [heq_cast_iff_heq]
        apply dcongr_heq
        · exact eqRec_heq_self (motive := fun x h ↦ Fin x → Fin x) g (Eq.symm this)
        · simp_all
        rintro - -
        apply dcongr_heq
        · exact cast_heq (Eq.symm (type_eq_of_heq hEqf'.right)) y.get
        · simp_all
        rintro - -
        congr!
    ⟩

theorem ex_sigma_perm {l₁ l₂ : List A} (h : ∃ s, l₁.apply_sig s = l₂) : l₁.Perm l₂ := by
  rcases h with ⟨s, rfl⟩
  exact Perm.symm apply_sig_Perm

-- Finally we can show my notion is equivilent to the one given in the task
theorem sigma_is_permunation
    {P : List A → List A → Prop}
    : (∀ l : List A, ∀ σ : σ l.length, P l (l.apply_sig σ))
    ↔ (∀ l₁ l₂, l₁.Perm l₂ → P l₁ l₂) where
  mp  h l₁ l₂ hperm := by
    obtain ⟨s, rfl⟩ := List.Perm_apply_sig hperm
    exact h l₁ s
  mpr h l σ :=
    h l (l.apply_sig σ) <| List.Perm.symm List.apply_sig_Perm

end sigma_is_permunation

end List

