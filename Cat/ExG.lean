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
import Cat.L1
import Cat.L2Live
import Cat.Product

universe u

namespace CategoryTheory

-- We consider some general category 𝓒
variable {𝓒 : Type u} [Category 𝓒]

-- And some objects in 𝓒
variable {X Y Z A B C U V W L : 𝓒}

-- Along with some morphisms
variable {f g : X ⟶ Y}

section Ex1

-- A morphism f : X ⟶ Y is a monomorphism if it is left-cancellabe.
-- Here is the definition provided by mathlib.
/--
info: constructor CategoryTheory.Mono.mk.{v, u} : ∀ {C : Type u} [inst : Category.{v, u} C] {X Y : C} {f : X ⟶ Y},
  (∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h) → Mono f
-/
#guard_msgs in
#print Mono.mk

section Ex1_1

-- A morphism s : X ⟶ Y is a *section* if:
class Section (s : X ⟶ Y) where
  -- There exists some morphism
  r : Y ⟶ X
  -- such that
  s_r_involution : s ≫ r = 𝟙 X
  -- NOTE! We write s ≫ r for r ∘ s due to mathlib prefering this

instance
    -- For any
    {s : X ⟶ Y}
    -- satisfying
    [hSec : Section s]
    -- it follows that it is a
    : Mono s where
  right_cancellation
      -- For some object
      {Z}
      -- and morphisms
      (g h : Z ⟶ X)
      -- satisfying
      (heq : g ≫ s = h ≫ s)
      -- we are RTP
      : g = h := calc
    g = g ≫ 𝟙 X           := (Category.comp_id g).symm
    _ = g ≫ (s ≫ hSec.r)  := by rw [hSec.s_r_involution]
    _ = (g ≫ s) ≫ hSec.r  := (Category.assoc g s hSec.r).symm
    _ = (h ≫ s) ≫ hSec.r  := by rw [heq]
    _ = h ≫ (s ≫ hSec.r)  := (Category.assoc h s hSec.r)
    _ = h ≫ 𝟙 X           := by rw [hSec.s_r_involution]
    _ = h                 := (Category.comp_id h)

end Ex1_1

section Ex1_2

-- An
class Equalizer
    {L X Y : 𝓒}
    -- is a morphism
    (l : (L ⟶ X))
    -- over some pair
    (f g : (X ⟶ Y))
    where
  -- whenever
  leq : l ≫ f = l ≫ g
  -- and
  uniq
    -- for every object and morphism
    {K} (k : K ⟶ X)
    -- satisfying
    : k ≫ f = k ≫ g
    -- we can conclude
    → ∃! u : K ⟶ L, u ≫ l = k

instance Equalizer.mono
    {L X Y : 𝓒} {f g : X ⟶ Y} {l : L ⟶ X}
    (hEqz : Equalizer l f g)
    : Mono l where
  right_cancellation
      -- For some object
      {Z}
      -- and morphisms
      (u v : Z ⟶ L)
      -- satisfying
      (heq : u ≫ l = v ≫ l)
      -- we are RTP
      : u = v :=

    -- We can first conclude that
    have ulfEqUlg : (u ≫ l) ≫ f = (u ≫ l) ≫ g := calc
      (u ≫ l) ≫ f
        = u ≫ (l ≫ f) := Category.assoc u l f
      _ = u ≫ (l ≫ g) := by rw [hEqz.leq]
      _ = (u ≫ l) ≫ g := (Category.assoc u l g).symm

    -- Then we can see we can instantiate hEqz.uniq
    -- using the equality we just showed.
    have ⟨
      -- This gives us the morphism
      (w : Z ⟶ L),
      -- satisfying
      (wlEqUl : w ≫ l = u ≫ l),
      -- which is also unique.
      -- It is just the uniqueness we need.
      (huniq : ∀ (y : Z ⟶ L), y ≫ l = u ≫ l → y = w)
    ⟩ := hEqz.uniq (u ≫ l) ulfEqUlg

    calc
      u = w :=
        -- trivially, since u ≫ l = u ≫ l,
        -- we can conclude u = w.
        huniq u rfl
      w = v :=
        -- then using the assumtion heq : u ≫ l = v ≫ l
        -- we can conclude v = w.
        (huniq v heq.symm).symm

end Ex1_2

section Ex1_3

class Regular (l : L ⟶ X) where
  (Y : 𝓒)
  (f g : X ⟶ Y)
  hEqz : Equalizer l f g

instance
    {s : L ⟶ X}
    [hSec : Section s]
    : Regular s where
  -- We pick
  Y := X
  -- and the morphisms
  f := 𝟙 X
  g := hSec.r ≫ s

  -- Now it remains to show s forms an equalizer 𝟙 X and Section.r s ≫ s.
  hEqz := {
    -- We construct the equality proof.
    leq := (calc
      s ≫ 𝟙 X
        = s                 := Category.comp_id s
      _ = 𝟙 L ≫ s           := (Category.id_comp s).symm
      _ = (s ≫ hSec.r) ≫ s  := by rw [hSec.s_r_involution]
      _ = s ≫ hSec.r ≫ s    := Category.assoc s (Section.r s) s)
    -- Now it remains to show that s is unique.
    uniq
        {K}
        (k : K ⟶ X)
        (heq : k ≫ 𝟙 X = k ≫ hSec.r ≫ s)
        : ∃! x, x ≫ s = k := by
      -- We begin by chancing the goal using the assumtion.
      rw [show k = k ≫ hSec.r ≫ s from (Category.comp_id _).symm.trans heq]
      clear heq
      -- Now we are RTP: ∃! x, x ≫ s = k ≫ Section.r s ≫ s
      exact ⟨
        -- We pick the structure that makes the equality the easiest.
        k ≫ hSec.r,
        -- This collapses the equality into simply associativity
        Category.assoc k (Section.r s) s,
        -- Finally now to show the uniqueness follows cleanly
        fun y (hyeq : y ≫ s = k ≫ hSec.r ≫ s) => calc
          y = y ≫ 𝟙 L                   := (Category.comp_id y).symm
          _ = y ≫ (s ≫ hSec.r)          := by rw [hSec.s_r_involution]
          _ = (y ≫ s) ≫ hSec.r          := (Category.assoc y s hSec.r).symm
          _ = (k ≫ hSec.r ≫ s) ≫ hSec.r := by rw [hyeq]
          _ = k ≫ hSec.r ≫ (s ≫ hSec.r) := by simp only [Category.assoc]
          _ = k ≫ hSec.r ≫ 𝟙 _          := by rw [hSec.s_r_involution]
          _ = (k ≫ hSec.r) ≫ 𝟙 _        := (Category.assoc k hSec.r (𝟙 L)).symm
          _ = k ≫ hSec.r                := Category.comp_id (k ≫ Section.r s)
      ⟩
  }

end Ex1_3

section Ex1_4

class Strong (m : X ⟶ Y) where
  strong :
    ∀ {U V},
    ∀ e : U ⟶ V,
    ∀ u v,
    Epi e → e ≫ v = u ≫ m → ∃! d : V ⟶ X, u = e ≫ d ∧ d ≫ m = v

instance
    {m : X ⟶ Y}
    [hReg : Regular m]
    : Strong m where
  strong {U V} e u v eepi hComm := by
    have ⟨
      -- We begin by using the fact that any equalizer is a monomorphism.
      -- This will be used to right cancel m.
      (hRightCancel : ∀ {Z : 𝓒} (g h : Z ⟶ X), g ≫ m = h ≫ m → g = h)
    ⟩ := Equalizer.mono hReg.hEqz

    -- We expand the hypothesis into its induvidual parts.
    -- This is done to just save space.
    rcases hReg with ⟨
      -- Call the object
      Z,
      -- and the morphisms
      f,
      g,
      -- We get that the expected square commutes
      mfEqMg : m ≫ f = m ≫ g,
      -- along with its uniqueness.
      -- This uniqueness will generate the needed morphism
      uniq : ∀ {K} (k : K ⟶ Y), k ≫ f = k ≫ g → ∃! u, u ≫ m = k
    ⟩

    -- This equality will be used to instantiate the uniqueness just above.
    -- The proof proceeds usind the left cancellation of e
    have vfEqVg : v ≫ f = v ≫ g := eepi.left_cancellation (v ≫ f) (v ≫ g) <|
      -- This proof can be made much simpler (by simp [hComm, mfEqMg]),
      -- but I keep it in the calculative format to make it more visible.
      calc
        e ≫ v ≫ f
          = (e ≫ v) ≫ f := (Category.assoc e v f).symm
        _ = (u ≫ m) ≫ f := by rw [hComm]
        _ = u ≫ (m ≫ f) := (Category.assoc _ _ _)
        _ = u ≫ (m ≫ g) := by rw [mfEqMg]
        _ = (u ≫ m) ≫ g := (Category.assoc _ _ _).symm
        _ = (e ≫ v) ≫ g := by rw [hComm]
        _ = e ≫ v ≫ g   := Category.assoc e v g

    obtain ⟨
      -- We construct the morphism
      (w : V ⟶ X),
      -- this syntax eliminates the equality so we are effectively rewriting with it
      (rfl : w ≫ m = v),
      -- We are then also given the uniqueness bellow.
      -- This will lift exactly to the uniqueness needed for the proof.
      (huniq : ∀ x, x ≫ m = w ≫ m → x = w)
    ⟩ := uniq v vfEqVg; clear uniq

    -- Finally, now we are RTP: ∃! d, u = e ≫ d ∧ d ≫ m = w ≫ m
    refine ⟨
      -- We use the constructed morphism as d
      w,
      ⟨
        -- Applying the right cancellation, we're RTP: u ≫ m = (e ≫ w) ≫ m
        hRightCancel u (e ≫ w) ?_,
        -- because of the elimination (rfl : w ≫ m = v)
        rfl
      ⟩,
      -- The uniqueness lifts exactly as one would expect.
      -- We can see that hr is exactly the square we need 
      -- (thanks to the equality elimination above).
      fun y ⟨_, (hr : y ≫ m = w ≫ m)⟩ => huniq y hr
    ⟩
    -- Finally, showing u ≫ m = (e ≫ w) ≫ m
    -- is the only thing that remains
    calc
      u ≫ m
        = e ≫ w ≫ m := hComm.symm
      _ = (e ≫ w) ≫ m := (Category.assoc _ _ _).symm

end Ex1_4

section Ex1_5

class Extremal (m : X ⟶ Y) where
  extreme :
    ∀ {V},
    ∀ e : X ⟶ V,
    ∀ v : V ⟶ Y,
    Epi e → e ≫ v = m → IsIso e

instance
    {m : X ⟶ Y}
    [hStrong : Strong m]
    : Extremal m where
  extreme {V} e v eepi eeq :=
    -- We see that using the strong morphism we can construct
    have ⟨
      -- the inverse morphism w
      (w : V ⟶ X),
      -- along with an equation showing it forms an inverse.
      ⟨(hinv : 𝟙 X = e ≫ w), _⟩,
      _
    ⟩ :=
      -- To do this instation we use e and the 𝟙 X morphisms.
      -- We pick e as it is the only morphism we know is Epi,
      -- and we pick 𝟙 X as it forces the equation into the form we need.
      hStrong.strong e (𝟙 X) v
      eepi
      -- The equation we need to provide turns out to come from our assumptions.
      (eeq.trans (Category.id_comp _).symm)
    ⟨
      -- We pick the inverse weve constructed
      w,
      -- and naturally the first equation is exactly what we need
      hinv.symm,
      -- we are not RTP: w ≫ e = 𝟙 V
      -- We note we have the equation (hinv : 𝟙 X = e ≫ w),
      -- using this along with the fact that e is an Epi,
      -- we can do the equational resoning.
      eepi.left_cancellation _ _ <|
        calc
          e ≫ w ≫ e
            = (e ≫ w) ≫ e := (Category.assoc e w e).symm
          _ = 𝟙 X ≫ e     := by rw [hinv]
          _ = e           := Category.id_comp e
          _ = e ≫ 𝟙 V     := (Category.comp_id e).symm
    ⟩

end Ex1_5

end Ex1

section Ex2

variable {n : Nat} {A B : Type u}

-- This question discusses vectors Aⁿ of the form.
#check Fin n → A
-- We can show A* is equivilent to lists
-- Therefore I deam it justifiable to use List A in place of the function definition

-- The expected monoid is defined.
/-- info: instMonoidList_cat -/
#guard_msgs in
#synth Monoid (List A)

-- Sing(leton) is equally defined.
/--
info: protected def List.singleton.{u} : {α : Type u} → α → List α :=
fun {α} a ↦ [a]
-/
#guard_msgs in
#print List.singleton

-- Flat is also defined
/-- info: List.flatten.{u} {α : Type u} : List (List α) → List α -/
#guard_msgs in
#check List.flatten
-- satsifying the desired equation.
/--
info: List.flatten_cons.{u_1} {α✝ : Type u_1} {l : List α✝} {L : List (List α✝)} : (l :: L).flatten = l ++ L.flatten
-/
#guard_msgs in
#check List.flatten_cons

structure σ (n : Nat) where
  f : Fin n → Fin n
  bij : Function.Bijective f

-- We define sigma application as expected
def _root_.List.apply_sig (l : List A) (s : σ l.length) : List A := List.ofFn (l.get ∘ s.f)

-- Working with these is extremely painful as they are not what multisets expect
-- Therefore this following section justifies how these are equivilent to an inductive definition.
-- The point of this is to change the definition to talk about perms,
-- rather than using sigmas directly.
-- The definition of Perm is as follows:

/--
info: inductive List.Perm.{u} : {α : Type u} → List α → List α → Prop
number of parameters: 1
constructors:
List.Perm.nil : ∀ {α : Type u}, [].Perm []
List.Perm.cons : ∀ {α : Type u} (x : α) {l₁ l₂ : List α}, l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)
List.Perm.swap : ∀ {α : Type u} (x y : α) (l : List α), (y :: x :: l).Perm (x :: y :: l)
List.Perm.trans : ∀ {α : Type u} {l₁ l₂ l₃ : List α}, l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃
-/
#guard_msgs in
#print List.Perm

-- Notably this isnt data-carrying.
-- As shown in a proof bellow, whenever you have a perm, you can construct a σ.
-- I would almost ignore this section as it is just gruntwork and pure De Bruijn factor

section sigma_is_permunation

instance : Equiv ((n : Nat) × (Fin n → A)) (List A) where
  toFun  := fun ⟨_, v⟩ => List.ofFn v
  invFun l := ⟨l.length, l.get⟩
  left_inv := by
    rintro ⟨l, f⟩
    ext
    · simp only [List.length_ofFn]
    · simp only
      apply Function.hfunext
      · simp
      · intro a a' heq
        simp only [List.get_eq_getElem, List.getElem_ofFn, heq_eq_eq]
        congr
        simp
  right_inv l := by simp

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

noncomputable def σ.isEquivPerm {n} : σ n ≃ Equiv.Perm (Fin n) :=
  have : σ n ≃ ((f : Fin n → Fin n) ×' Function.Bijective f) := {
    toFun := fun ⟨f,bij⟩ => ⟨f, bij⟩
    invFun := fun ⟨f,bij⟩ => ⟨f, bij⟩
  }
  this.trans sigmaBij_equiv_EquivPerm

theorem _root_.List.apply_sig_Perm {l : List A} {s : σ _} : List.Perm (l.apply_sig s) l := by
  dsimp [List.apply_sig]
  let x := σ.isEquivPerm.toFun s
  have : s.f = x := rfl
  rw [this]
  have eq := Equiv.Perm.ofFn_comp_perm x (List.get l)
  rw [List.ofFn_get] at eq
  exact eq

-- This is in mathlib, I actually pushed it there 
-- The problem is my mathlib is too out of date so i copied it here.
theorem dcongr_heq.{v}
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
theorem _root_.List.Perm_apply_sig : {l₁ l₂ : List A} → l₁.Perm l₂ → ∃ s, l₁.apply_sig s = l₂ := by
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
        simp
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

theorem sigma_is_permunation
    {α : List A → A}
    : (∀ l : List A, ∀ σ : σ l.length, α l = α (l.apply_sig σ))
    ↔ (∀ l₁ l₂, l₁.Perm l₂ → α l₁ = α l₂) where
  mp  h l₁ l₂ hperm := by
    obtain ⟨s, rfl⟩ := List.Perm_apply_sig hperm
    exact h l₁ s
  mpr h l σ :=
    h l (l.apply_sig σ) <| List.Perm.symm List.apply_sig_Perm

end sigma_is_permunation

-- With that out of the way I will continue through the next sections

structure CommStarAlg A where
  α : List A → A

  sing      : α ∘ List.singleton = id
  map_flat  : α ∘ List.map α = α ∘ List.flatten

  -- This is the changed definition because of setoid nonsense
  apply_sig : ∀ l₁ l₂, l₁.Perm l₂ → α l₁ = α l₂

structure CommStarHom (a : CommStarAlg A) (b : CommStarAlg B) where
  h : A → B
  heq : b.α ∘ List.map h = h ∘ a.α

instance {a : CommStarAlg A} {b : CommStarAlg B}
    : CoeFun (CommStarHom a b) (fun _ => A → B) where
  coe := CommStarHom.h

structure CommStarAlgAt (X : Type u) where
  A : Type _
  a : CommStarAlg A
  f : X → A

variable {X : Type _}

instance : CoeFun (CommStarAlgAt X) (fun v => X → v.A) where
  coe := CommStarAlgAt.f

structure CommStarHomAt (a b : CommStarAlgAt X) extends CommStarHom a.a b.a where
  hAtEq : h ∘ a = b

namespace CommStarAlgAt

-- We can now define the category we want

instance : Category (CommStarAlgAt X) where
  Hom := CommStarHomAt
  id X := {
    h := id
    heq := by simp only [List.map_id_fun, CompTriple.comp_eq]
    hAtEq := rfl
  }
  comp {X Y Z} A B := {
    h := B.h ∘ A.h
    heq := calc
      Z.a.α ∘ List.map (B.h ∘ A.h)
        = (Z.a.α ∘ List.map B.h) ∘ List.map A.h := by rw [←List.map_comp_map]; rfl
      _ = B.h ∘ (Y.a.α ∘ List.map A.h)          := by rw [B.heq]; rfl
      _ = (B.h ∘ A.h) ∘ X.a.α                   := by rw [A.heq]; rfl
    hAtEq := calc
      B.h ∘ (A.h ∘ X.f)
        = B.h ∘ Y.f     := by rw [A.hAtEq]
      _ = Z.f           := B.hAtEq
  }
  -- comp_id, id_comp, and assoc are proven for free.
  -- and as they seem to be given in the defn I wont bother redoing it by hand.

-- We define a function
def toMultisetFn (Y : CommStarAlgAt X)
    : Multiset Y.A → Y.A :=
  Quotient.lift Y.a.α Y.a.apply_sig

theorem toMultisetFn_distrib
    {Y : CommStarAlgAt X}
    {a b : Multiset _}
    : Y.toMultisetFn (a + b)
    = Y.a.α [Y.toMultisetFn a, Y.toMultisetFn b] := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i a b
  change Y.a.α (a ++ b) = (Y.a.α ∘ List.map Y.a.α) [a, b]
  rw [Y.a.map_flat]
  simp
theorem distrub_tail
    {Y : CommStarAlgAt X}
    {a b}
    : Y.a.α [a, Y.a.α b] = Y.a.α (a :: b) := by
  change Y.a.α [id a, Y.a.α b] = Y.a.α (a :: b)
  rw [←Y.a.sing]
  change (Y.a.α ∘ List.map Y.a.α) [List.singleton a, b] = Y.a.α (a :: b)
  rw [Y.a.map_flat]
  simp [List.singleton]

-- We note that the object that has the property we look for would be analogous
def init : CommStarAlgAt X where
  A := Multiset X
  a := {
    α := List.sum
    sing := funext fun v => by simp [List.singleton, List.sum]
    map_flat := funext fun v => by simp
    apply_sig l₁ l₂ := List.Perm.sum_eq
  }
  f := fun X => {X}

def isInit X : Limits.IsInitial (CommStarAlgAt.init (X := X)) :=
  .ofUniqueHom
    (fun Y => {
      h (m : Multiset X) :=
        Y.toMultisetFn (Multiset.map Y.f m)
      heq := funext fun (v : List (Multiset _)) => by
        dsimp [init]
        induction v
        · rfl
        case cons hd tl ih =>
          simp
          rw [toMultisetFn_distrib, ←ih]
          exact distrub_tail.symm
      hAtEq := by 
        funext v
        change (Y.a.α ∘ List.singleton) _= _
        rw [Y.a.sing, id]
    })
    fun Y ⟨⟨m, hmEq⟩, mhEqAt⟩ => by
      dsimp [init] at mhEqAt hmEq ⊢
      apply (CommStarHomAt.mk.injEq _ _ _ _).mpr
      apply (CommStarHom.mk.injEq _ _ _ _).mpr
      funext v
      induction v using Quotient.ind
      rename_i v
      change m _ = Y.a.α (List.map Y.f v)
      rw [←mhEqAt, ←List.map_map]
      change _ = (Y.a.α ∘ List.map m) (List.map _ v)
      rw [hmEq]
      congr 1
      clear *-
      induction v
      · rfl
      case cons ih =>
        simp [←ih]

instance {X : Type u} : Limits.HasInitial (CommStarAlgAt.{u, u} X) :=
  Limits.IsInitial.hasInitial (isInit X)

end CommStarAlgAt

end Ex2

end CategoryTheory


