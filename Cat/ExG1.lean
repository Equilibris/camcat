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

universe u v

namespace CategoryTheory

section Ex1

-- We consider some general category 𝓒
variable {𝓒 : Type u} [Category 𝓒]

-- And some objects in 𝓒
variable {X Y Z A B C U V W L : 𝓒}

-- Along with some morphisms
variable {f g : X ⟶ Y}

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

end CategoryTheory

