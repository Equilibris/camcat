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
import Cat.ExGSigma
import Cat.Product

universe u v

namespace CategoryTheory

section Ex2

variable {n : Nat} {A B : Type u}

-- This question discusses vectors Aⁿ of the form.
#check Fin n → A
-- We can show A* is equivilent to lists
-- Therefore I deam it justifiable to use List A in place of the Sigma (Fin · → A) definition.

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

-- In ExGSigma.lean I now go on to prove that Permutations are equivilent σ.
-- This is why in this task I use Permutation instead.
-- The reasoning for this is the signature of Quot.lift for permutations.

#check (Quotient.lift
    : (f : List A → B)
    → (∀ (a b : List A), a.Perm b → f a = f b)
    → Multiset A → B)

-- This means a C*Alg can lift exactly to a function from Multisets to their result.
-- This makes the proof super clean.

-- We need this slighly cute lemma for the end of the proof
theorem Multiset.sum_sing_map
    (v : List A)
    : (List.map (fun X_1 ↦ {X_1}) v).sum = Multiset.ofList v := by
  induction v
  · rfl
  case cons ih => simp [ih]

-- With that out of the way I will continue through the next sections

structure CommStarAlg A where
  α : List A → A

  sing      : α ∘ List.singleton = id
  map_flat  : α ∘ List.map α = α ∘ List.flatten

  -- This is the changed definition because of setoid nonsense
  apply_sig : ∀ l₁ l₂, l₁.Perm l₂ → α l₁ = α l₂

-- I believe there exists a unique isomorphism between CommStarAlg and Abel

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

-- We define a function toMultisetFn,
-- this follows exactly from the defn of the C*Alg(X)
-- This is also where the fact that i picked using List.Perm over σ comes in.
-- All the work done above can be justified by simply writing this function.
def toMultisetFn (Y : CommStarAlgAt X)
    : Multiset Y.A → Y.A :=
  Quotient.lift Y.a.α Y.a.apply_sig

-- The function distributes in interesting ways.
theorem toMultisetFn_distrib
    {Y : CommStarAlgAt X}
    {a b : Multiset _}
    : Y.toMultisetFn (a + b)
    = Y.a.α [Y.toMultisetFn a, Y.toMultisetFn b] := by
  induction a using Quotient.ind; induction b using Quotient.ind; rename_i a b
  symm; calc
    (Y.a.α ∘ List.map Y.a.α) [a, b]
      = (Y.a.α ∘ List.flatten) [a, b] := by rw [Y.a.map_flat]
    _ = Y.a.α (a ++ b)                := by simp

-- This is also a general lemma which will be very useful later on.
theorem distrub_tail
    {Y : CommStarAlgAt X}
    {a b}
    : Y.a.α [a, Y.a.α b] = Y.a.α (a :: b) := calc
    Y.a.α [id a, Y.a.α b]
      = Y.a.α [(Y.a.α ∘ .singleton) a, Y.a.α b] := by rw [←Y.a.sing]
    _ = (Y.a.α ∘ .map Y.a.α) [.singleton a, b]  := rfl
    _ = (Y.a.α ∘ .flatten) [.singleton a, b]    := by rw [Y.a.map_flat]
    _ = Y.a.α (a :: b)                          := by simp [List.singleton]
  -- The last step doesnt really have anything to do with category theory,
  -- so I'll just let `simp` solve it

-- Here we can finally define the initial object
-- It is analgous how we made the free monoid from a list,
-- we make the free abelian monoid from a Multiset.
-- Multisets are lists quotient by the permutation setoid (List.Perm).
-- Multisets are both functors and (abelian) monoids,
-- which are the two structures we will use in this proof.

def init : CommStarAlgAt X where
  A := Multiset X
  a := {
    -- The monoid on Multisets is concatonation lifted from Lists.
    -- We then pick List.sum as our function as it has the property we want
    --   List.sum [a,b,c] = a + b + c = ⟦a ++ b ++ c⟧ .
    -- The square brackets here are refering to the content of the quotient.
    α := List.sum
    sing := funext fun v => by simp [List.singleton, List.sum]
    map_flat := funext fun v => by simp
    -- We get apply_sig for free as multisets are abelian.
    apply_sig l₁ l₂ := List.Perm.sum_eq
  }
  -- f is actually just sing lifted which is cute
  f := fun X => {X}

-- To prove an object is initial it suffices to:
-- Construct a morphism from the ⊥ to any other object,
-- and to show this morphism is unique.
-- The function Limits.IsInitial.ofUniqueHom does exactly this:
-- (NOTE: This isnt definition because initials are given as Limits)

/--
info: CategoryTheory.Limits.IsInitial.ofUniqueHom.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X : C} (h : (Y : C) → X ⟶ Y)
  (uniq : ∀ (Y : C) (m : X ⟶ Y), m = h Y) : Limits.IsInitial X
-/
#guard_msgs in
#check Limits.IsInitial.ofUniqueHom 

def isInit X : Limits.IsInitial (CommStarAlgAt.init (X := X)) :=
  .ofUniqueHom
    (fun Y => {
      -- We construct the morphism using the toMultisetFn function.
      -- This distributes with Y.f nicely as shown above.
      h (m : Multiset X) := Y.toMultisetFn (Multiset.map Y.f m)
      -- We are now RTP : (Y.a.α ∘ List.map fun m ↦ Y.toMultisetFn (Multiset.map Y.f m))
      --      = (fun m ↦ Y.toMultisetFn (Multiset.map Y.f m)) ∘ init.a.α
      -- This follows from the distrubution lemmas given above.
      heq := funext fun (v : List (Multiset _)) => by
        dsimp [init]
        induction v
        · rfl
        case cons hd tl ih =>
          simp only [List.map_cons, List.sum_cons, Multiset.map_add]
          rw [toMultisetFn_distrib, ←ih]
          exact distrub_tail.symm
      -- Next we are RTP: (fun m ↦ Y.toMultisetFn (Multiset.map Y.f m)) ∘ init.f = Y.f
      hAtEq := funext fun v => by
        -- To show it is unique we can use sing thanks to nice defeqs from lean.
        change (Y.a.α ∘ List.singleton) _= _
        rw [Y.a.sing, id]
    })
    fun Y ⟨
        ⟨
          m,
          (hmEq : Y.a.α ∘ List.map m = m ∘ init.a.α)
        ⟩,
        (mSigEqf : (m ∘ fun X => ({X} : Multiset _)) = Y.f)
      ⟩ => by
      dsimp [init] at mSigEqf hmEq ⊢
      refine (CommStarHomAt.mk.injEq _ _ _ _).mpr 
        <| (CommStarHom.mk.injEq _ _ _ _).mpr 
        <| funext fun v => Eq.symm ?_
      -- Shwoing that the function is unique is quite nice to do actually
      -- We are RTP: m v = Y.toMultisetFn (Multiset.map Y.f v)
      induction v using Quotient.ind
      rename_i v
      calc
        Y.a.α (List.map Y.f v)
          = Y.a.α (List.map Y.f v)                         := rfl
        _ = Y.a.α (List.map (m ∘ _) v)                     := by rw [mSigEqf]
        _ = Y.a.α (List.map m (List.map _ v))              := by rw [List.map_map]
        _ = (Y.a.α ∘ List.map m) (List.map _ v)            := rfl
        _ = (m ∘ _) (List.map _ v)                         := by rw [hmEq]
        _ = m (v.map (fun X_1 ↦ ({X_1} : Multiset _))).sum := by rfl
        _ = m (Multiset.ofList v)                          := by rw [Multiset.sum_sing_map v]
        _ = m ⟦v⟧                                          := rfl

-- Sanity check the proof doesnt depend on sorryAx.
/--
info: 'CategoryTheory.CommStarAlgAt.isInit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isInit

instance {X : Type u} : Limits.HasInitial (CommStarAlgAt.{u, u} X) :=
  Limits.IsInitial.hasInitial (isInit X)

end CommStarAlgAt

end Ex2

end CategoryTheory
