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
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.FinEnum
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.ExG2

universe u v

namespace CategoryTheory

variable {A B C : Type _}

/-
  This file is not remotely as clean as Ex1 or Ex2.
  This is mainly seen in the large usage of `simp`.
  `simp` is an automatic simplification tactic that tries to normalise.
  Since I have resorted to developing my own theory (fin_preimage) to construct comp,
  I need to use a lot of simp lemmas from mathlib.
-/

section lemmas

-- This section mainly concerns a collection of lemmas that are needed for the later proofs.
-- They could (and will be after this assessment) be parts of mathlib.
-- All this is basically just noise.

theorem fin_cast_linv {n m} (p : n = m) : Function.LeftInverse (Fin.cast p.symm) (Fin.cast p) :=
  fun _ => rfl
theorem fin_cast_rinv {n m} (p : n = m) : Function.RightInverse (Fin.cast p.symm) (Fin.cast p) :=
  fun _ => rfl

theorem fin_cast_id {n m} (p : n = m) : Fin.cast p ∘ Fin.cast p.symm = id := rfl

theorem bij_f_cast {n m} {p : n = m} : Function.Bijective (Fin.cast p) := by
  constructor
  · exact Fin.cast_injective p
  · intro a
    use (Fin.cast p.symm a)
    rw [Fin.cast_trans, Fin.cast_eq_self]

@[simp]
theorem filterMap_add
    {a b : Multiset A}
    {f : A → Option B}
    : ((a + b).filterMap f) = (a.filterMap f + b.filterMap f) := by 
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  simp
@[simp]
theorem filterMap_none
    {ms : Multiset A}
    : Multiset.filterMap (fun _ ↦ none) ms = ({} : Multiset B) := by
  induction ms using Quot.ind; rename_i ms
  simp

@[simp]
theorem map_singleton_flatten : {a : List A} → (List.map List.singleton a).flatten = a
  | [] => rfl
  | hd :: tl => by
    change hd :: (List.map List.singleton tl).flatten = hd :: tl
    rw [map_singleton_flatten]

@[simp]
theorem map_singleton_sum {a : Multiset A} : (a.map ({·})).sum = a := by
  induction a using Quot.ind; rename_i a
  simp
  induction a
  · rfl
  · simp_all

@[simp]
theorem multiset_map_some {f : A → B} {ms : Multiset (Multiset A)} :
    Multiset.map f ms.sum = (ms.map (Multiset.map f)).sum := by
  induction ms using Quot.ind;rename_i ms
  simp only [Multiset.quot_mk_to_coe'', Multiset.sum_coe, Multiset.map_coe]
  induction ms
  · rfl
  case cons hd tl ih => simpa

@[simp]
theorem multiset_map_all {a : List A}
    : (Multiset.map a.get Fintype.elems.val)
    = Multiset.ofList a := by
  induction a
  · rfl
  case cons hd tl ih =>
    have : (Fintype.elems.val : Multiset (Fin (hd :: tl).length)) = 
      ⟨0, by simp⟩ ::ₘ (Fintype.elems.val.map Fin.succ) := by
      refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
      · exact Fintype.elems.nodup
      · simp only [List.length_cons, Fin.zero_eta, Multiset.nodup_cons, Multiset.mem_map,
          Finset.mem_val, Fin.succ_ne_zero, and_false, exists_false, not_false_eq_true, true_and]
        exact
          (Multiset.nodup_map_iff_of_injective <| Fin.succ_injective _).mpr
            Fintype.elems.nodup
      rintro (_|_)
      <;> simp [Fintype.complete]
    rw [this]
    simp only [Fin.zero_eta, List.length_cons, Multiset.map_cons, Multiset.map_map,
      Function.comp_apply]
    change hd ::ₘ Multiset.map tl.get _ = _
    rw [ih]
    simp

@[simp]
theorem multiset_map_all' {a : List A}
    : (Multiset.map (fun x ↦ a[↑x]) (Fintype.elems.val : Multiset <| Fin a.length))
    = Multiset.ofList a :=
  multiset_map_all

@[simp]
theorem Perm_ofList_toList {a : List A} : a.Perm (Multiset.ofList a).toList :=
  Multiset.coe_eq_coe.mp <| (Multiset.coe_toList _).symm

instance fintype_card_eq : Finite (A → Bool) → Finite A := by
  contrapose
  simp only [not_finite_iff_infinite]
  exact fun a ↦ Function.infinite_of_left

theorem multiset_finite : Finite (Multiset A) → IsEmpty A := by
  contrapose
  simp only [not_isEmpty_iff, not_finite_iff_infinite, Nonempty.forall]
  intro a
  apply Infinite.of_injective (β := Nat) (Multiset.replicate · a)
  intro a b h
  simp only [Multiset.eq_replicate, Multiset.card_replicate] at h
  exact h.1

theorem mem_sum {a}
    {ls : List (Multiset B)}
    (h : a ∈ ls.sum) : ∃ idx : Fin _, a ∈ ls[idx] := by
  induction ls
  · simp at h
  case cons hd tl ih =>
    simp only [List.sum_cons, Multiset.mem_add] at h
    rcases h with (h|h)
    · exact ⟨⟨0, by simp⟩, h⟩
    · specialize ih h
      rcases ih with ⟨idx, p⟩
      refine ⟨⟨idx + 1, by simp⟩, p⟩

theorem nodup_disj
    [Fintype A]
    {s : A → Multiset B}
    (hNd : ∀ x, (s x).Nodup)
    (h : ∀ a b, a ≠ b → Disjoint (s a) (s b)) : (∑ x, s x).Nodup := by
  change (Multiset.map s Finset.univ.val).sum.Nodup
  rcases Finset.univ with ⟨elems, nd⟩
  induction elems using Quot.ind; rename_i elems
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_nodup, Multiset.map_coe,
    Multiset.sum_coe] at nd ⊢
  induction elems
  · simp
  case cons hd tl ih =>
    simp at nd ⊢
    specialize ih nd.2
    apply (Multiset.Nodup.add_iff _ ih).mpr
    · apply Multiset.disjoint_left.mpr
      intro a mema memb
      have ⟨idx, memb⟩ := mem_sum memb
      simp only [Fin.getElem_fin, List.getElem_map] at memb
      specialize h hd tl[idx] (by grind)
      exact Multiset.disjoint_left.mp h mema memb
    · exact hNd hd

end lemmas

section Ex3

-- I decided to use a definition closer to the one in the question after trying many alternatives.
-- There were neumerous problems with proving assoc of composition,
-- but this defn seemed to have the least problems.
structure Ent (A B : Type u) where
  r : List A → B → Prop
  -- We use the same change as we did in Ex2.
  -- Later we do actually benefit from being able to extract a σ though.
  perm : ∀ l₁ b, r l₁ b → ∀ l₂, l₁.Perm l₂ → r l₂ b

namespace Ent

def MsRel (x : Ent A B) (ms : Multiset A) (bv : B) : Prop :=
  x.r ms.toList bv

def ofMsRel (R : Multiset A → B → Prop) : Ent A B where
  r ls b := R ls b
  perm l₁ b R l₂ lperm := by
    have : Multiset.ofList l₂ = Multiset.ofList l₁ := Multiset.coe_eq_coe.mpr lperm.symm
    rw [this]
    exact R

theorem msRel_iff_r_toList {l b} {E : Ent A B} : E.r l.toList b = E.MsRel l b := by rfl
theorem msRel_coe_iff_r {l b} {E : Ent A B} : E.r l b = E.MsRel l b := by
  refine propext ⟨?_, ?_⟩ <;> refine fun h => E.perm _ _ h _ ?_
  · exact Perm_ofList_toList
  · exact Perm_ofList_toList.symm

@[ext]
def ext {E F : Ent A B} (h : ∀ a b, E.r a b ↔ F.r a b) : E = F :=
  match E, F with
  | ⟨_, _⟩, ⟨_, _⟩ =>
    (mk.injEq _ _ _ _).mpr
    <| funext fun a => funext fun b => propext (h a b)

-- The definition we use is equivilent to this alternative definition.
-- This is much cleaner to work with and will be used more later on.
def equivMsRel : (Ent A B) ≃ (Multiset A → B → Prop) where
  toFun e := MsRel e
  invFun := ofMsRel
  left_inv e := by
    ext a b
    constructor
    <;> rintro h
    <;> apply e.perm _ _ h
    <;> apply Multiset.coe_eq_coe.mp
    <;> simp
  right_inv v := funext fun a => funext fun b => by
    simp [ofMsRel, MsRel]

-- Relational lifting is exacly as given
abbrev LiftR (R : A → B → Prop) : Ent A B where
  r a b := ∃ w, a = [w] ∧ R w b
  perm l b := by
    rintro ⟨w, rfl, rwb⟩
    simpa

abbrev Ax A : Ent A A := LiftR (· = ·)

-- Composition will use tree structures pairing the values up through the composition.
-- I do this through using the multiset preimages of functions.
-- Lean did not have these built in so I develop the basic theory needed for them here.

def fin_preimage {A B} [fta : Fintype A] [DecidableEq B]
    (f : A → B) (b : B)
    : Multiset A :=
  fta.elems.val.filter (f · = b)

namespace fin_preimage

variable {A B C : Type _} [fta : Fintype A]

-- They compose in interesting ways over bijections.

@[simp]
theorem comp_bij {b} {f : A → B} {g : B → C} [DecidableEq B] [DecidableEq C] [Fintype B]
    {gInv : C → B}
    (hl : Function.LeftInverse gInv g)
    (hr : Function.RightInverse gInv g)
    : fin_preimage (g ∘ f) b = fin_preimage f (gInv b) := by
  simp [fin_preimage]
  induction fta.elems.val using Quot.ind; rename_i l
  simp only [Multiset.quot_mk_to_coe'', Multiset.filter_coe, Multiset.coe_eq_coe]
  apply List.Perm.of_eq
  induction l
  · rfl
  case cons hd tl ih =>
    simp [List.filter_cons, ←ih]
    split
    <;> split
    <;> simp_all
    <;> rename_i h₁ h₂
    · apply h₂
      rw [←h₁]
      exact (hl _).symm
    · refine h₁ <| hr _

@[simp]
theorem comp_bij'
    {b fInv} (f : A → B) (g : B → C) [DecidableEq C] [ftb : Fintype B]
    (hl : Function.LeftInverse fInv f)
    (hr : Function.RightInverse fInv f)
    : fin_preimage (g ∘ f) b = (fin_preimage g b).map fInv := by
  dsimp [fin_preimage]
  have : ∀ (p : A → Prop), DecidablePred p :=
    fun p _ => Classical.propDecidable _
  rw [Multiset.map_filter' _ (Function.LeftInverse.injective hr)]
  have : (Multiset.map fInv ftb.elems.val) = fta.elems.val := by
    refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
    · refine (Multiset.nodup_map_iff_of_injective <| Function.LeftInverse.injective hr).mpr
        <| Fintype.elems.nodup
    · exact Fintype.elems.nodup
    intro a
    simp only [Multiset.mem_map, Finset.mem_val, Fintype.complete, true_and, iff_true]
    use f a
    exact hl a
  rw [this]
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  any_goals exact Multiset.Nodup.filter _ <| Fintype.elems.nodup
  intro a
  simp only [Multiset.mem_filter, Finset.mem_val, Fintype.complete, true_and]
  constructor
  · rintro rfl
    use f a
    exact ⟨rfl, hl a⟩
  · rintro ⟨_, rfl, rfl⟩
    rw [hr]

@[simp]
theorem fin_preimage_id {v : A} [DecidableEq A] : (fin_preimage id v) = {v} := by
  simp [fin_preimage, Multiset.filter_eq', Multiset.count_eq_of_nodup fta.elems.nodup, fta.complete]

@[simp]
theorem bij
    {b fInv} (f : A → B) [DecidableEq B] [Fintype B]
    (hl : Function.LeftInverse fInv f)
    (hr : Function.RightInverse fInv f)
    : fin_preimage f b = {fInv b} := calc
  fin_preimage f b
    = fin_preimage (id ∘ f) b       := rfl
  _ = (fin_preimage id b).map fInv  := comp_bij' _ _ hl hr
  _ = Multiset.map fInv {b}         := by rw [fin_preimage_id]
  _ = {fInv b}                      := rfl


@[simp]
theorem unit_inv (f : A → Fin 1) : (fin_preimage f 0) = fta.elems.val := by
  simp only [fin_preimage, Fin.isValue, Multiset.filter_eq_self, Finset.mem_val, fta.complete,
    forall_const]
  intro a; cases f a; omega

theorem eq_unit {f : A → B} [DecidableEq B] {v a}
    (h : fin_preimage f v = {a}) : f a = v := by
  simp [fin_preimage] at h
  rcases fta with ⟨⟨ms, nd⟩, comp⟩
  change Multiset.filter (fun x ↦ f x = v) ms = {a} at h
  induction ms using Quot.ind; rename_i ms
  simp [List.filter_eq_cons_iff] at h nd comp
  rcases h with ⟨_, _, _, _, rfl, _⟩
  rfl

theorem exists_sig_iff_unique_valued {f : A → B} [DecidableEq B] {v}
    : (∃ a, fin_preimage f v = {a}) ↔ ∃! a, f a = v := by
  have : DecidableEq A := Classical.typeDecidableEq A
  constructor
  · rintro ⟨w, h⟩
    have := eq_unit h
    refine ⟨w, this, fun y => ?_⟩
    rintro rfl
    dsimp [fin_preimage] at h
    rcases fta with ⟨⟨ms, nd⟩, comp⟩
    change Multiset.filter (fun x ↦ f x = _) ms = {w} at h
    induction ms using Quot.ind; rename_i ms
    simp only [Multiset.quot_mk_to_coe'', Multiset.coe_nodup, Finset.mem_mk, Multiset.mem_coe,
      Multiset.filter_coe, Multiset.coe_eq_singleton, List.filter_eq_cons_iff, decide_eq_true_eq,
      this, decide_true, List.filter_eq_nil_iff, true_and] at ms nd comp h
    rcases h with ⟨l₁, l₂, rfl, hl, hr⟩
    obtain (h|rfl|h) : y ∈ l₁ ∨ y = w ∨ y ∈ l₂ := by have := comp y; simp_all
    · exact (hl _ h rfl).elim
    · rfl
    · exact (hr _ h rfl).elim
  · rintro ⟨a, rfl, uniq⟩
    use a
    rcases fta with ⟨⟨ms, nd⟩, comp⟩
    dsimp [fin_preimage]
    induction ms using Quot.ind; rename_i ms
    simp only [Multiset.quot_mk_to_coe'', Finset.mem_mk, Multiset.mem_coe, Multiset.coe_nodup,
      Multiset.filter_coe, Multiset.coe_eq_singleton, List.filter_eq_cons_iff, decide_eq_true_eq,
      decide_true, List.filter_eq_nil_iff, true_and] at comp nd uniq ⊢
    let idx := ms.idxOf a
    use (ms.take idx), (ms.drop idx.succ)
    rw [
      show a = ms.get (Fin.mk (ms.idxOf a) (List.idxOf_lt_length_of_mem (comp a))) from by simp,
      List.cons_get_drop_succ,
      List.take_append_drop,
      List.get_eq_getElem, List.getElem_idxOf]
    refine ⟨rfl, ?tk, ?dp⟩
    <;> intro v h heq
    <;> obtain rfl := uniq _ heq
    <;> dsimp [idx] at h
    <;> clear *-h nd
    <;> induction ms
    any_goals simp only [List.not_mem_nil, not_false_eq_true, List.idxOf_of_notMem, List.length_nil,
      List.take_nil, zero_add, List.drop_nil, List.drop_succ_cons] at h
    all_goals rename_i hd tl ih
    all_goals by_cases h' : hd = v
    any_goals subst h'
    all_goals simp_all

-- Notably you can also conclude they are a bijection iff they have unique preimages.

theorem exists_sig_iff_bijective {f : A → B} [DecidableEq B]
    : (∀ v, ∃ a, fin_preimage f v = {a}) ↔ Function.Bijective f := by
  conv => lhs; intro v; rw [exists_sig_iff_unique_valued]
  exact (Function.bijective_iff_existsUnique f).symm

theorem sum_all
    {f : A → B} [DecidableEq B] [Fintype B]
    : (∑ x, fin_preimage f x) = fta.elems.val := by
  dsimp [fin_preimage]
  have : DecidableEq A := Classical.typeDecidableEq A
  refine Multiset.ext'_iff.mpr fun a => ?_
  simp only [Multiset.count_eq_of_nodup fta.elems.nodup, Finset.mem_val, fta.complete, ↓reduceIte]
  refine Multiset.count_eq_one_of_mem ?_ ?comp
  case comp => simp [fta.complete]
  apply nodup_disj
  · exact fun a => Multiset.Nodup.filter _ Fintype.elems.nodup
  intro a b h
  apply Multiset.disjoint_left.mpr
  intro v hma hmb
  simp [Fintype.complete] at hma hmb
  exact h <| hma.symm.trans hmb

end fin_preimage

-- Composition was an absolute pain.
-- I went through 4 equivilent definitions before I ended up on this one,
-- this might even have been a mistake because all of the definitions were nice in their own ways.
-- The one I ended up sticking with is the one given below.
-- This uses fin_preimages to map up between the lists.
-- The question also contains:
-- > Remember to argue that if E ⊆ A* × B is an entailment from A to B and
-- > F ⊆ B* × C is an entailment from 𝐵 to 𝐶 then their composition
-- > F ⊛ E ⊆ A* × C is an entailment from A to C.
-- This follows for free by the type signature.

def comp (E : Ent A B) (F : Ent B C) : Ent A C where
  r := fun ls c =>
    ∃ lpart : List B, ∃ f : Fin ls.length → Fin lpart.length,
      F.r lpart c
      ∧ ∀ v : Fin lpart.length,
        E.MsRel (fin_preimage f v |>.map (ls[·])) lpart[v]
  perm := by
    rintro l₁ b ⟨lpart, fMap, fHolds, mapping⟩ l₂ perm 
    obtain ⟨⟨s, v⟩, rfl⟩ := List.Perm_apply_sig perm
    have p := (@List.apply_sig_length A l₁ ⟨s, v⟩)
    refine ⟨lpart, (fMap ∘ s) ∘ (Fin.cast p), fHolds, ?_⟩
    have ⟨invC, hlC, hrC⟩ :=
      Function.bijective_iff_has_inverse.mp <| (bij_f_cast (p := p))
    obtain rfl : invC = Fin.cast p.symm := by 
      clear *-hlC hrC
      funext v
      rw [←hrC v, hlC, Fin.cast_trans, Fin.cast_eq_self]
    have ⟨invS, hlS, hrS⟩ := Function.bijective_iff_has_inverse.mp v
    intro v'
    rw [fin_preimage.comp_bij' _ _ hlC hrC, fin_preimage.comp_bij' _ _ hlS hrS]
    simp only [List.apply_sig, Multiset.map_map, Function.comp_apply, Fin.getElem_fin,
      List.getElem_ofFn, Fin.coe_cast, Fin.eta]
    conv => lhs; lhs; intro x; rw [hrS x]
    exact mapping v'

-- Another much cleaner definition is the one below.
structure CompObj (E : Multiset A → B → Prop) where
  la : Multiset A
  b : B
  r : E la b

def comp'
    (E : Multiset A → B → Prop)
    (F : Multiset B → C → Prop)
    (ls : Multiset A)
    (c : C) : Prop :=
  ∃ lpart : Multiset (CompObj E),
    F (lpart.map CompObj.b) c
    ∧ ls = (lpart.map CompObj.la).sum

def multiset_map_sum {n : Nat}
    (sel : Fin n → Multiset A)
    (f : A → B)
    : (∑ x, Multiset.map f (sel x)) = Multiset.map f (∑ x, sel x) := by
  unfold Finset.sum
  generalize (Finset.univ.val : Multiset (Fin n)) = z
  simp

def ms_eq_lift {a b : Multiset A} (eq : a = b) : a.toList.Perm b.toList := 
  eq ▸ List.Perm.refl a.toList

def ms_toList_add {a b : Multiset A} : (a + b).toList.Perm (a.toList ++ b.toList) := by
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_add]
  refine Perm_ofList_toList.symm.trans <| List.Perm.append ?_ ?_
  <;> exact Perm_ofList_toList

def ms_sum_toList_Perm
    : (ls : List (Multiset A)) → ls.sum.toList.Perm (ls.map Multiset.toList).flatten
  | [] => by simp
  | hd :: tl => by
    simp only [List.sum_cons, List.map_cons, List.flatten_cons]
    apply ms_toList_add.trans
    refine List.Perm.append (ms_eq_lift rfl) ?_
    exact ms_sum_toList_Perm _

noncomputable def compObj_mapper {E : Multiset A → B → Prop}
    : (lpart : List (CompObj E))
    → Fin (List.map (Multiset.toList ∘ CompObj.la) lpart).flatten.length
    → Fin (List.map CompObj.b lpart).length
  | [] , v => v.elim0
  | hd :: tl, v =>
    if h : v < hd.la.card then
      ⟨0, by simp⟩
    else
      Fin.succ
        <| compObj_mapper tl
        <| v.cast (by simp [Nat.add_comm])
        |>.subNat hd.la.card (by rw [Fin.coe_cast]; exact Nat.le_of_not_lt h)

theorem filter_fin_to_map {n m : Nat} (h : n ≤ m)
    : (Multiset.filter (fun x : Fin m ↦ ↑x < n) Fintype.elems.val)
    = (Multiset.map (Fin.castLE h) Fintype.elems.val) := by
  apply Multiset.ext'_iff.mpr
  intro a
  rw [
    Multiset.count_eq_of_nodup (Multiset.Nodup.filter _ Fintype.elems.nodup),
    Multiset.count_eq_of_nodup (Multiset.Nodup.map (Fin.castLE_injective h) Fintype.elems.nodup)
  ]
  simp [Fintype.complete]
  split <;> rename_i h
  <;> simp only [left_eq_ite_iff, not_exists, one_ne_zero, imp_false, not_forall,
      Decidable.not_not, right_eq_ite_iff, zero_ne_one, imp_false, not_exists]
  · use ⟨_, h⟩
    simp
  · rintro _ rfl
    simp at h

theorem map_fin_cast {n m : Nat} (h : n = m)
    : (Multiset.map (Fin.cast h) Fintype.elems.val)
    = Fintype.elems.val := by subst h; simp

theorem dite_eq_pull_left
    {c a} {f t : _ → A} [Decidable c]
    : ((if h : c then t h else f h) = a) = if v : c then t v = a else f v = a := by
  grind

theorem dite_eq_pull_right
    {c a} {f t : _ → A} [Decidable c]
    : (a = (if h : c then t h else f h)) = if v : c then a = t v else a = f v := by
  grind

theorem dite_and_dite
    {c} {f₁ f₂ t₁ t₂ : _ → Prop} [Decidable c]
    : ((if h : c then t₁ h else f₁ h) ∧ if h : c then t₂ h else f₂ h)
    = if v : c then t₁ v ∧ t₂ v else f₁ v ∧ f₂ v := by
  grind

theorem fintype_split
    {n m : Nat}
    : (Fintype.elems.val : Multiset (Fin (n + m)))
    = Multiset.map (Fin.castAdd m) (Fintype.elems.val : Multiset (Fin n))
    + Multiset.map (Fin.cast (Nat.add_comm _ _)) (Multiset.map (Fin.addNat · n) Fintype.elems.val)
    := by
  refine Multiset.ext.mpr fun a => ?_
  rw [Multiset.count_eq_of_nodup Fintype.elems.nodup]
  simp only [Finset.mem_val, Fintype.complete, ↓reduceIte, Multiset.map_map, Function.comp_apply,
    Fin.cast_addNat, Multiset.count_add]
  rw [
    Multiset.count_eq_of_nodup
      <| Multiset.Nodup.map (Fin.castAdd_injective n m) (Fintype.elems.nodup),
    Multiset.count_eq_of_nodup 
      <| Multiset.Nodup.map (Fin.natAdd_injective m n) (Fintype.elems.nodup)
  ]
  simp only [Multiset.mem_map, Finset.mem_val, Fintype.complete, true_and]
  split <;> rename_i h
  · rcases h with ⟨w, rfl⟩
    simp only [Nat.left_eq_add, ite_eq_right_iff, one_ne_zero, imp_false, not_exists]
    intro ⟨a, alt⟩ h
    rcases w with ⟨w, wlt⟩
    simp only [Fin.natAdd_mk, Fin.castAdd_mk, Fin.mk.injEq] at h
    omega
  · split
    · rfl
    · rename_i h'
      rcases a with ⟨a, alt⟩
      rw [not_exists] at h' h
      have nh : ∀ x, (h : x < n) → ¬x = a := fun x h' v => h ⟨x, h'⟩ (v ▸ rfl)
      have nh' : ∀ x, (h : x < m) → ¬n + x = a := fun x h v => h' ⟨x, h⟩ (v ▸ rfl)
      clear h h'
      exfalso
      rcases lt_or_ge a n with (h|h)
      · exact nh _ h rfl
      · obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le h
        apply nh' _ _ rfl
        omega

theorem compObj_mapper.fin_preimage_eq
    {E : Multiset A → B → Prop}
    : (lpart : List (CompObj E))
    → (v : Fin (List.map CompObj.b lpart).length)
    → Multiset.map
        (List.map (Multiset.toList ∘ CompObj.la) lpart).flatten.get
          (fin_preimage (compObj_mapper lpart) v) =
      lpart[v].la
  | [], v => v.elim0
  | hd :: tl, ⟨0, _⟩ => by
    have : DecidableEq A := Classical.typeDecidableEq A
    simp only [fin_preimage, List.map_cons, List.length_cons, compObj_mapper, Function.comp_apply,
      List.flatten_cons, Fin.zero_eta, dite_eq_left_iff, not_lt, Fin.succ_ne_zero, imp_false,
      not_le, List.get_eq_getElem, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, List.length_map,
      Nat.zero_mod, List.getElem_cons_zero]
    rw [filter_fin_to_map (by simp)]
    simp only [Multiset.map_map, Function.comp_apply, Fin.coe_castLE, Multiset.length_toList,
      Fin.is_lt, List.getElem_append_left]
    change Multiset.map (hd.la.toList.get ∘ Fin.cast (by simp)) _ = _
    rw [←Multiset.map_map, map_fin_cast, multiset_map_all]
    exact Multiset.coe_toList hd.la
  | hd :: tl, ⟨n+1, h⟩ => by
    have : DecidableEq A := Classical.typeDecidableEq A
    symm
    apply (compObj_mapper.fin_preimage_eq tl ⟨n, (by simp_all)⟩).symm.trans
    apply Multiset.ext.mpr
    intro a
    simp only [fin_preimage, List.get_eq_getElem, Multiset.count_map, Multiset.filter_filter,
      List.map_cons, List.length_cons, Function.comp_apply, List.flatten_cons]
    conv =>
      rhs; rhs; lhs; intro v
      · rw [List.getElem_append]
        simp only [Multiset.length_toList, compObj_mapper, List.map_cons, Function.comp_apply,
          List.flatten_cons, List.length_cons, Fin.zero_eta]
        rw [dite_eq_pull_left, dite_eq_pull_right, dite_and_dite]
        simp only [Fin.zero_eq_mk, Nat.add_eq_zero, one_ne_zero, and_false, Fin.succ, Fin.mk.injEq,
          Nat.add_right_cancel_iff, dite_then_false, not_lt]
    conv =>
      rhs; rhs;
      rw [
        ←Multiset.map_id Fintype.elems.val,
        ←fin_cast_id List.length_append.symm,
        ←Multiset.map_map,
        map_fin_cast,
        fintype_split
      ]
    simp only [Multiset.map_map, Function.comp_apply, Fin.cast_addNat, Multiset.map_add,
      Multiset.filter_add, Multiset.card_add]
    conv =>
      rhs;lhs
      rw [Multiset.filter_map]
      simp only [Function.comp_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.cast_trans,
        Multiset.card_map]
      arg 1; lhs; intro x;
      rw! [show (hd.la.card ≤ x.val) = False from (by 
        simp only [eq_iff_iff, iff_false, not_le]
        rw [←Multiset.length_toList]
        exact x.isLt
      )]
      simp only [IsEmpty.exists_iff]
    simp only [Multiset.filter_false, Multiset.card_zero, Multiset.filter_map, Function.comp_apply,
      Fin.coe_cast, Fin.coe_natAdd, Multiset.length_toList, add_tsub_cancel_left, Fin.cast_trans,
      le_add_iff_nonneg_right, zero_le, exists_true_left, Multiset.card_map, zero_add]
    conv =>
      rhs; arg 1; lhs
      · intro x; rhs;
        rw [Fin.val_inj (b := ⟨n, Nat.succ_lt_succ_iff.mp h⟩)]
        lhs; rhs
        unfold Fin.subNat Fin.cast Fin.addNat
        simp

theorem comp_iff_comp'
    (E : Ent A B) (F : Ent B C)
    : comp E F = equivMsRel.invFun (comp' (equivMsRel.toFun E) (equivMsRel.toFun F)) := by
  ext a b
  dsimp only [equivMsRel, ofMsRel, comp, comp']
  have : DecidableEq A := Classical.typeDecidableEq A
  constructor
  · rintro ⟨lpart, fmap, hl, hr⟩
    use Multiset.ofList (List.ofFn (fun v => {
      la := Multiset.map (a[·]) (fin_preimage fmap v)
      b := lpart[v]
      r := hr v
      : CompObj _ }))
    constructor
    · simp only [Fin.getElem_fin, Multiset.map_coe, List.map_ofFn]
      unfold Function.comp
      simp only [MsRel, List.ofFn_getElem]
      exact F.perm _ _ hl _ Perm_ofList_toList
    · apply Multiset.ext.mpr
      simp only [Multiset.coe_count, Fin.getElem_fin, Multiset.map_coe, List.map_ofFn,
        Multiset.sum_coe, List.sum_ofFn, Function.comp_apply, Multiset.count_sum']
      intro v
      conv =>
        rhs; rhs; intro x
        rw [Multiset.count_map]
        change (Multiset.filter (Eq v ∘ a.get) _).card
        rw [←Multiset.card_map a.get, ←Multiset.filter_map]
        rw [Multiset.filter_eq, Multiset.card_replicate]
      rw [←Multiset.count_sum', multiset_map_sum, fin_preimage.sum_all, multiset_map_all]
      exact (Multiset.coe_count v a).symm
  · rintro ⟨lpart, hl, hr⟩
    induction lpart using Quot.ind; rename_i lpart
    simp [MsRel] at hl hr
    /- have := (List.Perm.symm Perm_ofList_toList) -/
    have : a.Perm (List.map (Multiset.toList ∘ CompObj.la) lpart).flatten := by 
      rw [←List.map_map]
      symm
      apply (ms_sum_toList_Perm _).symm.trans
      symm
      apply Perm_ofList_toList.trans
      rw [hr]
    clear hr
    obtain ⟨⟨s, bijS⟩, rfl⟩ := List.Perm_apply_sig this.symm
    have ⟨si, sil, sir⟩ := Function.bijective_iff_has_inverse.mp bijS
    refine ⟨
      _, 
      (compObj_mapper _ ∘ s) ∘ Fin.cast List.apply_sig_length, --compObj_mapper _ ∘ Fin.cast hACast,
      F.perm _ _ hl _ (List.Perm.symm Perm_ofList_toList),
      ?_
    ⟩
    intro v
    rw [fin_preimage.comp_bij' (Fin.cast _) _ (fin_cast_linv _) (fin_cast_rinv _)]
    rw [fin_preimage.comp_bij' _ _ sil sir]
    simp [List.apply_sig]
    conv => lhs; lhs; intro v; arg 2; rw [sir v]
    change E.MsRel (Multiset.map (List.get _) _) _
    rw [compObj_mapper.fin_preimage_eq]
    exact lpart[v].r

-- Type \circledast
infixr:100 " ⊛ " => comp

theorem comp_respects_comp
    (R : A → B → Prop)
    (S : B → C → Prop)
    : LiftR (Relation.Comp R S) = LiftR R ⊛ LiftR S := by
  ext a b
  simp only [Relation.Comp, comp, LiftR, Fin.getElem_fin, exists_and_left]
  constructor
  · rintro ⟨w, rfl, w', r, s⟩
    refine ⟨[w'], ⟨_, rfl, s⟩, id, fun | ⟨0, _⟩ => ⟨w, ?_, r⟩⟩
    simp
  · rintro ⟨_, ⟨w, rfl, swb⟩, ⟨f, h⟩⟩
    specialize h ⟨0, Nat.zero_lt_succ [].length⟩
    simp only [MsRel, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      fin_preimage.unit_inv, Multiset.toList_eq_singleton_iff, Multiset.map_eq_singleton,
      Finset.val_eq_singleton_iff, List.getElem_cons_zero, exists_exists_and_eq_and] at h
    rcases h with ⟨w', heq, hr⟩
    obtain ⟨wa, rfl⟩ := 
      have : a.length = 1 := by
        have := Fintype.complete (α := Fin a.length)
        rw [heq] at this
        simp only [Finset.mem_singleton] at this
        clear *-this
        rcases a with (_|⟨hd, (_|⟨hd2,tl⟩)⟩)
        · exact w'.elim0
        · rfl
        · have := (this ⟨0, by simp⟩).trans (this ⟨1, by simp⟩).symm
          simp at this
      List.length_eq_one_iff.mp this
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero,
      List.getElem_cons_zero] at hr
    refine ⟨wa, rfl, _, hr, swb⟩

theorem comp_Ax (E : Ent A B) : E ⊛ Ax B = E := by
  ext a b
  constructor
  · rintro ⟨lperm, f, ⟨w,rfl,rfl⟩, hr⟩
    specialize hr ⟨0, by simp⟩
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      fin_preimage.unit_inv, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero] at hr
    change E.MsRel (Multiset.map a.get Fintype.elems.val) w at hr
    rw [multiset_map_all] at hr
    exact E.msRel_coe_iff_r.mpr hr
  · intro h
    refine ⟨[b], fun _ => ⟨0, by simp⟩, ⟨_, rfl, rfl⟩, fun ⟨0, _⟩ => ?_⟩
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      fin_preimage.unit_inv, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero]
    change E.MsRel (Multiset.map a.get _) _
    rw [multiset_map_all]
    exact msRel_coe_iff_r.mp h

theorem Ax_comp (E : Ent A B) : Ax A ⊛ E = E := by
  ext a b
  constructor
  · rintro ⟨lperm, f, r, h⟩
    simp only [MsRel, Fin.getElem_fin, Multiset.toList_eq_singleton_iff, Multiset.map_eq_singleton,
      exists_eq_right] at h

    apply E.perm _ _ r

    have fBij : Function.Bijective f := fin_preimage.exists_sig_iff_bijective.mp
      fun v => ⟨Classical.choose (h v), (Classical.choose_spec (h v)).1⟩
    have ⟨fi, hl, hr⟩ := Function.bijective_iff_has_inverse.mp fBij

    have hEq : ∀ (v : Fin lperm.length), a[fi v] = lperm[v] := fun v => by
      obtain ⟨_, hFinset, hEq⟩ := h v
      rw [fin_preimage.bij _ hl hr, Multiset.singleton_inj] at hFinset
      subst hFinset
      exact hEq

    have hlEq : a.length = lperm.length := by
      have : (FinEnum.card (Fin a.length)) = 
          (FinEnum.ofEquiv (Fin a.length) ((Equiv.ofBijective f fBij).symm)).card
          := rfl
      simpa using this
    apply List.ex_sigma_perm
    refine ⟨⟨f ∘ Fin.cast hlEq.symm, Function.Bijective.comp fBij bij_f_cast⟩, ?_⟩
    apply List.ext_getElem (List.apply_sig_length.trans hlEq.symm)
    intro i h₁ h₂
    simp only [List.apply_sig, List.getElem_ofFn, Function.comp_apply, Fin.cast_mk,
      List.get_eq_getElem]
    calc
      lperm[f ⟨i, h₂⟩]
        = a[fi (f ⟨i, h₂⟩)] := (hEq (f ⟨i, h₂⟩)).symm
      _ = a[Fin.mk i h₂] := by rw [hl ⟨i, h₂⟩]
  · intro h
    use a, id
    simp [h, MsRel]
    /- refine ⟨a.map (fun a => ⟨{a}, a, ⟨_, rfl, rfl⟩⟩), ?_, ?_⟩ -/
    /- · simpa -/
    /- · simp -/

theorem comp_assoc {W X Y Z} (f : Ent W X) (g : Ent X Y) (h : Ent Y Z)
    : (f ⊛ g) ⊛ h = f ⊛ g ⊛ h := by
  ext a b
  constructor
  · rintro ⟨lwp, fMap, hr, hfa⟩
    simp only [MsRel, comp, Fin.getElem_fin, exists_and_left] at hfa
    refine ⟨?_, ?_, ?_⟩
    stop
    refine ⟨(lwp.map (fun v => Classical.choose (CompObj.r v))).sum, ?_, ?_⟩
    · refine ⟨lwp.map (fun v => CompObj.mk _ _ (Classical.choose_spec (CompObj.r v)).left), ?_, ?_⟩
      · rw [Multiset.map_map]
        exact hr
      · simp [Multiset.map_map]
    · simp
      clear *-
      induction lwp using Quot.ind; rename_i lwp
      induction lwp
      · simp
      case cons hd tl ih =>
        simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sum_coe, List.map_cons,
          List.sum_cons, Multiset.sum_add] at ih ⊢
        rw [←(Classical.choose_spec hd.r).right, ←ih]
  · rintro ⟨lx, fMap, ⟨lym, gMap, hh, hhAll⟩, hyAll⟩
    refine ⟨lym, gMap ∘ fMap, hh, fun iLym => ?_⟩
    refine ⟨lx, ?_, ?_⟩
    simp only [Fin.getElem_fin, Multiset.length_toList, Multiset.card_map]
    stop
    rintro ⟨lwf, ⟨lwg, hlwg, gperm⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    stop
    refine ⟨lwp, lw'', by simpa, rel, ?_⟩
    have fa := List.forall₂_iff_get.mp fa
    have fa' := List.forall₂_iff_get.mp fa'
    apply List.forall₂_iff_get.mpr ⟨?_, ?_⟩
    · have := List.Perm.length_eq wperm
      have := List.Perm.length_eq wperm'
      sorry

    · sorry

end Ent

@[pp_with_univ]
structure EType where
  ofType ::
  toType : Type u

instance : Category EType where
  Hom   a b := Ent a.toType b.toType
  comp  := Ent.comp
  id X := Ent.Ax X.toType
  id_comp := Ent.Ax_comp
  comp_id := Ent.comp_Ax
  assoc   := Ent.comp_assoc

namespace EType
open EType Ent

instance isTermEmpt : Limits.IsTerminal (ofType PEmpty) :=
  .ofUniqueHom (fun _Y => {
    r _h _l := False
    perm _l _b f := f.elim
  }) fun _x _m => Ent.ext fun _a b => b.elim

instance : Limits.HasTerminal EType := isTermEmpt.hasTerminal

def not_initial (v : Limits.HasInitial EType.{u}) : False :=
  have := ofType PUnit |> Limits.uniqueFromInitial |>.uniq
  let alwaysTrue := {
    r _ _ := True
    perm _ _ _ _ _ := .intro
  }
  let alwaysFalse := {
    r _ _ := False
    perm _ _ := False.elim
  }
  have := (this alwaysTrue).trans (this alwaysFalse).symm

  (Ent.ext_iff.mp this [] .unit).mp True.intro

def fst (A B : EType.{u}) : ofType (A.toType ⊕ B.toType) ⟶ A where
  r a b := a = [.inl b]
  perm := by 
    rintro _ b' rfl a perm
    obtain rfl := List.singleton_perm.mp perm
    rfl

def snd (A B : EType.{u}) : ofType (A.toType ⊕ B.toType) ⟶ B where
  r a b := a = [.inr b]
  perm := by
    rintro _ b' rfl a perm
    obtain rfl := List.singleton_perm.mp perm
    rfl

def lift
    (A B : EType.{u})
    {T : EType.{u}}
    (f : T ⟶ A) (s : T ⟶ B) : T ⟶ { toType := A.toType ⊕ B.toType } where
  r tl := fun
    | .inl v => f.r tl v
    | .inr v => s.r tl v
  perm := fun 
    | l₁, .inl v, (h : f.r _ _), l₂, perm => f.perm _ _ h _ perm
    | l₁, .inr v, (h : s.r _ _), l₂, perm => s.perm _ _ h _ perm

instance isBiProdSum (A B : EType.{u}) : Limits.IsBinaryProduct (fst A B) (snd A B) :=
  .ofUniqueHom (lift A B)
    (fun {T} f g => by
      refine ext fun a b => ?_
      dsimp [CategoryStruct.comp, comp, MsRel]
      constructor
      · rintro ⟨lpart, fMap, rfl, hr⟩
        specialize hr ⟨0, by simp⟩
        simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
          Fin.zero_eta, Fin.isValue, fin_preimage.unit_inv] at hr
        change f.r (Multiset.map a.get Fintype.elems.val).toList b at hr
        rw [multiset_map_all] at hr
        apply f.perm _ _ hr _ Perm_ofList_toList.symm
      · intro hr
        refine ⟨_, (fun _ => ⟨0, by simp⟩), rfl, fun | ⟨0, _⟩ => ?_⟩
        simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
          Fin.zero_eta, Fin.isValue, fin_preimage.unit_inv]
        change f.r (Multiset.map a.get Fintype.elems.val).toList b
        rw [multiset_map_all]
        apply f.perm _ _ hr _ Perm_ofList_toList
      )
    (fun {T} f g => by
      refine ext fun a b => ?_
      dsimp [CategoryStruct.comp, comp, MsRel]
      constructor
      · rintro ⟨lpart, fMap, rfl, hr⟩
        specialize hr ⟨0, by simp⟩
        simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
          Fin.zero_eta, Fin.isValue, fin_preimage.unit_inv] at hr
        change g.r (Multiset.map a.get Fintype.elems.val).toList b at hr
        rw [multiset_map_all] at hr
        apply g.perm _ _ hr _ Perm_ofList_toList.symm
      · intro hr
        refine ⟨_, (fun _ => ⟨0, by simp⟩), rfl, fun | ⟨0, _⟩ => ?_⟩
        simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
          Fin.zero_eta, Fin.isValue, fin_preimage.unit_inv]
        change g.r (Multiset.map a.get Fintype.elems.val).toList b
        rw [multiset_map_all]
        apply g.perm _ _ hr _ Perm_ofList_toList
      )
    fun {T} f s t => by
      rintro rfl rfl
      refine ext fun | a, .inl b => ?il | a, .inr b => ?ir
      <;> dsimp [CategoryStruct.comp, Ent.comp, fst, snd, MsRel]
      <;> constructor

      case il.mp =>
        intro h
        refine ⟨_, fun _ => ⟨0, by simp⟩, rfl, fun | ⟨0, _⟩ => ?_⟩
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          fin_preimage.unit_inv, List.getElem_cons_zero]
        change t.r (Multiset.map a.get Fintype.elems.val).toList _
        rw [multiset_map_all]
        apply t.perm _ _ h _ Perm_ofList_toList
      case ir.mp =>
        intro h
        refine ⟨_, fun _ => ⟨0, by simp⟩, rfl, fun | ⟨0, _⟩ => ?_⟩
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          fin_preimage.unit_inv, List.getElem_cons_zero]
        change t.r (Multiset.map a.get Fintype.elems.val).toList _
        rw [multiset_map_all]
        apply t.perm _ _ h _ Perm_ofList_toList

      case il.mpr =>
        rintro ⟨_, f, rfl, fa⟩
        specialize fa ⟨0, by simp⟩
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          fin_preimage.unit_inv, List.getElem_cons_zero] at fa
        change t.r (Multiset.map a.get Fintype.elems.val).toList _ at fa
        rw [multiset_map_all] at fa
        apply t.perm _ _ fa _ Perm_ofList_toList.symm
      case ir.mpr =>
        rintro ⟨_, f, rfl, fa⟩
        specialize fa ⟨0, by simp⟩
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          fin_preimage.unit_inv, List.getElem_cons_zero] at fa
        change t.r (Multiset.map a.get Fintype.elems.val).toList _ at fa
        rw [multiset_map_all] at fa
        apply t.perm _ _ fa _ Perm_ofList_toList.symm

instance (A B : EType) : Limits.HasBinaryProduct A B :=
  Limits.IsBinaryProduct.hasBinaryProduct _ _ (isBiProdSum  _ _)
instance : Limits.HasBinaryProducts EType :=
  Limits.hasBinaryProducts_of_hasLimit_pair _

open Limits in
example (hCp : HasBinaryCoproducts EType) : False := by
  have msIso : (Multiset PEmpty → PUnit → Prop) ≃ Bool := {
    toFun v :=
      have : Decidable (v ∅ PUnit.unit) := Classical.propDecidable (v ∅ PUnit.unit)
      if v {} .unit then
        .true
      else
        .false
    invFun := fun
      | .true => fun _ _ => True
      | .false => fun _ _ => False

    left_inv v := funext fun a => funext fun | .unit => (by
      obtain rfl : a = 0 := Subsingleton.eq_zero a
      dsimp
      split
      <;> simpa)
    right_inv := fun | .true | .false => by simp
  }
  have equiv := (calc
    (Multiset (( ofType PEmpty ) ⨿ ( ofType PEmpty )).toType → Bool)
      ≃ _             := .arrowCongr (Equiv.prodPUnit _).symm Equiv.propEquivBool.symm
    _ ≃ _             := .curry _ _ _
    _ ≃ _             := equivMsRel.symm
    _ ≃ _             := Limits.coprod_homset_equiv (X := ofType PEmpty)
    _ ≃ (Multiset PEmpty → PUnit → Prop) × (Multiset PEmpty → PUnit → Prop) :=
                                                    (Equiv.prodCongr equivMsRel equivMsRel)
    _ ≃ Bool × Bool   := (Equiv.prodCongr msIso msIso)
    _ ≃ (Bool → Bool) := (Equiv.boolArrowEquivProd Bool).symm)
  have finF : Finite (Multiset (( ofType PEmpty ) ⨿ ( ofType PEmpty )).toType → Bool) :=
    Finite.of_equiv (Bool → Bool) equiv.symm

  have setIsEmp := multiset_finite <| fintype_card_eq finF
  have : 2 = 4 := Fintype.card_eq.mpr ⟨calc
    Bool ≃ _          := .symm (.punitArrowEquiv Bool)
    _ ≃ _             := .arrowCongr (Equiv.equivPUnit.{_, u} _).symm (.refl _)
    _ ≃ (Bool → Bool) := equiv⟩
  omega

open Limits IsBinaryProduct in
class IsExponential {𝓒} [Category 𝓒] (X Y Y_X : 𝓒) where
  prod : 𝓒 → 𝓒 → 𝓒
  fst (A B : 𝓒) : prod A B ⟶ A
  snd (A B : 𝓒) : prod A B ⟶ B
  isProd (A B : 𝓒) : IsBinaryProduct (fst A B) (snd A B)
  app : prod Y_X X ⟶ Y
  cur_ex (Z : 𝓒) (f : prod Z X ⟶ Y) : ∃! cur,
    map (fst _ _) (snd _ _) (isProd _ _) cur (𝟙 X) ≫ app = f

namespace IsExponential

open Limits

class All 𝓒 [Category 𝓒] where
  (prod exp : 𝓒 → 𝓒 → 𝓒)
  fst (A B : 𝓒) : prod A B ⟶ A
  snd (A B : 𝓒) : prod A B ⟶ B
  isProd (A B : 𝓒) : IsBinaryProduct (fst A B) (snd A B)
  equiv (X Y C : 𝓒) : (C ⟶ (exp X Y)) ≅ ((prod C X) ⟶ Y)

instance {𝓒} [Category 𝓒] (a : All 𝓒) {A B}
    : IsExponential A B (a.exp A B) where
  prod := _; fst := _; snd := _
  isProd := a.isProd
  app := (a.equiv _ _ _).hom (𝟙 _)
  cur_ex Z f := by
    refine ⟨(a.equiv _ _ _).inv f, ?_, ?_⟩
    · 
      dsimp [IsBinaryProduct.map]
      sorry
    · 
      sorry

end IsExponential

def expon' (C X Y : Type _)
    : (Multiset C → Multiset X × Y → Prop)
    ≃ (Multiset (C ⊕ X) → Y → Prop) where
  toFun   e l r := e (l.filterMap Sum.getLeft?) ⟨l.filterMap Sum.getRight?, r⟩
  invFun  e := fun l ⟨ms,r⟩ => e (ms.map Sum.inr + l.map Sum.inl) r
  left_inv e := by
    ext a ⟨ms, b⟩
    simp only [filterMap_add, Multiset.filterMap_map]
    unfold Function.comp
    simp [Multiset.filterMap_some]
  right_inv e := by
    ext v r
    suffices eq : (Multiset.filterMap (fun x ↦ Option.map Sum.inr x.getRight?) v +
      Multiset.filterMap (fun x ↦ Option.map Sum.inl x.getLeft?) v) = v by
      simp [Multiset.map_filterMap, eq]
    induction v using Quot.ind; rename_i v
    simp only [Multiset.quot_mk_to_coe'', Multiset.filterMap_coe, Multiset.coe_add,
      Multiset.coe_eq_coe]
    induction v
    · rfl
    case cons hd tl ih =>
      cases hd
      case inr => simpa
      simp only [Sum.getRight?_inl, Option.map_none, List.filterMap_cons_none, Sum.getLeft?_inl,
        Option.map_some, Option.some.injEq, List.filterMap_cons_some]
      apply List.perm_middle.trans
      rwa [List.perm_cons]

def expon (C X Y : Type _)
    : Ent C (Multiset X × Y)
    ≃ Ent (C ⊕ X) Y := calc
  Ent C (Multiset X × Y)
    ≃ (Multiset C → Multiset X × Y → Prop)  := equivMsRel
  _ ≃ (Multiset (C ⊕ X) → Y → Prop)         := expon' C X Y
  _ ≃ Ent (C ⊕ X) Y                         := equivMsRel.symm

#exit

open Limits in
instance {X Y : EType.{u}} : IsExponential X Y (ofType <| (Multiset X.toType) × Y.toType) where
  prod := _; fst := _; snd := _
  isProd A B := isBiProdSum A B
  app := {
    r ls v := ∃ l₁ l₂ n,
      l₂ = ls.filterMap Sum.getRight? ∧
      List.replicate n ⟨l₁, v⟩ = ls.filterMap Sum.getLeft? ∧
      l₁ = l₂
    perm la b := by
      rintro ⟨l₁, _, nr, rfl, hEq, rfl⟩ lb permab
      have hEqB := (List.perm_replicate.mpr hEq.symm).symm.trans 
        (List.Perm.filterMap Sum.getLeft? permab)
        |>.symm
        |> List.perm_replicate.mp
        |>.symm
      refine ⟨_, _ ,nr, rfl, hEqB, ?_⟩
      simp [List.Perm.filterMap Sum.getRight? permab]
  }
  cur_ex Z f := by
    refine ⟨
      {
        r v s := ∃ y z, v = [z] ∧ f.r (s.1.toList.map (Sum.inr)) y
        perm := by
          sorry
      },
      ?holds,
      ?uniq
    ⟩
    · change Ent.comp (lift _ _ _ _) _ = _
      dsimp [BinaryFan.fst, BinaryFan.snd]
      refine Ent.ext fun a b => ⟨?_, ?_⟩
      <;> dsimp [Ent.comp]
      · rintro ⟨w, fM, ⟨_, _, _, _⟩, hr⟩
        simp [MsRel, snd,fst,lift, CategoryStruct.comp, comp] at hr
        sorry
      · sorry
    · sorry

end EType

end Ex3

end CategoryTheory


