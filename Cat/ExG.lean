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

section lemmas

theorem fin_cast_linv {n m} (p : n = m) : Function.LeftInverse (Fin.cast p.symm) (Fin.cast p) :=
  fun _ => rfl
theorem fin_cast_rinv {n m} (p : n = m) : Function.RightInverse (Fin.cast p.symm) (Fin.cast p) :=
  fun _ => rfl

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
  induction a using Quot.ind;rename_i a
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


end lemmas

section Ex3

@[grind]
structure Ent (A B : Type u) where
  r : List A → B → Prop
  perm : ∀ l₁ b, r l₁ b → ∀ l₂, l₁.Perm l₂ → r l₂ b

namespace Ent

@[grind]
def MsRel (x : Ent A B) (ms : Multiset A) (bv : B) : Prop :=
  x.r ms.toList bv

def ofMsRel (R : Multiset A → B → Prop) : Ent A B where
  r ls b := R ls b
  perm l₁ b R l₂ lperm := by
    have : Multiset.ofList l₂ = Multiset.ofList l₁ := Multiset.coe_eq_coe.mpr lperm.symm
    rw [this]
    exact R

theorem msRel_iff_r_toList {l b} {E : Ent A B} : E.r l.toList b = E.MsRel l b := by
  grind
theorem msRel_coe_iff_r {l b} {E : Ent A B} : E.r l b = E.MsRel l b := by
  ext
  have : (l : Multiset _).toList.Perm l := Multiset.coe_eq_coe.mp <| by simp
  constructor <;> refine fun h => E.perm _ _ h _ ?_
  · exact this.symm
  · exact this

@[ext]
def ext {E F : Ent A B} (h : ∀ a b, E.r a b ↔ F.r a b) : E = F :=
  match E, F with
  | ⟨_, _⟩, ⟨_, _⟩ =>
    (mk.injEq _ _ _ _).mpr
    <| funext fun a => funext fun b => propext (h a b)

def equivMsRel : (Ent A B) ≃ (Multiset A → B → Prop) where
  toFun e ms v := e.r ms.toList v
  invFun := ofMsRel
  left_inv e := by
    ext a b
    constructor
    <;> rintro h
    <;> apply e.perm _ _ h
    <;> apply Multiset.coe_eq_coe.mp
    <;> simp
  right_inv v := funext fun a => funext fun b => by
    simp [ofMsRel]

variable (R : A → B → Prop)

abbrev LiftR : Ent A B where
  r a b := ∃ w, a = [w] ∧ R w b
  perm l b := by
    rintro ⟨w, rfl, rwb⟩
    simpa

abbrev Ax A : Ent A A := LiftR (· = ·)

-- The alternative is a sublist structure,
-- This might be more expressive but also harder
-- NOTE: This has the opposite order of how the question requests it.
--       This is done to conform with how lean does relational composition.

-- The question also contains:
-- > Remember to argue that if E ⊆ A* × B is an entailment from A to B and
-- > F ⊆ B* × C is an entailment from 𝐵 to 𝐶 then their composition
-- > F ⊛ E ⊆ A* × C is an entailment from A to C.
-- This follows from the type signatures for free because of working in a proof assistant.
-- Therefore I will assume I have argued for this.

def fin_preimage {A B} [fta : Fintype A] [DecidableEq B]
    (f : A → B) (b : B)
    : Multiset A :=
  fta.elems.val.filter (f · = b)

namespace fin_preimage

variable {A B C : Type _} [fta : Fintype A]

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

/- @[simp] -/
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

theorem exists_sig_iff_bijective {f : A → B} [DecidableEq B]
    : (∀ v, ∃ a, fin_preimage f v = {a}) ↔ Function.Bijective f := by
  conv => lhs; intro v; rw [exists_sig_iff_unique_valued]
  exact (Function.bijective_iff_existsUnique f).symm

end fin_preimage

def comp (E : Ent A B) (F : Ent B C) : Ent A C where
  r := fun ls c =>
    ∃ lpart : List B, ∃ f : Fin ls.length → Fin lpart.length,
      F.r lpart c ∧ ∀ v : Fin _, E.MsRel (fin_preimage f v |>.map (ls[·])) lpart[v]
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

theorem comp_iff_comp'
    (E : Ent A B) (F : Ent B C)
    : comp E F = equivMsRel.invFun (comp' (equivMsRel.toFun E) (equivMsRel.toFun F)) := by
  ext a b
  dsimp [equivMsRel, ofMsRel, comp, comp']
  constructor
  · sorry
  · rintro ⟨lpart, hl, hr⟩
    refine ⟨_, ?_, hl, ?_⟩
    · simp
      sorry
    · intro v
      simp
      sorry

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

def fintype_card_eq : Finite (A → Bool) → Finite A := by
  contrapose
  simp only [not_finite_iff_infinite]
  exact fun a ↦ Function.infinite_of_left

theorem ms_finite : Finite (Multiset A) → IsEmpty A := by
  contrapose
  simp only [not_isEmpty_iff, not_finite_iff_infinite, Nonempty.forall]
  intro a
  apply Infinite.of_injective (β := Nat) (Multiset.replicate · a)
  intro a b h
  simp only [Multiset.eq_replicate, Multiset.card_replicate] at h
  exact h.1

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

  have setIsEmp := ms_finite <| fintype_card_eq finF
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
  equiv (X Y C : 𝓒) : (C ⟶ (exp X Y)) ≃ ((prod C X) ⟶ Y)

instance {𝓒} [Category 𝓒] (a : All 𝓒) {A B}
    : IsExponential A B (a.exp A B) where
  prod := _; fst := _; snd := _
  isProd := a.isProd
  app := (a.equiv _ _ _).toFun (𝟙 _)
  cur_ex Z f := by
    refine ⟨(a.equiv _ _ _).invFun f, ?_, ?_⟩
    · dsimp
      sorry
    · sorry


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


