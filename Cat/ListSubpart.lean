import Mathlib.Data.List.Defs
import Mathlib.Data.List.Sublists

universe u

namespace List

variable {A : Type u}

inductive Subpart (n : Nat) : List A → List (List A) → Prop
  | nil : Subpart n [] (List.replicate n [])
  | consN {hd tl tl'}
    (idx : Nat)
    (h : idx < n)
    (rest : Subpart n tl tl')
    : Subpart n (hd :: tl) (tl'.modify idx (hd :: ·))

namespace Subpart

variable {n : Nat} {a : List A} {bs : List (List A)}

theorem zero (sp : Subpart 0 a bs) : bs = [] := by
  induction sp
  · rfl
  case consN idx _ _ => contradiction

theorem nz (sp : Subpart n.succ a bs) : bs ≠ [] := by
  induction sp
  · simp
  case consN ih =>
    by_contra!
    simp_all

theorem zero' (sp : Subpart n a []) : n = 0 := by
  generalize h : [] = z at sp
  induction sp
  · simp at h
    assumption
  · simp_all

theorem modOut {v f idx}
    (hmod : (a.modify idx f) ~ v)
    : ∃ jdx z, a ~ z ∧ v = z.modify jdx f := by
  generalize h' : a.modify idx f = av at hmod
  induction hmod
  · simp_all
  · simp_all
  · sorry
  · sorry

theorem all_Perm_mem {cs} (sp : Subpart n a bs) (perm : bs.Perm cs) : Subpart n a cs := by
  induction sp generalizing cs
  · simp at perm
    subst perm
    exact nil
  case consN ih =>
    sorry

theorem mem_Subpart_sublist {a : List A} {bs} : (Subpart n.succ a bs) → ∀ b ∈ bs, b.Sublist a
  | .nil, _, _=> by simp_all
  | .consN (tl' := tl') idx hidx hsp, b, bmem => by
    induction idx
    · cases tl'
      · simp_all
      · simp only [modify_zero_cons, mem_cons] at bmem
        cases bmem 
        · rename_i h
          subst h
          have := mem_Subpart_sublist hsp
          simp_all
        · have := mem_Subpart_sublist hsp
          simp_all
    case succ ih' =>
      specialize ih' (by omega)
      cases tl'
      · simp_all
      simp at bmem
      cases bmem
      · rename_i h
        subst h
        sorry
      · sorry

end Subpart

end List


