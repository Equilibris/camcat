import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Cat.L1

universe u

open CategoryTheory

instance : PartialOrder PEmpty where
  le := fun _ => PEmpty.elim
  le_refl := fun x => PEmpty.elim x
  le_trans := fun x => PEmpty.elim x
  le_antisymm := fun x => PEmpty.elim x
  lt_iff_le_not_ge x := x.elim

/- instance : @Limits.HasInitial (Sigma PartialOrder) poOrd := by -/
/-   apply Limits.IsInitial.hasInitial -/
/-   case X => exact ⟨PEmpty, inferInstance⟩ -/
/-   apply Limits.IsInitial.ofUniqueHom (fun _ => sorry) -/
/-   sorry -/


def isTerminalPUnit : Limits.IsTerminal PUnit.{u + 1} :=
  Limits.IsTerminal.ofUniqueHom
    (fun _ _ => PUnit.unit)
    fun _ _ => rfl


instance : Limits.HasTerminal (Type u) :=
  Limits.IsTerminal.hasTerminal isTerminalPUnit

instance : @Limits.HasTerminal (Sigma PartialOrder) poOrd := by
  apply Limits.IsTerminal.hasTerminal (X := ⟨PUnit, by infer_instance⟩)
  apply Limits.IsTerminal.ofUniqueHom
  case h =>
    exact fun a => ⟨fun _ => .unit, fun ⦃a_1 b⦄ a ↦ .intro⟩
  · intros
    rfl

instance {α : _} : Monoid (List α) where
  one := []
  mul := List.append
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

structure SMonObj (S : Type u) where
  M : Type u
  f : S → M
  mon : Monoid M

instance sMon {S : Type _} : Category (SMonObj S) where
  Hom := fun ⟨M₁, f₁, mon₁⟩ ⟨M₂, f₂, mon₂⟩ => (f : MonoidHom M₁ M₂) ×' f₂ = f ∘ f₁
  id := fun ⟨M, f, mon⟩ => ⟨MonoidHom.id M, rfl⟩
  comp := fun {X Y Z} ⟨f, hf⟩ ⟨g, hg⟩ =>
    have ⟨Mx, fx, monx⟩ := X
    have ⟨My, fy, mony⟩ := Y
    have ⟨Mz, fz, monz⟩ := Z
    ⟨g.comp f, by rw [MonoidHom.coe_comp, Function.comp_assoc, ←hf, ←hg]⟩

def initial (S : Type u) : SMonObj S where
  M := List S
  f := ([·])
  mon := by infer_instance

namespace initial

def homo
    {S M : Type u}
    (f : S → M)
    [mon : Monoid M]
    : List S →* M where
  toFun := List.foldr (f · * ·) 1
  map_one' := rfl
  map_mul' := fun x y => by
    change List.foldr _ _ (x ++ y) = _
    rw [List.foldr_append]
    induction x
    · simp [mon.one_mul]
    case cons hd tl ih =>
      change _ * _ = _ * _ * _
      rw [mul_assoc, ih]

end initial

open initial in
instance sliceInit {S : Type u} : Limits.HasInitial (SMonObj S) := by
  apply Limits.IsInitial.hasInitial (X := initial S)
  apply Limits.IsInitial.ofUniqueHom
    (fun ⟨M, f, mon⟩ => ⟨homo f, funext fun s => (mul_one (f s)).symm⟩)
  · intro ⟨M, f, mon⟩ ⟨homo, heq⟩
    congr
    apply MonoidHom.ext_iff.mpr
    intro ls
    induction ls
    · change homo 1 = _
      rw [homo.map_one]
      rfl
    case cons ih =>
      change homo ([_] * _) = _ * (initial.homo f) _
      rw [homo.map_mul, ih]
      congr
      rw [heq]
      rfl

/-- info: 'sliceInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sliceInit

