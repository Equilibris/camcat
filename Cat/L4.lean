import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Cat.L1

universe u

open CategoryTheory

variable {C : Type _} [cat : Category C] (X Y : C)

structure ProdObj where
  Z : C
  fst : Z ⟶ X
  snd : Z ⟶ Y

structure ProdHom (x y : ProdObj X Y) : Type _ where
  h : x.Z ⟶ y.Z
  d1 : x.fst = h ≫ y.fst
  d2 : x.snd = h ≫ y.snd

instance : Category (ProdObj X Y) where
  Hom := ProdHom X Y
  id := fun x => ⟨𝟙 _, by simp, by simp⟩
  comp := fun {X Y Z} x y => ⟨
    x.h ≫ y.h,
    calc
      X.fst
        = x.h ≫ Y.fst := x.d1
      _ = x.h ≫ y.h ≫ Z.fst := by rw [y.d1]
      _ = (x.h ≫ y.h) ≫ Z.fst := (Category.assoc _ _ _).symm,
    calc
      X.snd
        = x.h ≫ Y.snd := x.d2
      _ = x.h ≫ y.h ≫ Z.snd := by rw [y.d2]
      _ = (x.h ≫ y.h) ≫ Z.snd := (Category.assoc _ _ _).symm
  ⟩

variable {X Y}

def forget : ProdObj X Y ⥤ C where
  obj := ProdObj.Z
  map := ProdHom.h

def forget.fst (o : ProdObj X Y) : forget.obj o ⟶ X := o.fst
def forget.snd (o : ProdObj X Y) : forget.obj o ⟶ Y := o.snd

class HasProd {C : Type _} [Category C] (X Y : C) where
  term : ProdObj X Y
  prod : Limits.IsTerminal term

namespace HasProd

variable (X Y X' Y' : C) [inst : ∀ X Y : C, HasProd X Y]

abbrev obj (x y : C) : C := ProdObj.Z <| (inst x y).term

-- TODO: Find the right assoc and strength
infixr:100 "×c" => HasProd.obj

def fst : X ×c Y ⟶ X := ProdObj.fst _
def snd : X ×c Y ⟶ Y := ProdObj.snd _

def func (m0 : X ⟶ X') (m1 : Y ⟶ Y') : ProdObj X Y ⥤ ProdObj X' Y' where
  obj := fun ⟨Z, f, g⟩ => ⟨Z, f ≫ m0, g ≫ m1⟩
  map := fun ⟨h, d1, d2⟩ => ⟨
    h,
    by dsimp; rw [←Category.assoc, ←d1],
    by dsimp; rw [←Category.assoc, ←d2]
  ⟩

/- def par (m0 : X ⟶ X') (m1 : Y ⟶ Y') : X ×c Y ⟶ X' ×c Y' := -/
/-   (prod X' Y').from ((func m0 m1).obj (term X Y)) -/

instance [inst : HasProd X Y] : Limits.HasBinaryProduct X Y :=
  Limits.HasLimit.mk
    ⟨
    ⟨
      inst.term.Z,
      fun | ⟨.left⟩ => term.fst | ⟨.right⟩ => term.snd,
      by rintro (x|x) (y|y) ⟨_, _⟩ <;> simp
    ⟩,
    by
    apply Limits.IsLimit.mkConeMorphism
    case lift =>
      intro cone
      let po : ProdObj X Y := {
        Z := cone.pt,
        fst := cone.π.app ⟨.left⟩,
        snd := cone.π.app ⟨.right⟩,
      }
      dsimp
      let uniq := inst.prod.uniq (Limits.asEmptyCone po)
      let lift := inst.prod.lift (Limits.asEmptyCone po)
      simp at uniq lift ⊢
      change Limits.ConeMorphism _ _
      refine Limits.ConeMorphism.mk (ProdHom.h lift) ?_
      intro x
      rcases x with ⟨_|_⟩
      <;> simp
      · sorry
      · sorry
      
    simp
    sorry
    /- { -/
    /-   lift | ⟨pt, f, _⟩ => (by -/
    /-     let po : ProdObj X Y := { -/
    /-       Z := pt, -/
    /-       fst := f ⟨.left⟩ -/
    /-       snd := f ⟨.right⟩ -/
    /-     } -/
    /-     change po.Z ⟶ _ -/
    /-     apply ProdHom.h -/
    /-     exact inst.prod.from po), -/
    /-   fac -/
    /-     | ⟨pt, f, hFNat⟩, ⟨.left⟩ -/
    /-     | ⟨pt, f, hFNat⟩, ⟨.right⟩ => (by -/
    /-       simp at f hFNat ⊢ -/
    /-       sorry -/
    /-     ) -/
    /-   uniq := sorry -/
    /- } -/
  ⟩

end HasProd

section Prods

def Prod.corec {γ α β : Type _}
      (f : γ → α) (g : γ → β) (v : γ) : α × β :=
  ⟨f v, g v⟩

instance {X Y : Type u} : HasProd X Y where
  term := ⟨X × Y, Prod.fst, Prod.snd⟩
  prod := Limits.IsTerminal.ofUniqueHom
    (fun po => ⟨Prod.corec po.fst po.snd, rfl, rfl⟩)
    (fun _ ⟨h, d1, d2⟩ => by
      congr
      rw [d1, d2]; clear d1 d2; dsimp at h ⊢
      ext v <;> rfl)

instance {α : Type u} [SemilatticeInf α] {X Y : α} : HasProd X Y where
  term := (⟨X ⊓ Y, .up inf_le_left, .up inf_le_right⟩)
  prod := Limits.IsTerminal.ofUniqueHom
    (fun po => ⟨.up (le_inf po.fst.down po.snd.down), rfl, rfl⟩)
    (fun _ _ => rfl) -- Subsingleton elim

instance cMon (o : C) : Monoid (o ⟶ o) where
  one := 𝟙 o
  mul := (· ≫ ·)
  mul_assoc := Category.assoc
  one_mul := Category.id_comp
  mul_one := Category.comp_id

instance (priority := low)
    -- [∀ a b : C, Subsingleton (a ⟶ b)]
    : Preorder C where
  le := (Nonempty <| · ⟶ ·)
  le_refl a := .intro (𝟙 a)
  le_trans a b c := fun ⟨f⟩ ⟨g⟩ => .intro (f ≫ g)

end Prods

