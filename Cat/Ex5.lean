import Mathlib.Tactic.DepRewrite
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Nat
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.Ex2
import Cat.Ex4
import Cat.HEq

open CategoryTheory
open Limits

universe u v

variable {𝓒 : Type u} [Category.{v, u} 𝓒] {A B X Y Z X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝓒}

section

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

instance {F G : P ⥤ Q} : Subsingleton (NatTrans F G) where
  allEq _ _ := NatTrans.ext (funext
    fun _ => Subsingleton.allEq (α := PLift _) _ _)

def orderAdj {F : P ⥤ Q} {G : Q ⥤ P}
    (h : ∀ {X Y}, X ≤ F.obj Y ↔ G.obj X ≤ Y) : G ⊣ F :=
  .mkOfHomEquiv {
    homEquiv X Y := {
      toFun := PLift.up ∘ h.mpr ∘ PLift.down
      invFun := PLift.up ∘ h.mp ∘ PLift.down
      left_inv := fun ⟨x⟩ => rfl
      right_inv := fun ⟨x⟩ => rfl
    }
  }

def eOrderHom : P →o Q ≅ P ⥤  Q where
  hom v := {
    obj := v
    map (f : PLift _) := PLift.up (v.monotone f.down)
  }
  inv f := {
    toFun a := f.obj a
    monotone' a b h := (f.map (.up h)).down
  }

end

def SetOrd : Type u ⥤ Sigma PartialOrder where
  obj X := ⟨Set X, by infer_instance⟩
  map f := {
    toFun x := setOf fun i => (∃ v ∈ x, f v = i)
    monotone' x y h := by
      rintro i ⟨w, hm, rfl⟩
      exact ⟨_, h hm, rfl⟩
  }
  map_id X := by
    apply OrderHom.ext
    simp
    rfl
  map_comp f g := by
    apply OrderHom.ext
    funext i
    simp [CategoryStruct.comp]

section

variable {A B : Type u} (f : A → B)

def finv : SetOrd.obj B ⟶ SetOrd.obj A where
  toFun (v : Set B) := setOf (f · ∈ v)
  monotone' _ _ h := fun _ h' => h h'

def exs : SetOrd.obj A ⟶ SetOrd.obj B where
  toFun (v : Set A) : Set B := setOf fun x => ∃ x', f x' = x ∧ x' ∈ v
  monotone' a b h := by
    rintro v ⟨_, rfl, mem⟩
    refine ⟨_, rfl, h mem⟩

def fa : SetOrd.obj A ⟶ SetOrd.obj B where
  toFun (v : Set A) : Set B := setOf fun x => ∀ x', f x' = x → x' ∈ v
  monotone' _ _ h _ h' w heq := h (h' w heq)

example : eOrderHom.hom (finv f) ⊣ eOrderHom.hom (fa f) :=
  .mkOfHomEquiv {
    homEquiv (X Y : Set _) := {
      toFun h := PLift.up <| by
        have h : {x | f x ∈ X} ≤ Y := h.down
        intro i v w rfl
        exact h v
      invFun h := PLift.up <| fun i h' => h.down h' _ rfl
      left_inv := fun ⟨_⟩ => rfl
      right_inv := fun ⟨_⟩ => rfl
    }
  }

example : eOrderHom.hom (exs f) ⊣ eOrderHom.hom (finv f) :=
  .mkOfHomEquiv {
    homEquiv (X Y : Set _) := {
      toFun h := PLift.up fun i h' => h.down (⟨i, rfl, h'⟩)
      invFun h := PLift.up fun i => by
        rintro ⟨_, rfl, h'⟩
        exact h.down h'
      left_inv  := fun ⟨_⟩ => rfl
      right_inv := fun ⟨_⟩ => rfl
    }
  }

example : eOrderHom.hom (finv f) ⊣ eOrderHom.hom (fa f) := orderAdj {
  mp h x h' := h h' x rfl
  mpr h x h' y := by rintro rfl; exact h h'
}

example : eOrderHom.hom (exs f) ⊣ eOrderHom.hom (finv f) := orderAdj {
  mp h x := by rintro ⟨_,rfl,h'⟩; exact h h'
  mpr h x h' := h ⟨x, rfl, h'⟩
}

end

section

variable [HasPullbacks 𝓒] (f : Y ⟶ X)

#check PullbackFunctor f

-- TODO
noncomputable example : Over.map f ⊣ PullbackFunctor f :=
  .mkOfHomEquiv {
    homEquiv X Y := {
      toFun v := by
        apply Over.homMk (pullback.lift X.hom v.left (by simp)) ?_
        dsimp [PullbackFunctor]
        rw [pullback.lift_fst]
      invFun v := by
        apply Over.homMk ?_ ?_
        · exact v.left ≫ pullback.snd _ _
        simp
        rw [←pullback.condition, ←Category.assoc]
        congr
        sorry
      left_inv := sorry
      right_inv := sorry
    }
  }

end

section

variable {𝓓 : Type u} [Category 𝓓] {F : 𝓒 ⥤ 𝓓} {G : 𝓓 ⥤ 𝓒} (adj : F ⊣ G)

-- TODO: Ex4

abbrev T (adj : F ⊣ G) := G ⋙ F

def T.μ : T adj ⋙ T adj ⟶ T adj :=
  .hcomp adj.counit (.id (T adj))
    ≫ eqToHom (Functor.id_comp (T adj))

#check adj.unit

end

