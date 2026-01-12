/- import Mathlib.CategoryTheory.Closed.Cartesian -/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Cat.Product

universe u
variable
    {𝓒 : Type u}
    [CategoryTheory.Category 𝓒]
    {U V W X Y Z P T : 𝓒}

namespace CategoryTheory

-- Recursive tactic for repeated reassociation
syntax "reassoc_rw" (num)* : tactic

macro_rules
| `(tactic| reassoc_rw) => `(tactic| skip)
| `(tactic| reassoc_rw $n:num $ns:num*) =>
    `(tactic|
      nth_rw $n:num [← Category.assoc];
      simp only [
        _root_.CategoryTheory.Limits.IsBinaryProduct.lift_fst,
        _root_.CategoryTheory.Limits.IsBinaryProduct.lift_snd,
        _root_.CategoryTheory.Limits.IsBinaryProduct.lift_comp,
        _root_.CategoryTheory.Category.assoc,
        _root_.CategoryTheory.Category.comp_id,
        _root_.CategoryTheory.Category.id_comp,
        ];
      reassoc_rw $ns:num*)

open Limits in
class SimpleCartesianMonoidalCategory (C : Type u) [Category C] where
  tensorUnit : C
  isTerminalTensorUnit : Limits.IsTerminal tensorUnit

  tensorObj : C → C → C
  fst (X Y : C) : tensorObj X Y ⟶ X
  snd (X Y : C) : tensorObj X Y ⟶ Y

  tensorProductIsBinaryProduct (X Y : C) : IsBinaryProduct (fst X Y) (snd X Y)

open Limits in
instance scmcCmc [scmc : SimpleCartesianMonoidalCategory 𝓒] : CartesianMonoidalCategory 𝓒 where
  tensorUnit := scmc.tensorUnit
  isTerminalTensorUnit := scmc.isTerminalTensorUnit

  tensorObj := scmc.tensorObj

  fst := scmc.fst
  snd := scmc.snd

  tensorProductIsBinaryProduct := scmc.tensorProductIsBinaryProduct

  associator X Y Z := IsBinaryProduct.associator
    (scmc.tensorProductIsBinaryProduct _ _)
    (scmc.tensorProductIsBinaryProduct _ _)
    (scmc.tensorProductIsBinaryProduct _ _)
    (scmc.tensorProductIsBinaryProduct _ _)
  leftUnitor X := IsBinaryProduct.leftUnitor 
    scmc.isTerminalTensorUnit
    (scmc.tensorProductIsBinaryProduct _ _)
  rightUnitor X := IsBinaryProduct.rightUnitor
    scmc.isTerminalTensorUnit
    (scmc.tensorProductIsBinaryProduct _ _)
  whiskerLeft X {Y₁ Y₂} m :=
    (scmc.tensorProductIsBinaryProduct X Y₂).lift (scmc.fst _ _) ((scmc.snd _ _) ≫ m)
  whiskerRight {Y₁ Y₂} m X :=
    (scmc.tensorProductIsBinaryProduct Y₂ X).lift (scmc.fst _ _ ≫ m) (scmc.snd _ _)

  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by 
    apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    · reassoc_rw 1 1
    · reassoc_rw 1 1 1 2

  associator_naturality f₁ f₂ f₃ := by
    simp only [IsBinaryProduct.lift_comp, IsBinaryProduct.lift_fst, IsBinaryProduct.associator,
      IsBinaryProduct.lift_snd]
    apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    any_goals apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    · reassoc_rw 1 2
    · reassoc_rw 1 1 2 2 2 2
    · reassoc_rw 1 1 1 1 1 1
  leftUnitor_naturality f := by
    simp [IsBinaryProduct.leftUnitor]
  rightUnitor_naturality f := by
    simp [IsBinaryProduct.rightUnitor]

  pentagon W X Y Z := by
    simp only [IsBinaryProduct.associator, IsBinaryProduct.lift_comp, IsBinaryProduct.lift_fst,
      IsBinaryProduct.lift_snd]
    apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    any_goals apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    any_goals apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    · reassoc_rw 1 2
    · reassoc_rw 1 1 1 1 1 1 2
    · reassoc_rw 1 1 1 1 1 1
    · reassoc_rw 1 1 1
  triangle X Y := by
    simp only [IsBinaryProduct.associator, IsBinaryProduct.leftUnitor, IsBinaryProduct.lift_comp,
      IsBinaryProduct.lift_fst, IsBinaryProduct.rightUnitor]
    apply (scmc.tensorProductIsBinaryProduct _ _).hom_ext
    · simp
    · reassoc_rw 1
  fst_def X Y := by
    simp [IsBinaryProduct.rightUnitor]
  snd_def X Y := by
    simp [IsBinaryProduct.leftUnitor]

section Bi

end Bi

end CategoryTheory
