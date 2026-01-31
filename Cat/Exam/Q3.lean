import Mathlib.CategoryTheory.Limits.Shapes.Terminal

universe u

open CategoryTheory

variable {C : Type u} [Category C] (F : C ⥤ C)

structure Alg where
  A : C
  α : F.obj A ⟶ A

structure AlgHom (A B : Alg F) where
  h : A.A ⟶ B.A
  eq : F.map h ≫ B.α = A.α ≫ h

def AlgHom.comp
    {X Y Z : Alg F}
    (f : AlgHom F X Y)
    (g : AlgHom F Y Z)
    : AlgHom F X Z where
  h := f.h ≫ g.h
  eq := calc
    F.map (f.h ≫ g.h) ≫ Z.α 
      = F.map f.h ≫ F.map g.h ≫ Z.α := by simp
    _ = (F.map f.h ≫ Y.α) ≫ g.h := by rw [g.eq, Category.assoc]
    _ = X.α ≫ f.h ≫ g.h := by rw [f.eq, Category.assoc]

instance : Category (Alg F) where
  Hom := AlgHom F
  id _ := { h := 𝟙 _, eq := by simp}
  comp {X Y Z} f g := AlgHom.comp F f g

  comp_id f := by simp [AlgHom.comp]
  id_comp f := by simp [AlgHom.comp]
  assoc f := by simp [AlgHom.comp]

def FUp (v : Alg F) : Alg F where
  A := F.obj v.A
  α := F.map v.α

@[simp]
theorem FUpA {O} : (FUp F O).A = F.obj O.A :=
  rfl

@[simp]
theorem FUpα {O} : (FUp F O).α = F.map O.α :=
  rfl

open Limits

variable [HasInitial (Alg F)]

noncomputable def down : FUp F (⊥_ Alg F) ⟶ ⊥_ Alg F where
  h := (⊥_ Alg F).α
  eq := rfl

example [HasInitial (Alg F)] : IsIso ((⊥_ (Alg F)).α) where
  out := ⟨
    (initial.to (FUp F (⊥_ _))).h,
    by
      have rhs : ((initial.to (FUp F (⊥_ Alg F))).h ≫ (⊥_ Alg F).α) = 𝟙 _ := calc
        (initial.to (FUp F (⊥_ Alg F)) ≫ down F).h
          = (initial.to (⊥_ Alg F)).h := by rw [initial.to_comp (down F)]
        _ = AlgHom.h (𝟙 (⊥_ Alg F)) := by rw
                                        [initial.hom_ext (𝟙 (⊥_ Alg F)) (initial.to (⊥_ Alg F))]
      constructor
      · calc
          (⊥_ Alg F).α ≫ (initial.to (FUp F (⊥_ Alg F))).h
            = F.map (initial.to (FUp F _)).h ≫ (FUp F (⊥_ _)).α            := by rw
                                                                        [←(initial.to (FUp F _)).eq]
        _ = F.map (initial.to (FUp F _)).h ≫ F.map (⊥_ Alg F).α       := rfl
        _ = F.map ((initial.to (FUp F (⊥_ Alg F))).h ≫ (⊥_ Alg F).α)  := by rw [F.map_comp]
        _ = F.map (𝟙 _)                                               := by rw [rhs]
        _ = 𝟙 _                                                       := by rw [Functor.map_id]
      · exact rhs,
  ⟩

