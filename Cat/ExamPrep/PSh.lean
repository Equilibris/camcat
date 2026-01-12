import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
/- import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian -/
import Mathlib.CategoryTheory.Yoneda
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.Ex2
import Cat.Ex4
import Cat.HEq

open CategoryTheory

universe u

section

variable {𝓒 : Type} [SmallCategory 𝓒]
  {X Y : 𝓒ᵒᵖ ⥤ Type}
  {f g : X ⟶ Y}

example
    (h : ∀ c : 𝓒, ∀ x : yoneda.obj c ⟶ X, x ≫ f = x ≫ g)
    : f = g := by
  ext S obj
  specialize h S.unop
  change ∀ (x : NatTrans _ _), _ at h
  have := h (yonedaEquiv.symm obj)
  rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right] at this
  simpa using this

end

section

variable {A B C : Type} [Category A] [Category B] [Category C]

def comp_func : (B ⥤ C) × (A ⥤ B) ⥤ (A ⥤ C) where
  obj := fun ⟨G, F⟩ => F ⋙ G
  map := fun {X Y} nt => match X, Y, nt with
    | ⟨F, G⟩, ⟨H, I⟩, ⟨ma, mb⟩ => NatTrans.hcomp mb ma
  map_id := fun ⟨G, F⟩ => by
    dsimp
    simp only [Functor.hcomp_id, Functor.whiskerRight_id']
  map_comp := fun {A B C} ⟨f, g⟩ ⟨h, i⟩ => 
    match A, B, C with
    | ⟨C0, C1⟩, ⟨C2, C3⟩, ⟨C4, C5⟩ => by
      dsimp at f g h i ⊢
      exact NatTrans.exchange _ _ _ _

end

namespace PSh

open Limits

variable {𝓒 : Type} [SmallCategory 𝓒]
  {X Y : 𝓒ᵒᵖ ⥤ Type}
  {f g : X ⟶ Y}

def constPsh : 𝓒ᵒᵖ ⥤ Type where
  obj _ := Unit
  map f _ := .unit

instance constIbp : IsTerminal (constPsh (𝓒 := 𝓒)) :=
  .ofUniqueHom
    (fun _ => { app X _ := .unit })
    (fun X m => by
      ext
      simp only
      rfl)

def pprod
    (X Y : 𝓒ᵒᵖ ⥤ Type)
    : 𝓒ᵒᵖ ⥤ Type where
  obj x := X.obj x × Y.obj x
  map f := fun ⟨a, b⟩ => ⟨X.map f a, Y.map f b⟩

namespace pprod

variable (X Y)

def fst : pprod X Y ⟶ X where
  app X := Prod.fst

def snd : pprod X Y ⟶ Y where
  app X := Prod.snd

def lift {X Y} {T : 𝓒ᵒᵖ ⥤ Type} (f : T ⟶ X) (g : T ⟶ Y) : (T ⟶ pprod X Y) where
  app := fun X v => ⟨f.app _ v, g.app _ v⟩
  naturality X Y v := by
    ext o
    simp only [pprod, types_comp_apply, Prod.mk.injEq]
    constructor
    · change (T.map v ≫ f.app Y) o = (f.app X ≫ _) _
      rw [f.naturality v]
    · change (T.map v ≫ g.app Y) o = (g.app X ≫ _) _
      rw [g.naturality v]

def map {X Y X' Y' : 𝓒ᵒᵖ ⥤ Type} (f : X ⟶ X') (g : Y ⟶ Y') : pprod X Y ⟶ pprod X' Y' where
  app X o := ⟨f.app _ o.1, g.app _ o.2⟩
  naturality U V h := by
    ext v
    rcases v with ⟨vl, vr⟩
    apply Prod.ext
    · change (X.map h ≫ f.app _) _ = (f.app _ ≫ X'.map h) _
      rw [f.naturality]
    · change (Y.map h ≫ g.app _) _ = (g.app _ ≫ Y'.map h) _
      rw [g.naturality]

instance ibp : IsBinaryProduct (pprod.fst X Y) (pprod.snd X Y) :=
  .ofUniqueHom
    (fun f g => lift f g)
    (fun f g => by
      ext o v
      simp [fst, lift])
    (fun f g => by
      ext o v
      simp [pprod.snd, lift])
    <| by
      rintro T _ _ m rfl rfl
      ext o v; apply Prod.ext
      <;> simp [pprod.fst, pprod.snd, lift]

end pprod

instance : CartesianMonoidalCategory (𝓒ᵒᵖ ⥤ Type) :=
  .ofChosenFiniteProducts
    { isLimit := constIbp, cone := _ }
    ({ isLimit := pprod.ibp · ·, cone := _ })

open scoped MonoidalCategory

def adjv (V : 𝓒ᵒᵖ ⥤ Type) : ((𝓒ᵒᵖ ⥤ Type) × 𝓒ᵒᵖ) ⥤ Type where
  obj X := (pprod (yoneda.obj X.2.unop) V) ⟶ X.1
  map {X Y} f n := (pprod.map (yoneda.map f.2.unop) (𝟙 _)) ≫ n ≫ f.1

instance exp_closed (V : 𝓒ᵒᵖ ⥤ Type) : Closed V where
  rightAdj := Functor.curry.obj <| adjv V
  adj := .mkOfHomEquiv {
    homEquiv X Y := {
      toFun v := {
        app U o := pprod.lift
            (pprod.snd (yoneda.obj (Opposite.unop (Y, U).2)) V)
            (pprod.fst (yoneda.obj (Opposite.unop (Y, U).2)) V ≫
              yonedaEquiv.symm o) ≫ v
        naturality X' Y' f := by
          ext o
          change pprod.lift (pprod.snd (yoneda.obj (Opposite.unop Y')) V)
                (pprod.fst (yoneda.obj Y'.unop) V ≫ yonedaEquiv.symm (X.map f o)) ≫
              v =
            pprod.map (yoneda.map f.unop) (𝟙 V) ≫
              pprod.lift (pprod.snd (yoneda.obj (Opposite.unop X')) V)
                  (pprod.fst (yoneda.obj X'.unop) V ≫ yonedaEquiv.symm o) ≫
                v
          ext U v
          rcases v with ⟨v₁, v₂⟩
          change v.app U (v₂, (yonedaEquiv.symm (X.map f o)).app U v₁)
            = v.app U (v₂, (yonedaEquiv.symm o).app U (v₁ ≫ f.unop))
          rw [yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply]
          simp
      }
      invFun v := {
        app U o := (v.app U o.2).app U ⟨𝟙 _, o.1⟩
        naturality X' Y' f := by
          funext ⟨ol, or⟩
          change (v.app Y' (X.map f or)).app Y' (𝟙 _, V.map f ol)
            = Y.map f ((v.app X' or).app X' (𝟙 _, ol))
          rw [show
              v.app Y' (X.map f or)
              = pprod.map (yoneda.map f.unop) (𝟙 V) ≫ v.app X' or ≫ 𝟙 Y
            from funext_iff.mp (v.naturality f) or]
          have := funext_iff.mp ((v.app X' or).naturality f) ⟨𝟙 _, ol⟩
          simpa [pprod.map, pprod] using this
      }
      left_inv o := by
        refine NatTrans.ext' (funext fun U ↦ ?_)
        funext ⟨va, vb⟩
        change o.app U (va, (yonedaEquiv.symm vb).app U (𝟙 (Opposite.unop U))) = o.app U (va, vb)
        rw [yonedaEquiv_symm_app_apply]
        simp
      right_inv v := by
        refine NatTrans.ext' (funext fun U ↦ ?_)
        funext o
        refine NatTrans.ext' (funext fun U' ↦ ?_)
        funext ⟨oa, ob⟩
        change (v.app U' ((yonedaEquiv.symm o).app U' oa)).app U' (𝟙 (Opposite.unop U'), ob)
          = (v.app U o).app U' (oa, ob)
        rw [yonedaEquiv_symm_app_apply, show
            v.app U' (X.map (Quiver.Hom.op oa) o)
            = pprod.map (yoneda.map oa) (𝟙 V) ≫ v.app U o ≫ 𝟙 Y
          from funext_iff.mp (v.naturality (.op oa)) o]
        change (v.app U o).app U' (𝟙 _ ≫ oa, ob) = (v.app U o).app U' (oa, ob)
        exact congr rfl (congr (congr rfl (Category.id_comp oa)) rfl)
    }
    homEquiv_naturality_right f g := by
      refine NatTrans.ext' (funext fun U ↦ ?_)
      funext o
      refine NatTrans.ext' (funext fun V ↦ ?_)
      funext ⟨va, vb⟩
      simp [adjv, pprod.lift, pprod.fst, pprod.snd, pprod.map]
  }

instance : MonoidalClosed (𝓒ᵒᵖ ⥤ Type) := ⟨exp_closed⟩

section

@[simp]
theorem app_curry {A X Y : 𝓒ᵒᵖ ⥤ Type} {v x} (h : A ⊗ Y ⟶ X) 
    : (MonoidalClosed.curry h).app v x = 
      pprod.lift (pprod.snd (yoneda.obj (Opposite.unop v)) A)
            (pprod.fst (yoneda.obj (Opposite.unop v)) A ≫ yonedaEquiv.symm x) ≫
          h
      := by
  simp [MonoidalClosed.curry, ihom.adjunction, Closed.adj, ]
  rfl

variable {A B X Y : 𝓒} [CartesianMonoidalCategory 𝓒]

def prod_yoneda : yoneda.obj A ⊗ yoneda.obj B ≅ yoneda.obj (A ⊗ B) where
  hom := 
    { app X o := CartesianMonoidalCategory.lift o.1 o.2 }
  inv := {
    app X o := ⟨(o ≫ CartesianMonoidalCategory.fst _ _ ), (o ≫ CartesianMonoidalCategory.snd _ _ )⟩
  }

@[simp]
theorem prod_yoneda_hom_app {c : 𝓒ᵒᵖ} {A B} {v} : (prod_yoneda (A := A) (B := B)).hom.app c v 
    = CartesianMonoidalCategory.lift v.1 v.2 := by
  simp [prod_yoneda]

@[simp]
theorem prod_yoneda_inv_app {c : 𝓒ᵒᵖ} {A B} {v} : (prod_yoneda (A := A) (B := B)).inv.app c v 
    = (v ≫ SemiCartesianMonoidalCategory.fst A B, v ≫ SemiCartesianMonoidalCategory.snd A B):= by
  simp [prod_yoneda]

def flip : A ⊗ B ≅ B ⊗ A where
  hom := (CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.snd _ _) (CartesianMonoidalCategory.fst _ _))
  inv := (CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.snd _ _) (CartesianMonoidalCategory.fst _ _))
  hom_inv_id := by
    simp
  inv_hom_id := by
    simp

@[simp]
theorem flip_hom : flip.inv = (flip.hom : A ⊗ B ⟶ _) := by
  rfl

@[simp]
theorem flip_inv : flip.hom ≫ flip.hom = 𝟙 (A ⊗ B) := by
  simp [flip]

@[simp, reassoc (attr := simp)]
theorem flip_whiskerLeft {f : X ⟶ Y} : A ◁ f ≫ flip.hom = flip.hom ≫ f ▷ A := by
  simp [flip]

@[simp, reassoc (attr := simp)]
theorem flip_whiskerRight {f : X ⟶ Y} : f ▷ A ≫ flip.hom = flip.hom ≫ A ◁ f := by
  simp [flip]

def exp_yoneda
    [CartesianMonoidalCategory 𝓒] {B A : 𝓒} [Closed A]
    : yoneda.obj (A ⟶[𝓒] B) ≅ yoneda.obj A ⟶[𝓒ᵒᵖ ⥤ Type] yoneda.obj B where
  hom := MonoidalClosed.curry (prod_yoneda.hom ≫ yoneda.map (MonoidalClosed.uncurry (𝟙 _)))
  inv := {
    app X o := MonoidalClosed.curry <| flip.hom ≫ yonedaEquiv (prod_yoneda.inv ≫ o)
    naturality X Y f := by 
      ext v
      simp only [yoneda_obj_obj, op_tensorObj, Opposite.op_unop, unop_tensorObj, types_comp_apply,
        yoneda_obj_map]
      rw [←MonoidalClosed.curry_natural_left]
      apply (MonoidalClosed.curry_eq_iff _ _).mpr
      simp only [flip_whiskerLeft_assoc, MonoidalClosed.uncurry_curry, Iso.cancel_iso_hom_left]
      simp only [yonedaEquiv, op_tensorObj, Opposite.op_unop, yoneda_obj_obj, unop_tensorObj,
        yoneda_obj_map, Quiver.Hom.unop_op, prod_yoneda, ihom, Closed.rightAdj, adjv, prod_Hom,
        pprod.map, yoneda_map_app, NatTrans.id_app, types_id_apply, Functor.curry_obj_obj_map,
        Category.comp_id, Equiv.coe_fn_mk, FunctorToTypes.comp, Category.id_comp]
      have := funext_iff.mp  (v.naturality (.op (f.unop ▷ A)))
      dsimp [pprod] at this ⊢
      rw [←this]
      simp
  }
  hom_inv_id := by 
    ext U v
    apply (MonoidalClosed.curry_eq_iff _ _).mpr
    refine (Iso.eq_inv_comp flip).mp ?_
    refine (Equiv.apply_eq_iff_eq_symm_apply yonedaEquiv).mpr ?_
    ext U' v'
    dsimp at v' v
    simp only [yoneda_obj_obj, app_curry, pprod.lift, pprod.snd, pprod.fst, Opposite.op_unop,
      yonedaEquiv, yoneda_obj_map, Quiver.Hom.unop_op, Equiv.coe_fn_symm_mk, FunctorToTypes.comp,
      prod_yoneda_inv_app, Category.assoc, prod_yoneda_hom_app, yoneda_map_app, op_tensorObj,
      unop_tensorObj, flip_hom, NatTrans.id_app, types_id_apply]
    nth_rw 2 [←Category.comp_id v]
    rw [MonoidalClosed.uncurry_natural_left]
    simp [flip, CartesianMonoidalCategory.comp_lift_assoc]
  inv_hom_id := by 
    ext U v
    simp only [op_tensorObj, Opposite.op_unop, yoneda_obj_obj, unop_tensorObj, FunctorToTypes.comp,
      app_curry, NatTrans.id_app, types_id_apply]
    apply NatTrans.ext
    funext U' ⟨vl, vr⟩
    simp only [yoneda_obj_obj, pprod.lift, pprod.snd, pprod.fst, yonedaEquiv, Opposite.op_unop,
      yoneda_obj_map, Quiver.Hom.unop_op, op_tensorObj, unop_tensorObj, Equiv.coe_fn_mk,
      FunctorToTypes.comp, prod_yoneda_inv_app, Category.id_comp, Equiv.coe_fn_symm_mk,
      prod_yoneda_hom_app, yoneda_map_app]
    have := funext_iff.mp <| v.naturality <| .op (flip.hom : A ⊗ Opposite.unop U ⟶ _)
    dsimp [pprod] at this
    rw [←this]; clear this
    simp only [flip, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
    rw [←Category.comp_id vr, ←CartesianMonoidalCategory.lift_map,
      MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc,
      ←MonoidalClosed.uncurry_natural_left]
    simp only [MonoidalCategory.id_whiskerRight, Category.comp_id, MonoidalClosed.uncurry_curry,
      Category.id_comp]
    have := funext_iff.mp <| v.naturality <| .op (CartesianMonoidalCategory.lift vr vl)
    dsimp [pprod] at this
    rw [←this]; clear this
    simp

def pointwise_repr (G : 𝓒ᵒᵖ ⥤ Type) {c v}
    : ((yoneda.obj c) ⟶[_] G).obj v ≅ G.obj (v ⊗ .op c) where
  hom h := yonedaEquiv (prod_yoneda.inv ≫ h)
  inv h := prod_yoneda.hom ≫ yonedaEquiv.symm h
  inv_hom_id := by
    ext o
    simp only [op_tensorObj, Opposite.op_unop, types_comp_apply, Iso.inv_hom_id_assoc,
      types_id_apply]
    exact Equiv.apply_symm_apply yonedaEquiv o

end

end PSh

