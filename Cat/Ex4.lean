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
import Cat.L1
import Cat.L2Live
import Cat.Product
import Cat.Ex2
import Cat.HEq

open CategoryTheory 
open Limits

universe u v

variable {𝓒 : Type u} [Category.{v, u} 𝓒] {A B X Y Z X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝓒}

theorem mono_iff_pullback {f : Y ⟶ X} : Mono f ↔ IsPullback (𝟙 Y) (𝟙 Y) f f := by
  constructor
  · intro mf
    apply IsPullback.of_isLimit' {w := rfl}
    refine PullbackCone.isLimitAux' _ fun s =>
      ⟨s.fst, Category.comp_id s.fst, ?_, fun v h => v ▸ (Category.comp_id _).symm⟩
    trans s.fst
    · exact Category.comp_id s.fst
    exact mf.right_cancellation _ _ <| PullbackCone.condition s
  · refine fun sq => ⟨fun {Z} g h hsq => ?_⟩
    rw [←sq.lift_snd g h hsq, sq.lift_fst g h hsq]

variable {u : B ⟶ A} {f : Y ⟶ X} {q : B ⟶ Y} {p : A ⟶ X}
    (h1 : IsPullback u q p f)

set_option pp.proofs true in
example [mp : Mono p] : Mono q where
  right_cancellation {Z} i j hij :=
    have := mp.right_cancellation (i ≫ u) (j ≫ u) <| by 
      rw [Category.assoc, h1.w, ←Category.assoc, hij, Category.assoc, ←h1.w, Category.assoc]
    h1.hom_ext this hij

example [mp : IsIso p] : IsIso q := by
  refine ⟨h1.lift (f ≫ inv (I := mp)) (𝟙 _) ?_, ?_, ?_⟩
  · simp
  · apply h1.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst]
      rw [←Category.assoc, ←h1.w, Category.assoc, IsIso.hom_inv_id]
      simp
    · simp
  · simp

set_option pp.proofs true in
example : IsPullback (C := Type) (Prod.fst : Unit × Bool → Unit) Prod.snd id (fun _ => .unit) := by
  apply IsPullback.of_isLimit'
  case w => exact .mk (funext fun _ => rfl)
  refine PullbackCone.isLimitAux' _ fun s =>
    ⟨fun v => ⟨.unit, s.snd v⟩, funext fun _ => rfl,funext fun _ => rfl, ?_⟩
  simp [CommSq.cone]
  intro m hf hs
  funext i
  ext
  change (m ≫ Prod.snd) i = _
  rw [hs]

set_option pp.proofs true in
example {Y Z X : Type u}
    (f : Y → X)
    (g : Z → X)
    : (P : Type u) ×' (p : P → Y) ×' (q : P → Z) ×'
    IsPullback (C := Type u) p q f g := by
  refine ⟨{ x : Y × Z // f x.fst = g x.snd }, Prod.fst ∘ Subtype.val, Prod.snd ∘ Subtype.val, ?_⟩
  apply IsPullback.of_isLimit'
  case w =>
    exact .mk (funext fun ⟨_, h⟩ => h)
  refine PullbackCone.isLimitAux' _ fun s => 
    ⟨fun v => ⟨⟨s.fst v, s.snd v⟩, (funext_iff.mp s.condition v)⟩, ?_, ?_, ?_⟩
  · rfl
  · rfl
  intro m ha hb
  ext v
  simp at ha hb
  apply Subtype.ext
  simp
  ext
  · exact funext_iff.mp ha v
  · exact funext_iff.mp hb v

set_option pp.proofs true in
example
    [ht : HasTerminal 𝓒]
    [pb : ∀ {A B C : 𝓒}, ∀ f : A ⟶ B, ∀ g : C ⟶ B, HasPullback f g]
    (A B : 𝓒)
    : HasBinaryProduct A B := 
  IsBinaryProduct.hasBinaryProduct
    (pullback.fst (terminal.from A) (terminal.from B))
    (pullback.snd (terminal.from A) (terminal.from B))
  <| IsBinaryProduct.ofUniqueHom
    (fun f g => pullback.lift f g <| by simp)
    (fun f g => by rw [pullback.lift_fst])
    (fun f g => by rw [pullback.lift_snd])
    (fun f g m hf hg => by
      dsimp
      ext
      · rw [pullback.lift_fst, hf]
      · rw [pullback.lift_snd, hg])

def over_v {O : 𝓒} {a b : Over O} : (a ⟶ b) → (a.left ⟶ b.left) := by
  exact fun a_2 ↦ a_2.left

set_option pp.proofs true in
example
    [hOP : ∀ O : 𝓒, ∀ A B : Over O, HasBinaryProduct A B]
    (A B C : 𝓒) (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g := by
  have hbp := hOP C (.mk f) (.mk g)
  have := productIsBinaryProduct (p := hbp)
  generalize @prod.fst _ _ _ _ hbp = fst, @prod.snd _ _ _ _ hbp = snd at this
  apply IsPullback.hasPullback
  case fst => exact fst.left
  case snd => exact snd.left
  apply IsPullback.of_isLimit'
  case w =>
    refine { w := ?_ }
    change fst.left ≫ (Over.mk f).hom = snd.left ≫ (Over.mk g).hom
    rw [Over.w, Over.w]
  refine PullbackCone.isLimitAux' _ fun s => 
    ⟨?_, ?_, ?_, ?_⟩
  · change s.pt ⟶ (Over.mk f ⨯ Over.mk g).left
    refine CommaMorphism.left
      (this.lift (T := .mk (s.fst ≫ f))
        (Over.homMk s.fst rfl)
        (Over.homMk s.snd s.condition.symm))
  · simp only [id_eq, CommSq.cone_fst]
    rw [←Over.comp_left, this.lift_fst]
    simp only [Over.homMk_left]
  · simp only [id_eq, CommSq.cone_snd]
    rw [←Over.comp_left, this.lift_snd]
    simp only [Over.homMk_left]
  dsimp [CommSq.cone]
  intro m hf hs; rw! [←hs, ←hf];
  have hp : m ≫ (Over.mk f ⨯ Over.mk g).hom = s.fst ≫ f := sorry
  change (Over.homMk (show (Over.mk (s.fst ≫ f)).left ⟶ _ from m) hp).left = _
  congr 1
  · rw [hf]
  simp
  apply heq_of_cast_eq (by rw [hf])
  apply this.hom_ext
  <;> simp
  <;> apply Over.OverMorphism.ext 
  <;> simp only [Over.mk_left, Over.comp_left, Over.homMk_left]
  <;> change _ = cast rfl _
  · sorry
  · sorry

noncomputable def PullbackFunctor [HasPullbacks 𝓒] (f : Y ⟶ X) : Over X ⥤ Over Y where
  obj v := .mk <| pullback.fst f v.hom
  map v := Over.homMk
    <| pullback.map _ _ _ _ (𝟙 _) (over_v v) (𝟙 _) (by simp) (by simp [over_v])
  map_id v := by
    simp [over_v]
    rfl
  map_comp f g := by
    simp only [Functor.id_obj, over_v, Over.comp_left, ← Over.homMk_comp, Over.mk_left]
    congr 1
    rw [pullback.map_comp]
    simp

instance sm {X} : Monoid (Set X) where
  mul := Set.union
  mul_assoc := Set.union_assoc
  one := ∅
  one_mul := Set.empty_union
  mul_one := Set.union_empty

def SetMon : Type u ⥤ Sigma Monoid where
  obj X := ⟨Set X, sm ⟩
  map f := {
    toFun x := setOf fun i => (∃ v ∈ x, f v = i)
    map_one' := Set.ext fun x ↦ {
        mp := fun ⟨_, v, _⟩ => v
        mpr v := v.elim
      }
    map_mul' x y := Set.ext fun i ↦ {
      mp := by
        rintro ⟨w, h, rfl⟩
        apply (Set.mem_union _ _ _).mpr
        rcases (Set.mem_union _ _ _).mp h with (h|h)
        · exact .inl ⟨_, h, rfl⟩
        · exact .inr ⟨_, h, rfl⟩
      mpr h := by
        rcases (Set.mem_union _ _ _).mp h with (⟨w', h', rfl⟩|⟨_, h', rfl⟩)
        · exact ⟨_, (Set.mem_union _ _ _).mpr <| .inl h', rfl⟩
        · exact ⟨_, (Set.mem_union _ _ _).mpr <| .inr h', rfl⟩
    }
  }
  map_comp f g := MonoidHom.ext fun x => by simp [CategoryStruct.comp]

def maphom {A B} (f : A → B) : List A →* List B := {
  toFun := List.map f
  map_one' := rfl
  map_mul' := fun _ _ => List.map_append
}

def Free : Type u ⥤  Sigma Monoid where
  obj X := ⟨List X, inferInstance⟩
  map := maphom
  map_id v := MonoidHom.ext fun s => by simp [maphom, CategoryStruct.id]
  map_comp f g := MonoidHom.ext fun s => by simp [maphom, CategoryStruct.comp]

example : NatTrans Free SetMon where
  app X := {
    toFun l := setOf (· ∈ l)
    map_one' := Set.ext fun v => ⟨False.elim ∘ (List.mem_nil_iff _).mp, False.elim⟩
    map_mul' U V := by
      ext i
      change i ∈ U ++ V ↔ i ∈ {x | x ∈ U} ∪ {x | x ∈ V}
      simp
  }
  naturality X Y f := MonoidHom.ext fun x => by
    simp [CategoryStruct.comp, SetMon, Free, maphom]

section

variable {C D : Type u} [Category C] [Category D]

example
    (F G : C ⥤ D) (θ : NatTrans F G)
    : @IsIso _ Functor.category _ _ θ ↔ ∀ X, IsIso (θ.app X) where
  mp ii X := ⟨inv (I := ii) |>.app X, by simp⟩
  mpr ii := ⟨
    { app X := inv (I := ii X) },
    by
      ext x
      change θ.app x ≫ inv (θ.app x) = 𝟙 _
      rw [IsIso.hom_inv_id],
    by
      ext x
      change inv (θ.app x) ≫ θ.app x  = 𝟙 _
      rw [IsIso.inv_hom_id]
  ⟩

end

section

-- Skipping Ex5

def PP : Type ⥤ Type where
  obj X := { x : Set X // x.Nonempty }
  map f x := ⟨
    setOf (∃ v ∈ x.val, f v = ·),
    have ⟨i, v⟩ := x.prop
    ⟨f i, i, v, rfl⟩
  ⟩

/--
info: CategoryTheory.NatTrans.naturality.{v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂}
  [Category.{v₂, u₂} D] {F G : C ⥤ D} (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y) :
  F.map f ≫ self.app Y = self.app X ≫ G.map f
-/
#guard_msgs in
#check NatTrans.naturality

example
    (ch : ∀ X : Type, PP.obj X → X)
    /- (hch : ∀ X : Type, ∀ S : PP.obj X, ch X S ∈ S.val) -/
    (h : ⦃X Y : _⦄ → (f : X → Y) → ch Y ∘ PP.map f = f ∘ ch X ) : False := by
  specialize h Bool.not
  have tf : ch Bool _ = !ch Bool _ := funext_iff.mp h ⟨{.false, .true}, .true, by simp⟩
  have : PP.map not ⟨{false, true}, by simp⟩ = ⟨{.false, .true}, by simp⟩ := by simp [PP]
  rwa [this, Bool.eq_not_self] at tf

end

