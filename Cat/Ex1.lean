import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Cat.L1

open CategoryTheory

namespace Exs

universe u

variable {A B C X Y Z U V W M G : Type u}

namespace Sets

theorem ex2.a (f : Z → X) (g : Z → Y)
    : ∃! fg : Z → X × Y,
    f = Prod.fst ∘ fg ∧ g = Prod.snd ∘ fg :=
  ⟨fun x => ⟨f x, g x⟩, ⟨rfl, rfl⟩, fun fg ⟨hl, hr⟩ =>
    funext fun y => by
      ext
      · rw [hl]
        rfl
      · rw [hr]
        rfl⟩

def pcomp (f : A → X) (g : B → Y) : A × B → X × Y
  | ⟨a, b⟩ => ⟨f a, g b⟩

theorem ex2.b₁ : pcomp (@id A) (@id B) = id := funext fun _ => rfl
theorem ex2.b₂ {p : A → X} {q : B → Y} {f : X → U} {g : Y → V}
    : pcomp f g ∘ pcomp p q = pcomp (f ∘ p) (g ∘ q) :=
  funext fun v ↦ rfl

theorem ex3.a (f : X → Z) (g : Y → Z)
    : ∃! fg : X ⊕ Y → Z,
    f = fg ∘ .inl ∧ g = fg ∘ .inr :=
  ⟨fun | .inl x => f x | .inr x => g x, ⟨rfl, rfl⟩,
    fun fg ⟨hl, hr⟩ =>
    funext fun 
      | .inl x => by rw [hl]; rfl
      | .inr x => by rw [hr]; rfl⟩

def qcomp (f : A → X) (g : B → Y) : A ⊕ B → X ⊕ Y
  | .inl x => .inl <| f x
  | .inr x => .inr <| g x

theorem ex3.b₁ : qcomp (@id A) (@id B) = id := funext fun 
  | .inl _ => rfl
  | .inr _ => rfl

theorem ex3.b₂ {p : A → X} {q : B → Y} {f : X → U} {g : Y → V}
    : qcomp f g ∘ qcomp p q = qcomp (f ∘ p) (g ∘ q) :=
  funext fun
    | .inl _ => rfl
    | .inr _ => rfl

theorem ex3 : Fin 2 ≃ Fin 3 → False
  | ⟨toFun, invFun, ht, hi⟩ =>
    have hinj : Function.Injective toFun := by exact?
    have hsur : Function.Surjective toFun := by exact?
  
    match h₁: toFun 0, h₂: toFun 1 with
    | 0, 0 
    | 1, 1 
    | 2, 2 =>
      have := hinj (h₁.trans h₂.symm)
      by contradiction
    | 1, 0 
    | 0, 1 =>
      have ⟨v, hb⟩ := hsur 2
      match v with
      | 0 =>
        have := hb.symm.trans h₁
        by contradiction
      | 1 =>
        have := hb.symm.trans h₂
        by contradiction
    | 2, 0 
    | 0, 2 => 
      have ⟨v, hb⟩ := hsur 1
      match v with
      | 0 =>
        have := hb.symm.trans h₁
        by contradiction
      | 1 =>
        have := hb.symm.trans h₂
        by contradiction
    | 2, 1 
    | 1, 2 =>
      have ⟨v, hb⟩ := hsur 0
      match v with
      | 0 =>
        have := hb.symm.trans h₁
        by contradiction
      | 1 =>
        have := hb.symm.trans h₂
        by contradiction

-- They are both countable and infinite, that mean they must satisfy this:
def ex4b : ℚ ≃ ℤ :=
  have ratNat : ℚ ≃ ℕ := Denumerable.eqv _
  have intNat : ℤ ≃ ℕ := Equiv.intEquivNat

  ratNat.trans intNat.symm

-- For ex5 it simply follows the algebraic laws one might expect.

def Monomorphism (f : X → Y) := ∀ {Z : Type u}, ∀ g h : Z → X, f ∘ g = f ∘ h → g = h

theorem ex6 {f : X → Y}
    : Function.Injective f ↔ Monomorphism f := ⟨
  fun h _ _ _ heq => funext (h <| funext_iff.mp heq ·),
  fun h x y heq =>
    funext_iff.mp ((h (fun | PUnit.unit => x) (fun _ => y)) (funext fun | .unit => heq)) .unit,
⟩

def Epimorphism (f : X → Y) := ∀ {Z : Type u}, ∀ g h : Y → Z , g ∘ f = h ∘ f → g = h

theorem ex7 {f : X → Y}
    : Function.Surjective f ↔ Epimorphism f := ⟨
  fun h Z g' h' heq => by
    refine funext fun v => ?_
    obtain ⟨w, rfl⟩ := h v
    exact funext_iff.mp heq w,
  fun h v => by
    /- have := h (fun _ => v) (fun _ => v) -/
    dsimp [Epimorphism] at h
    have hContra : ∀ {Z : Type u} (g h : Y → Z), g ≠ h → g ∘ f ≠ h ∘ f :=
      fun g₁ g₂ h₁ h₂ => h₁ (h g₁ g₂ h₂)
    haveI : DecidableEq X := Classical.typeDecidableEq X
    haveI : DecidableEq Y := Classical.typeDecidableEq Y
    let atV (z : Bool) : Y → ULift.{u, 0} Bool := (if · = v then .up z else .up .false)
    have hneq := hContra
      (atV .true)
      (atV .false)
      (have := funext_iff.mp · v; by simp [atV] at this)
    have ⟨w, h⟩ := Function.ne_iff.mp hneq
    dsimp at hneq
    use w
    dsimp [Function.comp_apply, atV] at h
    rw [ite_self, ite_eq_right_iff, ULift.up.injEq, Bool.true_eq_false,
        imp_false, Decidable.not_not] at h
    exact h
⟩

end Sets

variable [Monoid M]

namespace Monoid

variable [Monoid X] [Monoid Y] [Monoid Z]
in
section

instance : Monoid (X × Y) where
  one := ⟨1, 1⟩
  mul := fun ⟨a₁, b₁⟩ ⟨a₂,b₂⟩ => ⟨a₁ * a₂, b₁ * b₂⟩
  mul_one := fun ⟨a, b⟩ => by change Prod.mk (a * 1) (b * 1) = _; simp
  one_mul := fun ⟨a, b⟩ => by change Prod.mk (1 * a) (1 * b) = _; simp
  mul_assoc := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ => by
    change Prod.mk _ _ = Prod.mk _ _
    repeat rw [←Semigroup.mul_assoc]

def fsthom : X × Y →* X := {
  toFun := Prod.fst
  map_one' := rfl
  map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl
}
def sndhom : X × Y →* Y := {
  toFun := Prod.snd
  map_one' := rfl
  map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl
}

theorem ex1 (f : Z →* X) (g : Z →* Y)
    : ∃! fg : Z →* X × Y,
    f = fsthom.comp fg ∧ g = sndhom.comp fg := ⟨
  {
    toFun := fun z => ⟨f z, g z⟩
    map_one' := by simp [MonoidHom.map_one]
    map_mul' x y := by simp [MonoidHom.map_mul]
  },
  ⟨rfl, rfl⟩,
  fun x ⟨hl, hr⟩ => by
    rw [hl, hr]
    rfl
⟩

instance : Monoid (List X) where
  one := []
  mul := List.append

  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

def maphom (f : A → B) : List A →* List B := {
  toFun := List.map f
  map_one' := rfl
  map_mul' := fun _ _ => List.map_append
}

def monfold.d : List X → X
  | [] => 1
  | hd :: tl => hd * d tl
def monfold : List X →* X := {
  toFun := monfold.d,
  map_one' := rfl
  map_mul' := fun x y => by
    induction x
    · change monfold.d y = 1 * _
      rw [Monoid.one_mul]
    case cons hd tl ih =>
      change _ * monfold.d (tl * y) = _ * _ * _
      rw [ih]
      group
}

def sumfold (f : List X →* M) (g : List Y →* M) : List (X ⊕ Y) →* M :=
  monfold.comp (maphom (fun | .inl x => f [x] | .inr x => g [x]))
end

theorem ex2
      (f : List X →* M) (g : List Y →* M)
    : ∃! fg : List (X ⊕ Y) →* M,
    f = fg.comp (maphom .inl) ∧ g = fg.comp (maphom .inr) := ⟨
    sumfold f g,
    by
      constructor
      all_goals ext ls
      · induction ls
        · dsimp [maphom, sumfold]
          exact f.map_one
        case cons hd tl ih =>
          dsimp [] at ih
          change f ([hd] * tl) = f [hd] * (sumfold f g) ((maphom Sum.inl) tl)
          rw [MonoidHom.map_mul, ←ih]
      · induction ls
        · dsimp [maphom, sumfold]
          exact g.map_one
        case cons ih hd tl ih =>
          dsimp [] at ih
          change g ([hd] * tl) = g [hd] * (sumfold f g) ((maphom Sum.inr) tl)
          rw [MonoidHom.map_mul, ←ih],
    fun fn ⟨hl, hr⟩ => by
      ext l
      induction l
      · change fn 1 = 1
        rw [MonoidHom.map_one]
      case cons hd tl ih =>
        change fn ([_] * _) = _ * (sumfold f g) tl
        rw [MonoidHom.map_mul, ←ih, hl, hr]
        cases hd <;> rfl
⟩

end Monoid

namespace Group

variable [Group G]

theorem ex1.a {g : G} : ∃! one, g * one = g ∧ one * g = g :=
  ⟨1, ⟨mul_one g, one_mul g⟩, fun one ⟨hl, hr⟩ => calc
    one = 1 * one       := by group
    _ = (g⁻¹ * g) * one := by group
    _ = g⁻¹ * (g * one) := by group
    _ = g⁻¹ * g         := by rw [hl]
    _ = 1               := by group⟩

theorem ex1.b : ∃! op : G → G, ∀ g : G, op g * g = 1 ∧ g * op g = 1 := 
  ⟨
    Inv.inv,
    fun g => ⟨inv_mul_cancel g, mul_inv_cancel g⟩,
    fun inv univ => funext fun g => calc
      _ = 1 * inv g         := right_eq_mul.mpr rfl
      _ = g⁻¹ * g * inv g   := by rw [@Group.inv_mul_cancel]
      _ = g⁻¹ * (g * inv g) := mul_assoc g⁻¹ g (inv g)
      _ = g⁻¹ * 1           := by rw [(univ g).2]
      _ = g⁻¹               := MulOneClass.mul_one g⁻¹
  ⟩

theorem ex2 : (Inv.inv ∘ Inv.inv) = (id : G → G) := funext fun g => calc
  (g⁻¹)⁻¹ = 1 * (g⁻¹)⁻¹   := (one_mul g⁻¹⁻¹).symm
  _ = (g * g⁻¹) * (g⁻¹)⁻¹ := by rw [@mul_inv_cancel]
  _ = g * (g⁻¹ * (g⁻¹)⁻¹) := mul_assoc g g⁻¹ g⁻¹⁻¹
  _ = g * 1               := by rw [@mul_inv_cancel]
  _ = g                   := MulOneClass.mul_one g

theorem ex3.a1 {x y : G} (heq : x * y = 1) : y = x⁻¹ := calc
  _ = 1 * y         := right_eq_mul.mpr rfl
  _ = (x⁻¹ * x) * y := by rw [Group.inv_mul_cancel]
  _ = x⁻¹ * (x * y) := mul_assoc x⁻¹ x y
  _ = x⁻¹ * 1       := by rw [heq]
  _ = x⁻¹           := MulOneClass.mul_one x⁻¹

theorem ex3.a2 {x y : G} (heq : x * y = 1) : x = y⁻¹ := calc
  _ = x * 1           := (MulOneClass.mul_one x).symm
  _ = x * (y * y⁻¹ )  := by rw [@mul_inv_cancel]
  _ = (x * y) * y⁻¹   := (mul_assoc x y y⁻¹).symm
  _ = 1 * y⁻¹         := by rw [heq]
  _ = y⁻¹             := one_mul y⁻¹

theorem ex3.b : (1 : G) = 1⁻¹ := calc
  _ = 1 * (1 : G)⁻¹ := (mul_inv_cancel 1).symm
  _ = (1 : G)⁻¹     := by rw [one_mul]

theorem ex3.c {x y : G} : (x * y)⁻¹ = y⁻¹ * x⁻¹  := calc
  _ = 1 * (x * y)⁻¹                       := Eq.symm (one_mul (x * y)⁻¹)
  _ = (y⁻¹ * y) * (x * y)⁻¹               := by rw [@Group.inv_mul_cancel]
  _ = (y⁻¹ * (1 * y)) * (x * y)⁻¹         := by rw [@MulOneClass.one_mul]
  _ = (y⁻¹ * ((x⁻¹ * x) * y)) * (x * y)⁻¹ := by rw [@Group.inv_mul_cancel]
  _ = y⁻¹ * (x⁻¹ * x) * y * (x * y)⁻¹     := by rw [← @Semigroup.mul_assoc]
  _ = y⁻¹ * x⁻¹ * x * y * (x * y)⁻¹       := by rw [← @Semigroup.mul_assoc]
  _ = y⁻¹ * x⁻¹ * ((x * y) * (x * y)⁻¹)   := by group
  _ = (y⁻¹ * x⁻¹) * 1                     := by rw [@mul_inv_cancel]
  _ = y⁻¹ * x⁻¹                           := MulOneClass.mul_one (y⁻¹ * x⁻¹)

end Group

namespace univ

theorem ex1 
    {FX : Type _} [Monoid FX]
    (φ : X → FX)
    (f g : FX →* M)
    : f = g ↔ f ∘ φ = g ∘ φ := ⟨
  fun x => x ▸ rfl,
  sorry,
⟩

open Exs.Monoid

-- Ex2.a is solved in L3.lean

theorem ex2.bi : maphom id = MonoidHom.id (List X) := MonoidHom.ext fun x => by
  induction x
  · rfl
  case cons ih =>
    change _ :: (maphom id) _ = _ :: _
    rw [ih]
    rfl

theorem ex2.bii {f : A → B} {g : B → C}
    : maphom (g ∘ f) = (maphom g).comp (maphom f) :=
    MonoidHom.ext fun x => by
  induction x
  · rfl
  case cons hd tl ih =>
    change (g ∘ f) _  :: (maphom _ _) = (g ∘ f) _ :: ((maphom _).comp (maphom _)) _
    rw [←ih]

def s : A → List A := ([·])

example : List.flatten ∘ s = (id : List A → List A) := funext fun v => by
  dsimp [s]
  rw [List.append_nil]


theorem ex2.ci : List.flatten ∘ List.map s = (id : List A → List A) := funext fun v => by
  dsimp
  induction v
  · rfl
  case cons hd tl ih =>
    change hd :: (List.map s tl).flatten = hd :: tl
    rw [ih]

theorem ex2.cii
    : List.flatten ∘ List.map List.flatten 
    = (List.flatten ∘ List.flatten : List (List (List A)) → _) := funext fun v => by
  dsimp
  induction v
  · rfl
  case cons hd tl ih =>
    change _ ++ _ = (hd ++ tl.flatten).flatten
    rw [List.flatten_append, ←ih]

structure PType where (T : Type u) (t : T)

structure PType.Hom (a b : PType) where
  f : a.T → b.T
  h : f a.t = b.t

@[ext]
theorem PType.Hom.ext {A B} {a b : PType.Hom A B} (f : a.f = b.f) : a = b :=
  match a, b with
  | ⟨_, _⟩, ⟨_, _⟩ => (PType.Hom.mk.injEq _ _ _ _).mpr f

instance catPType : Category PType where
  Hom := PType.Hom
  id := fun x => ⟨id, rfl⟩
  comp := fun {X Y Z} ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g ∘ f, calc
    g (f _) = g Y.t := by rw [hf]
    _ = _ := hg⟩

def P (S : Type u) : PType := ⟨Option S, .none⟩

theorem ex3 {S : Type u} {X : PType} (f : S → X.T)
    : ∃! fs : PType.Hom (P S) X, fs.f ∘ Option.some = f := ⟨
  ⟨fun | .none => X.t | .some v => f v, rfl⟩,
  rfl,
  fun y eq => PType.Hom.ext <|
    funext (fun
      | .none => y.h
      | .some v => by apply congr eq (.refl v))
⟩

def ex4.F (X : PType) : Type _ := PType.Hom X X
instance {X : PType} : Monoid (ex4.F X) where
  one := catPType.id X
  mul := catPType.comp
  mul_one := catPType.id_comp
  one_mul := catPType.comp_id
  mul_assoc := catPType.assoc

def ex4.φx {X : PType} : PType.Hom X ⟨F X, catPType.id X⟩ where
  f _ := ⟨id, rfl⟩
  h := rfl

theorem ex4.b {X} (M : Type u) [mm : Monoid M]
    (f : PType.Hom X ⟨M, mm.one⟩)
    : ∃! fs : F X →* M, fs ∘ φx.f = f.f :=
  ⟨
    {
      toFun v := (f.f ∘ v.f) X.t
      map_one' := by
        dsimp
        rw [PType.Hom.h, PType.Hom.h]
        rfl
      map_mul' x y := by 
        dsimp
        simp [PType.Hom.h]
        exact (Monoid.one_mul _).symm
    },
    funext fun v => by
      dsimp
      simp [PType.Hom.h]
      sorry
      ,
    sorry,
  ⟩

end univ

namespace cat

variable {𝓒 : Type u} [Category 𝓒] {X Y Z : 𝓒}

theorem ex1
    {f : X ⟶ Y} {g h : Y ⟶ X}
    (ha : f ≫ g = 𝟙 X)
    (hb : h ≫ f = 𝟙 Y)
    : g = h := calc
  g = 𝟙 Y ≫ g     := Eq.symm (Category.id_comp g)
  _ = (h ≫ f) ≫ g := by rw [hb]
  _ = h ≫ (f ≫ g) := Category.assoc h f g
  _ = h ≫ 𝟙 _     := by rw [ha]
  _ = h           := Category.comp_id h

def Mono (f : X ⟶ Y) : Prop :=
    ∀ {Z : 𝓒} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h

def SplitMono (f : X ⟶ Y) : Prop :=
  ∃ f' : Y ⟶ X, f ≫ f' = 𝟙 X

theorem ex2.a {f : X ⟶ Y} : SplitMono f → Mono f :=
  fun ⟨f', hff'⟩ {Z} g h hgf => calc
    _ = g ≫ 𝟙 X       := (Category.comp_id g).symm
    _ = g ≫ (f ≫ f')  := by rw [hff']
    _ = (g ≫ f) ≫ f'  := (Category.assoc _ _ _).symm
    _ = (h ≫ f) ≫ f'  := by rw [hgf]
    _ = h ≫ (f ≫ f')  := (Category.assoc _ _ _)
    _ = h ≫ 𝟙 _       := by rw [hff']
    _ = h             := Category.comp_id h

theorem ex2.b {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) :=
  fun {_} h₁ h₂ hhh =>
    hf h₁ h₂ <| hg (h₁ ≫ f) (h₂ ≫ f) <| calc
      (h₁ ≫ f) ≫ g
        = h₁ ≫ f ≫ g    := Category.assoc _ _ _
      _ = h₂ ≫ f ≫ g    := hhh
      _ = (h₂ ≫ f) ≫ g  := (Category.assoc _ _ _).symm

theorem ex2.c {f : X ⟶ Y} {g : Y ⟶ Z}
    (hgf : Mono (f ≫ g))
    : Mono f :=
  fun {Z} h₁ h₂ hhh =>
    hgf _ _ <| calc
      h₁ ≫ f ≫ g
        = (h₁ ≫ f) ≫ g  := (Category.assoc h₁ f g).symm
      _ = (h₂ ≫ f) ≫ g  := by rw [hhh]
      _ = h₂ ≫ f ≫ g    := Category.assoc h₂ f g

theorem ex2.d
    (hf : ∀ (X Y : Type u) (f : X ⟶ Y), Mono f → SplitMono f)
    : False :=
  have ⟨inv, _⟩ := hf PEmpty PUnit PEmpty.elim (Sets.ex6.mp fun x => x.elim)
  (inv .unit).elim

theorem ex2.e 
    (f : Fin 2 ⟶ Fin 3)
    (h : SplitMono f)
    : ∃ a b : Fin 3 → Fin 2, a ∘ f = id ∧ b ∘ f = id ∧ a ≠ b :=
  have hNeq : f 0 ≠ f 1 := fun h' => absurd
    ((Sets.ex6.mpr <| ex2.a h) h')
    (by decide)
  match h0 : f 0, h1 : f 1 with
  | 0, 0 | 1, 1 | 2, 2 => by simp_all

  | x@0, y@1 | x@0, y@2
  | x@1, y@0 | x@1, y@2
  | x@2, y@0 | x@2, y@1 =>
    ⟨
      fun v => if v = x then 0 else if v = y then 1 else 0,
      fun v => if v = x then 0 else if v = y then 1 else 1,
      funext fun | 0 | 1 => (by simp_all),
      funext fun | 0 | 1 => (by simp_all),
      fun h =>
        have h0 := funext_iff.mp h 0
        have h1 := funext_iff.mp h 1
        have h2 := funext_iff.mp h 2
        by simp_all
    ⟩

def Epi (f : X ⟶ Y) : Prop :=
    ∀ {Z : 𝓒} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h

def SplitEpi (f : X ⟶ Y) : Prop :=
  ∃ f' : Y ⟶ X, f' ≫ f = 𝟙 Y

theorem ex3.a {f : X ⟶ Y} : SplitEpi f → Epi f :=
  fun ⟨f', hff⟩ {Z} g h hgh => calc
    g = 𝟙 Y ≫ g       := (Category.id_comp g).symm
    _ = (f' ≫ f) ≫ g  := by rw [hff]
    _ = f' ≫ (f ≫ g)  := Category.assoc _ _ _
    _ = f' ≫ (f ≫ h)  := by rw [hgh]
    _ = (f' ≫ f) ≫ h  := Category.assoc _ _ _ |>.symm
    _ = 𝟙 Y ≫ h       := by rw [hff]
    _ = h             := Category.id_comp h

theorem ex3.b {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) :=
  fun {_} h₁ h₂ hhh =>
    hg h₁ h₂ <| hf _ _ <| calc
      f ≫ g ≫ h₁
        = (f ≫ g) ≫ h₁ := (Category.assoc _ _ _).symm
      _ = (f ≫ g) ≫ h₂ := hhh
      _ = f ≫ g ≫ h₂   := (Category.assoc _ _ _)

theorem ex3.c {f : X ⟶ Y} {g : Y ⟶ Z}
    (hgf : Epi (f ≫ g))
    : Epi g :=
  fun {U} h₁ h₂ hhh => hgf _ _ <| calc
    (f ≫ g) ≫ h₁
      = f ≫ (g ≫ h₁)  := Category.assoc f g h₁
    _ = f ≫ (g ≫ h₂)  := by rw [hhh]
    _ = (f ≫ g) ≫ h₂  := (Category.assoc f g h₂).symm

theorem ex3.d
    (X Y : Type u) (f : X ⟶ Y)
    (hf : Epi f)
    : SplitEpi f :=
  ⟨ (Classical.choose <| Sets.ex7.mpr hf ·),
    funext (Classical.choose_spec <| Sets.ex7.mpr hf ·) ⟩

theorem ex3.e 
    (f : Fin 3 ⟶ Fin 2)
    (h : SplitEpi f)
    : ∃ a b : _ → Fin 3, f ∘ a = id ∧ f ∘ b = id ∧ a ≠ b := by
  have ⟨inv, (hinv : _ ∘ _ = id)⟩ := h
  have hs := Sets.ex7.mpr (ex3.a h)
  dsimp [Function.Surjective] at hs
  use inv
  sorry

  /- match h0 : f 0, h1 : f 1, h2 : f 2 with -/
  /- | 0, 0, 0 | 1, 1, 1 => by -/
  /-   all_goals obtain ⟨(_|_|_), h1'⟩ := hs 0 -/
  /-   all_goals obtain ⟨(_|_|_), h2'⟩ := hs 1 -/
  /-   <;> exfalso -/
  /-   <;> simp [h1', h2'] at h0 h1 h2 -/
  /-    -/
  /-  -/
  /- | _, _, _ => -/
  /-   ⟨ -/
  /-     fun v => if v = x then 0 else if v = y then 1 else 0, -/
  /-     fun v => if v = x then 0 else if v = y then 1 else 1, -/
  /-     funext fun | 0 | 1 => (by simp_all), -/
  /-     funext fun | 0 | 1 => (by simp_all), -/
  /-     fun h => -/
  /-       have h0 := funext_iff.mp h 0 -/
  /-       have h1 := funext_iff.mp h 1 -/
  /-       have h2 := funext_iff.mp h 2 -/
  /-       by simp_all -/
  /-   ⟩ -/

end cat

namespace iso

instance mat : Category Nat where
  Hom a b := Matrix (Fin a) (Fin b) ℝ
  comp    := (· * ·)
  id n    := 1
  assoc   := Matrix.mul_assoc

def ex1 {a : Nat} (m : Matrix (Fin a) (Fin a) ℝ) [x : Invertible m]
    : a ≅ a where
  hom := m
  inv := ⅟m
  hom_inv_id := by
    change _ * _ = _
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.mul_inv_of_invertible m]
    rfl
  inv_hom_id := by
    change _ * _ = _
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_mul_of_invertible m]
    rfl

-- No, if two objects have different dimentions you cannot construct an isomorphism between them.

variable {𝓒 : Type u} [Category 𝓒] {X Y Z : 𝓒}

def ex2.a (f : X ≅ Y) (g : Y ≅ Z) : X ≅ Z where
  hom := f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  hom_inv_id := (calc
    (f.hom ≫ g.hom) ≫ g.inv ≫ f.inv
      = ((f.hom ≫ g.hom) ≫ g.inv) ≫ f.inv := (Category.assoc _ _ _).symm
    _ = (f.hom ≫ (g.hom ≫ g.inv)) ≫ f.inv := by rw [(Category.assoc _ _ _).symm]
    _ = (f.hom ≫ 𝟙 Y) ≫ f.inv             := by rw [Iso.hom_inv_id]
    _ = f.hom ≫ f.inv                     := by rw [Category.comp_id]
    _ = 𝟙 X                               := by rw [Iso.comp_inv_eq_id])
  inv_hom_id := (calc
    (g.inv ≫ f.inv) ≫ f.hom ≫ g.hom 
      = ((g.inv ≫ f.inv) ≫ f.hom) ≫ g.hom := (Category.assoc _ _ _).symm
    _ = (g.inv ≫ (f.inv ≫ f.hom)) ≫ g.hom := by rw [(Category.assoc _ _ _).symm]
    _ = (g.inv ≫ 𝟙 Y) ≫ g.hom             := by rw [@Iso.inv_hom_id]
    _ = g.inv ≫ g.hom                     := by rw [@Category.comp_id]
    _ = 𝟙 Z                               := g.inv_hom_id)

def ex2.b (f : X ≅ Y) (g : Y ⟶ Z) (gf : X ≅ Z) (hFGgf : f.hom ≫ g = gf.hom)
    : Y ≅ Z where
  hom := g
  inv := gf.inv ≫ f.hom
  inv_hom_id := (calc
    (gf.inv ≫ f.hom) ≫ g
      = gf.inv ≫ (f.hom ≫ g)  :=  Category.assoc gf.inv f.hom g
    _ = gf.inv ≫ gf.hom       := by rw [hFGgf]
    _ = 𝟙 Z                   := gf.inv_hom_id)

  hom_inv_id := (calc 
    g ≫ gf.inv ≫ f.hom
      = 𝟙 Y ≫ g ≫ gf.inv ≫ f.hom := by rw [@Category.id_comp]
    _ = (f.inv ≫ f.hom) ≫ g ≫ gf.inv ≫ f.hom    := by rw [Iso.inv_hom_id]

    _ = ((f.inv ≫ f.hom) ≫ g) ≫ gf.inv ≫ f.hom  := (Category.assoc _ _ _).symm
    _ = (f.inv ≫ (f.hom ≫ g)) ≫ gf.inv ≫ f.hom  := by rw [←(Category.assoc f.inv _ _)]

    _ = (f.inv ≫ gf.hom) ≫ gf.inv ≫ f.hom       := by rw [hFGgf]

    _ = f.inv ≫ gf.hom ≫ gf.inv ≫ f.hom         := (Category.assoc _ _ _)
    _ = f.inv ≫ (gf.hom ≫ gf.inv) ≫ f.hom       := by rw [Category.assoc]

    _ = f.inv ≫ 𝟙 _ ≫ f.hom                     := by rw [Iso.hom_inv_id]
    _ = f.inv ≫ f.hom                           := by rw [@Category.id_comp]
    _ = 𝟙 Y                                     := f.inv_hom_id)

theorem ex2.c (gf : Unit ≅ Unit) (f : Unit ⟶ Bool) (g : Bool ⟶ Unit)
    (_hEq : gf.hom = f ≫ g)
    : ¬∃ iso : Unit ≅ Bool, f = iso.hom := by
  rintro ⟨⟨toF, invF, h₁, h₂⟩, rfl⟩
  have : ∀ b, f _ = b := funext_iff.mp h₂
  match h : f .unit with
  | .true   => exact Bool.noConfusion ((this .false).symm.trans h)
  | .false  => exact Bool.noConfusion ((this .true).symm.trans h)

theorem ex3 {T : Type u} [ipo : PartialOrder T] {x y : T}
    (hNeq : x ≠ y)
    (f : poset.Hom x y)
    : cat.Epi f ∧ cat.Mono f ∧ ¬IsIso f :=
  ⟨
    fun ⟨f⟩ ⟨g⟩ _ => (PLift.up.injEq f g).mpr rfl,
    fun ⟨f⟩ ⟨g⟩ _ => (PLift.up.injEq f g).mpr rfl,
    fun ⟨⟨f'⟩, _, _⟩ =>
      hNeq (ipo.le_antisymm _ _ f.down f')
  ⟩

end iso

end Exs

