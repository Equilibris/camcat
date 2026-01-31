import Cat.Exam.Q4
import Cat.Pullback
import Mathlib.Data.Fin.Pigeonhole

open CategoryTheory

def lam (l m : Nat) : l ⟶ (l + m) := Fin.castAddEmb m
def rho (m n : Nat) : n ⟶ (m + n) := Fin.natAddEmb m

def prop : ObjectProperty (Nat ⥤ Type) := fun S => ∀ l m n : Nat,
  IsPullback
    (S.map (lam m n))
    (S.map (rho l m))
    (S.map (rho l _ ≫ eqToHom ((Nat.add_assoc _ _ _).symm)))
    (S.map (lam _ n))

-- Since this is the right adjoint of a forgetful functor,
-- I belive this must be a free functor of some form.

-- Found this paper too https://www.cl.cam.ac.uk/~mpf23/papers/PreSheaves/CT2004.pdf
-- also https://www.cl.cam.ac.uk/~mpf23/papers/PreSheaves/cf.pdf
-- also https://alexhkurz.github.io/papers/domains9.pdf

variable (S : Nat ⥤ Type)

def rel (n : Nat) (a b : (m : Nat) × S.obj (n + m)) : Prop :=
  ∃ k, ∃ p : k ≥ a.1 ∧ k ≥ b.1,
    (S.map (lam _ (k - a.1) ≫ eqToHom (by omega)) a.2 : S.obj (n+k)) =
    (S.map (lam _ (k - b.1) ≫ eqToHom (by omega)) b.2 : S.obj (n+k))

instance quot (n) : Setoid ((m : Nat) × S.obj (n + m)) where
  r := rel S n
  iseqv := {
    refl := fun ⟨m, x⟩ => ⟨m + m, (by simp), rfl⟩
    symm := fun ⟨k, ⟨p1, p2⟩, h⟩ => ⟨k, ⟨p2, p1⟩, h.symm⟩
    trans a b := sorry
  }

def extendf {n m k} (f : Fin n ↪ Fin m) : Fin (n + k) ↪ Fin (m + k) where
  toFun v :=
    if h : v < n then
      (f.toFun ⟨_, h⟩).castAdd _
    else
      have : n ≤ m := Fin.le_of_embedding f
      (v.addNat (m - n)).cast (by omega)
  inj' a b h := by
    simp at h
    split at h
    <;> split at h
    <;> simp [Fin.ext_iff] at h
    any_goals omega
    simpa [Fin.val_inj] using h

@[simp]
theorem extendf_glue {n m} (f : Fin n ↪ Fin m) : (extendf (k := 0) f) = f := by 
  simp [extendf]
/- def extendf_lam {n m k} : (extendf (k := k) (lam m n)) = sorry := sorry -/
/-  -/
/- #exit -/

def adj : (Nat ⥤ Type) ⥤  prop.FullSubcategory where
  obj S := {
    obj := {
      obj n := Quotient (quot S n)
      map f := Quotient.lift
        (fun ⟨m, x⟩ => .mk _ ⟨m, S.map (extendf f) x⟩)
        fun a b ⟨m, p, h⟩ =>
          Quot.sound ⟨m, p, by
            dsimp at h ⊢
            change (S.map _ ≫ S.map _) _ = (S.map _ ≫ S.map _) _
            rw [← S.map_comp, ← S.map_comp]
            sorry⟩
      map_id := sorry
      map_comp := sorry
    }
    property l m n := pullbackSet.mpr <| by
      simp only
      stop
      simp
      constructor
      · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ rfl h'
        simp at h' ⊢
        sorry
      · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ rfl h
        simp at h
        /- rcases  -/
        sorry
  }
  /- obj S := { -/
  /-   obj := { -/
  /-     obj v := S.obj v × Finset (Fin v) -/
  /-     map f v := ⟨S.map f v.1, v.2.map f⟩ -/
  /-   } -/
  /-   property l m n := pullbackSet.mpr <| by -/
  /-     dsimp -/
  /-     constructor -/
  /-     · intro p p' h h' -/
  /-       simp at h h' -/
  /-       sorry -/
  /-     · intro a b h -/
  /-       simp at h -/
  /-       sorry -/
  /- } -/
  map {X Y} f := {
    hom := {
      app n := Quotient.lift
        (fun ⟨m, x⟩ => .mk _ ⟨m, f.app _ x⟩)
        sorry
      naturality := sorry
    }
  }
  map_id := sorry
  map_comp := sorry


example : adj ⊣ prop.ι where
  unit := {
    app X := {
      app n x := .mk _ ⟨0, x⟩
      naturality X Y f := by
        ext o
        simp [adj]
    }
  }
  counit := {
    app X := {
      hom := {
        app n := Quotient.lift
          (fun v => by 
            dsimp at v ⊢
            have := v.2
            sorry)
          sorry
      }
    }
  }


