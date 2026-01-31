import Mathlib.CategoryTheory.Monoidal.Closed.Types

open CategoryTheory

open scoped MonoidalCategory

section

universe u
variable {C : Type} [SmallCategory C]

def adjv (V : C ⥤ Type) : ((C ⥤ Type) × C) ⥤ Type where
  obj X := (coyoneda.obj (.op X.2) ⊗ V) ⟶ X.1
  map {X Y} f n := ((coyoneda.map (.op f.2)) ⊗ₘ (𝟙 _)) ≫ n ≫ f.1

axiom cant_be_bothered {V : C ⥤ Type} : MonoidalCategory.tensorLeft V ⊣ Functor.curry.obj (adjv V)

noncomputable instance : MonoidalClosed (C ⥤ Type) where
  closed V := {
    rightAdj := Functor.curry.obj <| adjv V
    adj := cant_be_bothered
  }

end

open Function (Embedding)

instance (priority := 10000) : Category Nat where
  Hom n m := Fin n ↪ Fin m
  id n := Embedding.refl _
  comp := Embedding.trans

variable (P : Nat ⥤ Type)

def N : Nat ⥤ Type where
  obj n := Fin n
  map := Embedding.toFun

section

noncomputable def inPre {m n : Nat} (f : Fin m ↪ Fin n) (i : Fin n) : Option (Fin m) :=
  (Finset.univ.filter (f · = i)).val.toList.head?

theorem inPre_filter_eq {m n : Nat} (f : Fin m ↪ Fin n) (i : Fin n)
    : Finset.univ.filter (f · = i) = if h : ∃ v, f v = i then {Classical.choose h} else {} := by
  split <;> rename_i heq
  · ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor <;> rintro rfl
    · exact (f.injective <| Classical.choose_spec heq).symm
    · exact Classical.choose_spec heq
  · ext n
    simp only [not_exists, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false] at heq ⊢
    apply heq

theorem inPre_eq {m n : Nat} (f : Fin m ↪ Fin n) (i : Fin n) : inPre f i
    = if h : ∃ v, f v = i then Option.some (Classical.choose h) else .none := by
  dsimp only [inPre]
  rw [inPre_filter_eq]
  split <;> simp

@[simp]
theorem inPre_refl {n : Nat} {i} : inPre (𝟙 n) i = .some i := by
  simp [inPre, CategoryStruct.id, Finset.filter_eq']

@[simp]
theorem inPre_succEmb {n : Nat} : inPre (Fin.succEmb n) 0 = none := by
  simp [inPre]

@[simp]
theorem inPre_iff {n m} {f : Fin n ↪ Fin m} {i v}
    : (inPre f i = some v) ↔ f v = i where
  mp h := by
    simp only [inPre_eq, Option.dite_none_right_eq_some, Option.some.injEq] at h
    rcases h with ⟨h,rfl⟩
    exact Classical.choose_spec h
  mpr := by
    rintro rfl
    simp [inPre, Finset.filter_eq']

@[simp]
theorem inPre_f {n m} {f : Fin n ↪ Fin m} {i} 
    : inPre f (f i) = .some i := by simp

@[simp]
theorem ninPre_iff {n m} {f : Fin n ↪ Fin m} {i}
    : (inPre f i = none) ↔ ∀ x, f x ≠ i where
  mp h i := by rintro rfl; simp at h
  mpr h := Option.eq_none_iff_forall_some_ne.mpr
    fun a h' => h a (inPre_iff.mp h'.symm)

@[simp]
theorem inPre_defn {n m} {f : Fin n ↪ Fin m} {i}
    : inPre f (f i) = .some i := by
  simp

@[simp]
theorem inPre_comp {n m k}
    {f : Fin n ↪ Fin m}
    {g : Fin m ↪ Fin k}
    {v : Fin _}
    : inPre (f.trans g) (g v) = inPre f v := by
  simp [inPre_eq]

end

def PSqO (n : Nat) : Type := (Fin n → P.obj n) × P.obj (n + 1)

noncomputable def extend {n m : Nat}
    (map : n ⟶ m)
    (v : Fin m)
    (h : inPre map v = none)
    : n + 1 ⟶ m where
  toFun := Fin.cases v map.toFun
  inj' {a b} h' := by
    rw [ninPre_iff] at h
    simp only [Embedding.toFun_eq_coe] at h'
    induction a using Fin.cases
    <;> induction b using Fin.cases
    <;> simp only [Fin.cases_zero, Fin.cases_succ] at h'
    · rfl
    · exact (h _ h'.symm).elim
    · exact (h _ h').elim
    · rw [EmbeddingLike.apply_eq_iff_eq] at h'
      subst h'
      rfl

noncomputable def objIso {P} {n : Nat} : PSqO P n ≃ (N ⟶[_] P).obj n where
  toFun pqsv := {
    app m prod := by
      change (n ⟶ m) ⊗ Fin m at prod
      change P.obj m
      exact match h : inPre prod.1 prod.2 with
      | .some v => P.map prod.fst <| pqsv.fst v
      | .none => P.map (extend prod.1 prod.2 h) pqsv.snd
    naturality m n' f := by
      dsimp [N]
      ext prod
      change (n ⟶ m) ⊗ Fin m at prod
      rcases prod with ⟨ol, or⟩
      dsimp [N]
      -- We split on the case inPre (ol ≫ f) (f or)
      split <;> rename_i heq
      <;> simp only [CategoryStruct.comp] at heq
      · simp only [inPre_comp, inPre_iff] at heq
        subst heq
        split <;> rename_i h
        <;> simp only [inPre_defn, reduceCtorEq, Option.some.injEq] at h
        subst h
        simp
      · rw [inPre_comp] at heq
        split
        <;> rename_i h'
        · have := heq.symm.trans h'
          contradiction
        change _ = (P.map _ ≫ P.map _) _
        rw [←P.map_comp]
        apply congr (congr rfl _) rfl
        change extend (ol ≫ f) _ _ = extend ol or _ ≫ f
        apply Embedding.ext
        intro i
        induction i using Fin.cases
        <;> simp [extend, CategoryStruct.comp]
  }
  invFun ntv := by
    change NatTrans (coyoneda.obj (Opposite.op n) ⊗ N) P at ntv
    change (Fin n → P.obj n) × P.obj (n + 1)
    constructor
    · exact fun i => ntv.app n ⟨𝟙 _, i⟩
    · apply ntv.app (n + 1)
      dsimp [N]
      refine ⟨Fin.succEmb _, 0⟩
  left_inv psqv := by
    dsimp
    apply Prod.ext
    · dsimp
      ext i
      split
      <;> rename_i heq
      <;> simp only [inPre_refl, reduceCtorEq, Option.some.injEq] at heq
      subst heq
      rw [P.map_id]
      rfl
    · dsimp
      split
      <;> rename_i heq
      <;> simp at heq
      conv =>
        rhs
        rw [←show _ = psqv.2 from funext_iff.mp (P.map_id _) psqv.2]
      apply congr (congr rfl _) rfl
      apply Embedding.ext
      rintro (_|i)
      <;> dsimp [extend]
      <;> rfl
  right_inv ntv := by
    apply NatTrans.ext
    funext m i
    change (n ⟶ m) ⊗ Fin m at i
    dsimp
    split
    <;> rename_i v heq
    · change (ntv.app n ≫ P.map i.1) _ = _
      rw [←ntv.naturality]
      dsimp [N]
      rw [Category.id_comp, inPre_iff.mp heq]
      rfl
    · change (ntv.app _ ≫ P.map _) _ = _
      rw [←ntv.naturality]
      dsimp [N]
      rfl

noncomputable def PSq : Nat ⥤  Type where
  obj := PSqO P
  map {X Y} f := objIso.invFun ∘ ((ihom N).obj P).map f ∘ objIso.toFun

variable {P}

noncomputable def iso : Iso (PSq P) (N ⟶[_] P) where
  hom := {
    app m := objIso.toFun
    naturality X Y f := by
      change (objIso ∘ objIso.symm) ∘ ((ihom N).obj P).map f ∘ objIso 
        = ((ihom N).obj P).map f ∘ objIso
      rw [Equiv.self_comp_symm]
      rfl
  }
  inv := {
    app n := objIso.invFun
    naturality X Y f := by
      change _ = objIso.symm ∘ _ ∘ objIso ∘ objIso.symm
      rw [Equiv.self_comp_symm]
      rfl
  }

noncomputable def app : N ⊗ PSq P ⟶ P := (𝟙 _ ⊗ₘ iso.hom) ≫ MonoidalClosed.uncurry (𝟙 (N ⟶[_] P))

