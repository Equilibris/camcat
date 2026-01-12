# Topic to be covered in the exam

## Categories (confident)

### Practice Questions

1. **Basic Composition**: Given morphisms f : A → B, g : B → C, h : C → D in category 𝒞, prove that (h ∘ g) ∘ f = h ∘ (g ∘ f).

2. **Isomorphism Properties**: If f : A → B is an isomorphism, prove that f⁻¹ is unique. Then show that if g : B → C is also an isomorphism, then (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹.

3. **Monic/Epic**: Prove that every isomorphism is both monic and epic. Give an example where a morphism is both monic and epic but not an isomorphism.

## Functors (confident)

### Practice Questions

1. **Functor Laws**: Given functors F : 𝒞 → 𝒟 and G : 𝒟 → ℰ, prove that G ∘ F preserves identities and composition.

2. **Faithful/Full**: Construct an example of a functor that is faithful but not full, and another that is full but not faithful.

3. **Preservation**: Show that any functor F : 𝒞 → 𝒟 preserves split monomorphisms (i.e., if m has a left inverse in 𝒞, then F(m) has a left inverse in 𝒟).

## Natural transformations (confident)

### Practice Questions

1. **Naturality**: Given functors F, G : 𝒞 → 𝒟 and a natural transformation α : F ⟹ G, prove that for any morphism f : A → B in 𝒞, the following square commutes:
   ```
   F(A) --α_A--> G(A)
     |            |
   F(f)          G(f)
     |            |
     v            v
   F(B) --α_B--> G(B)
   ```

2. **Vertical Composition**: If α : F ⟹ G and β : G ⟹ H are natural transformations, prove that β ∘ α : F ⟹ H is also natural.

3. **Natural Isomorphism**: Show that the natural transformation between the double dual functor and the identity on finite-dimensional vector spaces is a natural isomorphism.

## Cartesian closed structure (would like a refresher)

### Theory Review
A category 𝒞 is **cartesian closed** if:
1. 𝒞 has a terminal object 1
2. 𝒞 has binary products A × B for all objects A, B
3. For each object A, the functor A × (-) has a right adjoint (-)^A

The exponential object B^A represents the "function space" from A to B.

### Key Properties
- **Evaluation morphism**: ev : B^A × A → B
- **Curry/Uncurry**: For any f : C × A → B, there exists unique curry(f) : C → B^A such that f = ev ∘ (curry(f) × id_A)
- **Adjunction**: Hom(C × A, B) ≅ Hom(C, B^A)

### Practice Questions

1. **Curry/Uncurry**: Given f : (A × B) × C → D, express curry(curry(f)) : A → D^(B×C) and show this equals curry'(f) : A → (D^C)^B.

2. **Exponential Functoriality**: Prove that (-)^A is a contravariant functor in A and covariant functor in the exponent.

3. **Internal Logic**: In Set, show that the exponential B^A corresponds to the set of functions from A to B. Compute specific examples like 2^3 where 2 = {0,1}.

## Left and right adjoints (needs a bit of work)

### Theory Review
An **adjunction** F ⊣ G consists of functors F : 𝒞 → 𝒟, G : 𝒟 → 𝒞 with:
- **Unit**: η : Id_𝒞 ⟹ G ∘ F
- **Counit**: ε : F ∘ G ⟹ Id_𝒟
- **Triangle identities**: (ε_F) ∘ (F_η) = id_F and (G_ε) ∘ (η_G) = id_G

Equivalently: natural isomorphism Hom_𝒟(F(A), B) ≅ Hom_𝒞(A, G(B))

### Key Examples
- Free-forgetful adjunctions
- Product-exponential adjunction: (-) × A ⊣ (-)^A
- Diagonal-product adjunction: Δ ⊣ ×

### Practice Questions

1. **Unit/Counit**: From the hom-set bijection φ : Hom(F(A), B) ≅ Hom(A, G(B)), construct the unit and counit and verify the triangle identities.

2. **Preservation**: Prove that right adjoints preserve limits and left adjoints preserve colimits.

3. **Composition**: If F ⊣ G and F' ⊣ G', show that F' ∘ F ⊣ G ∘ G' with explicit unit and counit.

4. **Free Monoid**: Show that the free monoid functor List : Set → Mon is left adjoint to the forgetful functor U : Mon → Set.

## Dependent products and functions (completely unknown)

### Theory Explanation
**Dependent types** extend simple types by allowing types to depend on values. In category theory, this corresponds to fibrations and indexed categories.

### Dependent Products (Π-types)
Given a family of types B(x) indexed by x : A, the **dependent product** ∏_{x:A} B(x) represents functions f such that f(x) : B(x) for each x : A.

**Categorical Interpretation**:
- Given a fibration p : E → B and object I in B
- The dependent product ∏_I is right adjoint to weakening p* : E/I → E
- In presheaf topoi: (∏_f φ)(i) = ∏_{j ∈ f⁻¹(i)} φ(j)

### Dependent Functions
Dependent functions generalize exponentials:
- Simple function type: A → B
- Dependent function type: ∏_{x:A} B(x) (function taking x:A to B(x))

### Key Properties
1. **β-reduction**: ((λx:A. t) s) reduces to t[s/x]
2. **η-expansion**: f = λx. f(x) when f : ∏_{x:A} B(x)
3. **Substitution**: respects composition

### Practice Questions

1. **Basic Construction**: In the category of families over Set, construct the dependent product for the family B(n) = Fin(n) indexed by n : ℕ.

2. **Adjunction Property**: Show that weakening W : ∏_{x:A} B(x) → ∏_{x:A} C is left adjoint to dependent product formation when C doesn't depend on x.

3. **Type Theory**: Express the type of the polymorphic identity function id : ∏_{A:Type} A → A and show it corresponds to a natural transformation.

## Exponentials in presheaf categories (completely unknown)

### Theory Explanation
**Presheaf categories** PSh(𝒞) = [𝒞^op, Set] are always cartesian closed. The exponential G^F for presheaves F, G : 𝒞^op → Set is given by:

**(G^F)(c) = Nat(y(c) × F, G)**

where y : 𝒞 → PSh(𝒞) is the Yoneda embedding and Nat denotes natural transformations.

### Explicit Construction
For c ∈ 𝒞:
```
(G^F)(c) = {α : ∀d. Hom(c,d) × F(d) → G(d) |
           α natural in d}
```

### Key Properties
1. **Yoneda Lemma**: Nat(y(c), F) ≅ F(c)
2. **Evaluation**: ev_c : (G^F)(c) × F(c) → G(c)
3. **Curry**: For φ : H × F → G, curry(φ)(c)(h)(f) = φ_c(h,f)

### Examples
- **Terminal Object**: 1(c) = {*} (constant presheaf)
- **Products**: (F × G)(c) = F(c) × G(c) (pointwise)
- **Representables**: If F = y(a), then G^F ≅ G^a where G^a(c) = G(c)^{Hom(c,a)}

### Practice Questions

1. **Exponential Calculation**: In PSh(2) where 2 = {0 → 1}, compute Ω^Ω where Ω is the subobject classifier.

2. **Natural Transformation**: For presheaves F, G on ℕ^op (natural numbers with reverse order), construct the evaluation map ev : G^F × F → G explicitly.

3. **Representable Case**: If F = Hom(-,a) in PSh(𝒞), show that G^F(c) ≅ G(c)^{Hom(c,a)} and relate this to the enriched Yoneda lemma.

4. **Internal Logic**: Express the exponential transpose of a morphism φ : F × G → H in PSh(𝒞) using the internal language of topoi.

