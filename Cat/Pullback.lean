import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

namespace CategoryTheory.Limits

universe u

variable
    {𝓒 : Type u}
    [Category 𝓒]
    {U V W X Y Z P T : 𝓒}

section pull

variable
    {f : X ⟶ Z} {g : Y ⟶ Z}
    (fst : W ⟶ X)
    (snd : W ⟶ Y)
    (eq : fst ≫ f = snd ≫ g)

def IsPullback := IsLimit (PullbackCone.mk fst snd eq)

#check PullbackCone.IsLimit.mk

def IsPullback.ofUniqueHom {fst snd}
    (eq : fst ≫ f = snd ≫ g) (lift : (s : PullbackCone f g) → s.pt ⟶ W)
    (fac_left : ∀ (s : PullbackCone f g), lift s ≫ fst = s.fst)
    (fac_right : ∀ (s : PullbackCone f g), lift s ≫ snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.pt ⟶ W), m ≫ fst = s.fst → m ≫ snd = s.snd → m = lift s)
    : IsPullback fst snd eq := 
  PullbackCone.IsLimit.mk eq lift fac_left fac_right uniq

#check PullbackCone.isLimitAux

end pull

