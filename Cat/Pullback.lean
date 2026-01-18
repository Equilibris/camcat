import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

namespace CategoryTheory.Limits

#check IsPullback

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

#check pullback

def IsPullback.ofUniqueHom {fst snd}
    (eq : fst ≫ f = snd ≫ g) (lift : (s : PullbackCone f g) → s.pt ⟶ W)
    (fac_left : ∀ (s : PullbackCone f g), lift s ≫ fst = s.fst)
    (fac_right : ∀ (s : PullbackCone f g), lift s ≫ snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.pt ⟶ W), m ≫ fst = s.fst → m ≫ snd = s.snd → m = lift s)
    : IsPullback fst snd eq :=
  PullbackCone.IsLimit.mk eq lift fac_left fac_right uniq

end pull

section push

variable
    {f : Z ⟶ X} {g : Z ⟶ Y}
    (inl : X ⟶ W)
    (inr : Y ⟶ W)
    (eq : f ≫ inl = g ≫ inr)

def IsPushout := IsColimit (PushoutCocone.mk inl inr eq)

#check pullback

#check PushoutCocone.IsColimit.mk

def IsPushout.ofUniqueHom {inl inr}
    (eq : f ≫ inl = g ≫ inr)
    (desc : (s : PushoutCocone f g) → W ⟶ s.pt)
    (fac_left : ∀ (s : PushoutCocone f g), inl ≫ desc s = s.inl)
    (fac_right : ∀ (s : PushoutCocone f g), inr ≫ desc s = s.inr)
    (uniq : ∀ (s : PushoutCocone f g) (m : W ⟶ s.pt), inl ≫ m = s.inl → inr ≫ m = s.inr → m = desc s)
    : IsPushout inl inr eq := 
  PushoutCocone.IsColimit.mk eq desc fac_left fac_right uniq

end push

section chosen

class ChosenPullback (C : Type u) [𝒞 : Category C] where
  pull {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : C
  fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : pull f g ⟶ X
  snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : pull f g ⟶ Y
  w {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : fst f g ≫ f = snd f g ≫ g
  ipb {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : IsPullback _ _ (w f g)

class ChosenPushout (C : Type u) [𝒞 : Category C] where
  push {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : C
  inl {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : X ⟶ push f g
  inr {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : Y ⟶ push f g
  w {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : f ≫ inl f g = g ≫ inr f g
  ipo {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : IsPushout _ _ (w f g)

alias pull := ChosenPullback.pull
alias push := ChosenPushout.push

end chosen

end CategoryTheory.Limits

