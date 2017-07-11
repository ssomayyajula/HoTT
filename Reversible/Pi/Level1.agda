{-# OPTIONS --without-K #-}

module Reversible.Pi.Level1 where

open import Type using (Type; _⊔_; Type₀; Type₁)
open import Zero using (𝟘)
open import One
open import Paths using (_==_; refl; !; _◾_; ap; tpt; ind=)
open import Coproduct
open import DependentSum using (Σ; _,_; _×_; p₁)
open import Functions using (_∘_)
open import Univalence using (ua)
open import Equivalences using (_≃_; ide; !e; _●_; qinv-is-equiv; hae-is-qinv)
open import NaturalNumbers
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; identify)

open import PathsInSigma using (dpair=; pair=; dpair=-e₁)

open import Reversible.Pi.Syntax
open import Reversible.Pi.Level0

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦_⟧₁ {X} {Y} c = dpair= (ua #⟦ c ⟧₁ , dpair= ({!!} , identify _ _))

⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹
⟦ refl _ ⟧₁⁻¹ = id⟷

⟦⟦_⟧₁⁻¹⟧₁ : {X Y : M} (p : X == Y) → ⟦ ⟦ p ⟧₁⁻¹ ⟧₁ == let l = recTrunc (tpt ) ⟦⟦ X ⟧₀⁻¹⟧₀ in {!!}
⟦⟦_⟧₁⁻¹⟧₁ = {!!}

--⟦⟦ X ⟧₀⁻¹⟧₀

--recTrunc  (tpt (λ x → x == ⟦ ⟦ Y ⟧₀⁻¹ ⟧₀) p ⟦ c ⟧₁) identify ⟦⟦ X ⟧₀⁻¹⟧₀

cmpl₁ : {X Y : M} (p : X == Y) → Σ (⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹) (λ c → ∥ ⟦ c ⟧₁  == {!!} ∥)
cmpl₁ (refl _) = {!!} --⟦ p ⟧₁⁻¹ , ⟦⟦ p ⟧₁⁻¹⟧₁
