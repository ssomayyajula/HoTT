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

open import PathsInSigma using (dpair=)

open import Reversible.Pi.Syntax
open import Reversible.Pi.Level0

size= : {X Y : U} → X ⟷ Y → size X == size Y
size= = {!!}

{- tpt-dpair (ua #⟦ c ⟧₁)) ◾
                 tpt-const (ua #⟦ c ⟧₁)  ◾
                 size= c -}
--ua #⟦ c ⟧₁
⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ canonicalU X ⟧₀ == ⟦ canonicalU Y ⟧₀
⟦_⟧₁ c = dpair= ({!!} , dpair= ({!!} , identify _ _))

⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹
⟦ refl _ ⟧₁⁻¹ = id⟷

{-⟦⟦_⟧₁⁻¹⟧₁ : {X Y : M} (p : X == Y) → ∣∣ recTrunc _ (λ P → tpt (λ x → x == Y) P p) _  ⟦⟦ X ⟧₀⁻¹⟧₀ ∣∣
⟦⟦ refl _ ⟧₁⁻¹⟧₁ = {!!}-}

cmpl₁ : {X Y : M} (p : X == Y) → Σ (⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹) (λ c → ∥ ⟦ c ⟧₁ == {!!} ∥)
cmpl₁ p = ⟦ p ⟧₁⁻¹ , {!!} --⟦ p ⟧₁⁻¹ , ⟦⟦ p ⟧₁⁻¹⟧₁
