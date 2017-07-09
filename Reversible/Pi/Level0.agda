{-# OPTIONS --without-K #-}

module Reversible.Pi.Level0 where

open import Type using (Type₀; Type₁)
open import Paths using (_==_; refl; _◾_; ap)
open import DependentSum using (Σ; _,_; p₂)
open import PathsInSigma using (dpair=)
open import Functions using (_∘_)
open import Equivalences using (is-retract)
open import NaturalNumbers
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; indTrunc; identify)

open import Reversible.Pi.Syntax

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El; is-finite)

M : Type₁
M = Σ Type₀ is-finite

fromSize : ℕ → U
fromSize = recℕ U ZERO (λ _ → PLUS ONE)

ℕ-U-is-retract : is-retract ℕ U
ℕ-U-is-retract = size , fromSize , indℕ _ (refl _) (λ _ → ap succ)

⟦_⟧₀' : ℕ → M
⟦ n ⟧₀' = El n , n , ∣ refl _ ∣

⟦_⟧₀⁻¹' : M → ℕ
⟦ _ , n , _ ⟧₀⁻¹' = n

⟦⟦_⟧₀⟧₀⁻¹' : (n : ℕ) → ⟦ ⟦ n ⟧₀' ⟧₀⁻¹' == n
⟦⟦_⟧₀⟧₀⁻¹' = indℕ _ (refl _) (λ _ → ap succ)

⟦⟦_⟧₀⁻¹⟧₀' : (X : M) → ∥ ⟦ ⟦ X ⟧₀⁻¹' ⟧₀' == X ∥
⟦⟦ T , n , p ⟧₀⁻¹⟧₀' = indTrunc (λ p → ∥ ⟦ ⟦ T , n , p ⟧₀⁻¹' ⟧₀' == T , n , p ∥)
  (λ { (refl _) → ∣ dpair= (refl _ , dpair= (refl _ , refl _)) ∣ }) (λ _ → identify) p

⟦_⟧₀ : U → M
⟦_⟧₀ = ⟦_⟧₀' ∘ size

⟦_⟧₀⁻¹ : M → U
⟦_⟧₀⁻¹ = fromSize ∘ ⟦_⟧₀⁻¹'

⟦⟦_⟧₀⁻¹⟧₀ : (X : M) → ∥ ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ == X ∥
⟦⟦ X@(_ , n , _) ⟧₀⁻¹⟧₀ = recTrunc _ (λ p →
  ∣ ap (λ x → El x , x , ∣ refl (El x) ∣) (p₂ (p₂ ℕ-U-is-retract) n) ◾ p ∣) identify ⟦⟦ X ⟧₀⁻¹⟧₀'

cmpl₀ : (x : M) → Σ U (λ t → ∥ ⟦ t ⟧₀ == x ∥)
cmpl₀ x = ⟦ x ⟧₀⁻¹ , ⟦⟦ x ⟧₀⁻¹⟧₀
