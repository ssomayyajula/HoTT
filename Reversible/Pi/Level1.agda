{-# OPTIONS --without-K #-}

module Reversible.Pi.Level1 where

open import Paths using (_==_; refl; !; _◾_; tpt)

open import DependentSum using (Σ; _,_; p₁; p₂)
open import PathsInSigma using (dpair=-e₁)

open import Equivalences using (_≃_; path-to-eqv)
open import Univalence using (ua)
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; identify)

open import NaturalNumbers using (ℕ)

open import Reversible.Pi.Syntax hiding (!)
open import Reversible.Pi.Level0

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El;finite-types-is-univ)

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ c ⟧₁ = p₁ (finite-types-is-univ _ _) #⟦ c ⟧₁

-- A classical result, sort of
postulate
  equiv-to-comb : {m n : ℕ} → El m ≃ El n → fromSize m ⟷ fromSize n

--! p₁ ◾ p₂
-- Some automorphism on the flattened versions of X and Y
⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ∥ ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹ ∥
⟦_⟧₁⁻¹ {_ , _ , p₁} {_ , _ , p₂} p =
  recTrunc _ (λ p₁ →
  recTrunc _ (λ p₂ → ∣ equiv-to-comb (path-to-eqv (! p₁ ◾ dpair=-e₁ p ◾ p₂)) ∣)
  identify p₂)
  identify p₁

-- ⟦ ⟦ p ⟧₁ ⟧₁⁻¹ : fromSize (size X) ⟷ fromSize (size Y)
-- p : X ⟷ Y
--⟦⟦_⟧₁⟧₁⁻¹ : {X Y : U} (p : X ⟷ Y) → ⟦ ⟦ p ⟧₁ ⟧₁⁻¹ ⇔ {!!}
--⟦⟦ _ ⟧₁⟧₁⁻¹ = {!!}

{-⟦⟦_⟧₁⁻¹⟧₁ : {X Y : M} (p : X == Y) → ∣∣ recTrunc _ (λ P → tpt (λ x → x == Y) P p) _  ⟦⟦ X ⟧₀⁻¹⟧₀ ∣∣
⟦⟦ refl _ ⟧₁⁻¹⟧₁ = {!!}-}

--cmpl₁ : {X Y : M} (p : X == Y) → Σ (⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹) (λ c → ∥ ⟦ c ⟧₁ == {!!} ∥)
--cmpl₁ p = ⟦ p ⟧₁⁻¹ , {!!} --⟦⟦ p ⟧₁⁻¹⟧₁
