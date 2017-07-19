{-# OPTIONS --without-K #-}

module Reversible.Pi.Level1 where

open import Paths using (_==_; refl; _◾_; tpt)

open import Type using (Type; lsuc; lzero)
open import One
open import DependentSum using (Σ; _,_; p₁; p₂)
open import PathsInSigma using (dpair=-e₁; dpair=)

open import Equivalences using (_≃_; path-to-eqv; tpt-eqv; qinv-is-equiv)
open import Univalence using (ua)
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; identify)

open import OneTypes using (is-prop;prop; prop-is-set)

open import NaturalNumbers using (ℕ)

open import Reversible.Pi.Syntax
open import Reversible.Pi.Level0
--open import Reversible.Pi.FinUniverse

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El; finite-types-is-univ)

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ c ⟧₁ = p₁ (finite-types-is-univ _ _) #⟦ c ⟧₁

-- A classical result, sort of
postulate
  ==-to-⟷ : {m n : ℕ} → El m == El n → fromSize m ⟷ fromSize n

-- Some automorphism on the flattened versions of X and Y
--dpair=-e₁ p
--fromSize n1 <-> fromSize n2
-- Don't use truncation: use all-1-paths to get a permutation, then postulate that
-- permutations can be converted to ⟷
⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ∥ ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹ ∥
⟦_⟧₁⁻¹ {_ , _ , c₁} {_ , _ , c₂} p =
  recTrunc _ (λ c₁ →
  recTrunc _ (λ c₂ →
    ∣ ==-to-⟷ (Paths.! c₁ ◾ dpair=-e₁ p ◾ c₂) ∣
  ) identify c₂) identify c₁ 

-- ⟦ ⟦ p ⟧₁ ⟧₁⁻¹ : fromSize (size X) ⟷ fromSize (size Y)
-- p : X ⟷ Y
--

canonicalC : {A B : U} → (c : A ⟷ B) → ⟦ ⟦ A ⟧₀ ⟧₀⁻¹ ⟷ ⟦ ⟦ B ⟧₀ ⟧₀⁻¹
canonicalC {A} {B} c = ! (normalizeC A) ◎ (c ◎ normalizeC B )

R : {A B : U} → (c : A ⟷ B) (tc' : ∥ A ⟷ B ∥) → Set
R c tc' = {!!}

⟦⟦_⟧₁⟧₁⁻¹ : {X Y : U} (c : X ⟷ Y) → R (canonicalC c) (⟦ ⟦ c ⟧₁ ⟧₁⁻¹)
⟦⟦ _ ⟧₁⟧₁⁻¹ = {!!}

⟦⟦_⟧₁⁻¹⟧₁ : {X Y : M} (p : X == Y) → {!!} --∣∣ recTrunc _ (λ P → tpt (λ x → x == Y) P p) _  ⟦⟦ X ⟧₀⁻¹⟧₀ ∣∣
⟦⟦ refl _ ⟧₁⁻¹⟧₁ = {!!}

--cmpl₁ : {X Y : M} (p : X == Y) → Σ (⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹) (λ c → ∥ ⟦ c ⟧₁ == {!!} ∥)
--cmpl₁ p = ⟦ p ⟧₁⁻¹ , {!!} --⟦⟦ p ⟧₁⁻¹⟧₁
