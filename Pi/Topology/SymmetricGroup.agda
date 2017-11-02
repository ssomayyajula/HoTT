{-# OPTIONS --without-K --rewriting #-}

module Pi.Topology.SymmetricGroup where

open import lib.Basics
open import lib.types.Fin
open import lib.types.Nat
open import lib.types.Group using (Group; group; group-structure)

Array : ℕ → ∀ {ℓ} → Type ℓ → Type ℓ
Array n A = Fin n → A

ℕ⁺ : Type₀
ℕ⁺ = Σ ℕ (λ n → 0 < n)

ℕ⁺-pred : ℕ⁺ → ℕ
ℕ⁺-pred (0 , ())
ℕ⁺-pred (S n , _) = n

pS : ℕ⁺ → ℕ⁺
pS (n , l) = (S n , ltSR l)

record Sy (n : ℕ⁺) {ℓ} (G : Group ℓ) : Type ℓ where
  open Group G
  field
    σ : Array (ℕ⁺-pred n) El
    idem : ∀ i → comp (σ i) (σ i) == σ i
    --csuc : ∀ i → comp (comp (σ i) (σ i)) (comp (σ i) ())
