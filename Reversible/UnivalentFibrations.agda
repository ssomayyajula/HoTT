{-# OPTIONS --without-K #-}

module Reversible.UnivalentFibrations where

open import Type
open import DependentSum
open import Paths
open import Equivalences
open import PathsInSigma
open import Univalence
open import PropositionalTruncation

open import Reversible.Utils

module _ {ℓ} where
  {- The base space of a univalent fibration -}
  U[_] : Type ℓ → Type (lsuc ℓ)
  U[ T ] = Σ (Type ℓ) (λ X → ∥ X == T ∥)

  El[_] : (T : Type ℓ) → U[ T ] → Type ℓ
  El[ _ ] = p₁

  Ũ : Type ℓ → Type (lsuc ℓ)
  Ũ T = Σ U[ T ] El[ T ]

  infix 100 `_
  `_ : (T : Type ℓ) → U[ T ]
  ` T = T , ∣ refl T ∣

  `equiv : ∀ {X Y : Type ℓ} → (e : X ≃ Y) → tpt U[_] (ua e) (` X) == ` Y
  `equiv = ind≃ (λ {X} {Y} e → tpt U[_] (ua e) (` X) == ` Y)
    (λ X → tpt U[_] (ua (ide X)) (` X)
              ==⟨ ap (λ p → tpt U[_] p (` X)) (ua-ide X) ⟩
            tpt U[_] (refl X) (` X)
              ==⟨ refl _ ⟩
            (` X ∎))

  `loop : ∀ {X : Type ℓ} → (e : X ≃ X) → ` X == ` X
  `loop e = dpair= (ua e , identify _ _)

  `id : {T : Type ℓ} {A : U[ T ]} → A == A
  `id {_} {A} = refl A
