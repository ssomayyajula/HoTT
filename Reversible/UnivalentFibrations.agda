{-# OPTIONS --without-K #-}

module Reversible.UnivalentFibrations where

open import UnivalentTypeTheory
open import PropositionalTruncation
open import TwoUniverse using (is-type)

module _ {ℓ} where
  {- The base space of a univalent fibration -}
  U[_] : Type ℓ → Type (lsuc ℓ)
  U[ T ] = Σ (Type ℓ) (is-type T)

  El[_] : (T : Type ℓ) → U[ T ] → Type ℓ
  El[ _ ] = p₁

  Ũ : Type ℓ → Type (lsuc ℓ)
  Ũ T = Σ U[ T ] El[ T ]

  lift : (T : Type ℓ) → U[ T ]
  lift T = T , ∣ refl T ∣

  `id : {T : Type ℓ} {A : U[ T ]} → A == A
  `id {_} {A} = refl A

infixl 7 _`×_
infixl 6 _`+_
data Names : Type₀ where
  `0 : Names
  `1 : Names
  _`+_ : Names → Names → Names
  _`×_ : Names → Names → Names

{-# TERMINATING #-}
El : Names → Type₀
El = λ
  { `0       → 𝟘;
    `1       → 𝟙;
    (X `+ Y) → El X + El Y;
    (X `× Y) → El X × El Y }
