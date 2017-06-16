module Reversible.Pi.Permutation2 where

open import UnivalentTypeTheory
open import Reversible.Pi.AFin

infixr 5 _∷_

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (succ n)

postulate
  has-no-dup : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → Type₀

Perm : ℕ → Type₀
Perm n = Σ (Vec (AFin n) n) has-no-dup

perm-to-equiv : {n : ℕ} → Perm n → AFin n ≃ AFin n
perm-to-equiv ([] , _) = ide 𝟘
perm-to-equiv {succ n} ((x ∷ xs) , nd) = {!!}

equiv-to-perm : {n : ℕ} → AFin n ≃ AFin n → Perm n
equiv-to-perm (f , g , η , h , ε) = {!!}

perm-equiv : (n : ℕ) → Perm n ≃ (AFin n ≃ AFin n)
perm-equiv n = perm-to-equiv , qinv-is-equiv (equiv-to-perm , {!!} , {!!})
