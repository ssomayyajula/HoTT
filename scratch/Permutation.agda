module Reversible.Pi.Permutation where

open import Type
open import Zero
open import Paths
open import DependentSum
open import Functions
open import FunctionExtensionality
open import Equivalences
open import Data.Nat

open import Reversible.Utils
open import Reversible.Pi.AFin

data Perm : ℕ → Type₀ where
  right-shift : {n : ℕ} → Perm n
  swap12 : {n : ℕ} → Perm (suc (suc n))
  _□_ : {n : ℕ} → Perm n → Perm n → Perm n

{-
swap12-f : {n : ℕ} → AFin (suc (suc n)) → AFin n
swap12-f = {!!}
-}

perm-to-equiv : {n : ℕ} → Perm n → AFin n ≃ AFin n
perm-to-equiv {0}     right-shift = ide 𝟘
perm-to-equiv {suc n} right-shift = {!!}
perm-to-equiv swap12      = {!!}
perm-to-equiv (p □ q) =
  let (f1 , e1)      = perm-to-equiv p in
  let (f2 , e2)      = perm-to-equiv q in
  let (g1 , η1 , ε1) = hae-is-qinv e1  in
  let (g2 , η2 , ε2) = hae-is-qinv e2  in
  f1 ∘ f2 , qinv-is-equiv (g2 ∘ g1 , (λ x →
    ((g2 ∘ g1) ∘ (f1 ∘ f2)) x
      ==⟨ ap (λ f → f x) (! (∘-assoc g2 g1 (f1 ∘ f2))) ⟩
    (g2 ∘ g1 ∘ f1 ∘ f2) x
      ==⟨ ap (λ f → (g2 ∘ f) x) (∘-assoc g1 f1 f2) ⟩
    (g2 ∘ (g1 ∘ f1) ∘ f2) x
      ==⟨ ap g2 (η1 (f2 x)) ⟩
    (g2 ∘ id ∘ f2) x
      ==⟨ ap (λ f → (g2 ∘ f) x) (∘-unit f2) ⟩
    (g2 ∘ f2) x
      ==⟨ η2 x ⟩
    (id x ∎)) , (λ x →
    ((f1 ∘ f2) ∘ (g2 ∘ g1)) x
      ==⟨ ap (λ f → f x) (! (∘-assoc f1 f2 (g2 ∘ g1))) ⟩
    (f1 ∘ f2 ∘ g2 ∘ g1) x
      ==⟨ ap (λ f → (f1 ∘ f) x) (∘-assoc f2 g2 g1) ⟩
    (f1 ∘ (f2 ∘ g2) ∘ g1) x
      ==⟨ ap f1 (ε2 (g1 x)) ⟩
    (f1 ∘ id ∘ g1) x
      ==⟨ ap (λ f → (f1 ∘ f) x) (∘-unit g1) ⟩
    (f1 ∘ g1) x
      ==⟨ ε1 x ⟩
    (id x ∎)))

equiv-to-perm : {n : ℕ} → AFin n ≃ AFin n → Perm n
equiv-to-perm (f , e) =
  let (g , η , ε) = hae-is-qinv e in
  {!!}
