module Reversible.Pi.CPerm where

open import Type using (Type₀)
open import Paths using (_==_)
open import Functions using (_∘_; id)
open import Homotopies using (_∼_)
open import DependentSum using (p₁; p₂)
open import Equivalences using (_≃_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; allFin; tabulate; lookup)

FinVec : ℕ → ℕ → Type₀
FinVec m n = Vec (Fin m) n

1C : {n : ℕ} → FinVec n n
1C {n} = allFin n

_!!_ : ∀ {m} {A : Type₀} → Vec A m → Fin m → A
v !! i = lookup i v

infixr 80 _∘̂_
_∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ == 1C
    βp : πᵒ ∘̂ π == 1C

postulate
  perm-equiv : {m n : ℕ} → CPerm m n ≃ (Fin m ≃ Fin n)

perm-to-equiv : {m n : ℕ} → CPerm m n → Fin m ≃ Fin n
perm-to-equiv = p₁ perm-equiv

equiv-to-perm : {m n : ℕ} → Fin m ≃ Fin n → CPerm m n
equiv-to-perm = p₁ (p₂ perm-equiv)

ε : {m n : ℕ} → equiv-to-perm {m} {n} ∘ perm-to-equiv ∼ id
ε = p₁ (p₂ (p₂ perm-equiv))

η : {m n : ℕ} → perm-to-equiv {m} {n} ∘ equiv-to-perm ∼ id
η = p₁ (p₂ (p₂ (p₂ perm-equiv)))
