module Reversible.Pi.Semantics where

open import Type using (Type)
open import Paths using (_==_; !; _◾_; ap; refl; tpt)
open import DependentSum using (Σ; _,_)
open import Functions using (_∘_)
open import Equivalences using (_≃_; path-to-eqv; ide)
open import Univalence using (ua; ua-η; ua-ide)
open import PathsInSigma using (dpair=; dpair=-e₁; dpair=-e₂; dpair=-η; dpair=-β₁)
open import PropositionalTruncation using (identify)
open import OneTypes using (prop-is-set)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

open import Reversible.UnivalentFibrations using (U[_]; lift; lift-equiv)
open import Reversible.Pi.CPerm using (CPerm; perm-to-equiv; equiv-to-perm; η; ε)

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where
  ap-dpair=-e-out : {x y : X} → {ux : P x} → {uy : P y}
                     → {p q : (x , ux) == (y , uy)}
                     → (α : dpair=-e₁ p == dpair=-e₁ q)
                     → (tpt _ α (dpair=-e₂ p) == dpair=-e₂ q)
                     → (p == q)
  ap-dpair=-e-out {p = p} {q} α β = ! (dpair=-η p)
                                    ◾ ap dpair= (dpair= (α , β))
                                    ◾ dpair=-η q

all-eqvs-fin : {m n : ℕ} (f : Fin m ≃ Fin n) → Σ (CPerm m n) (λ p → f == perm-to-equiv p)
all-eqvs-fin f = equiv-to-perm f , ! (η f)

all-1-paths-fin : {m n : ℕ} (l : Fin m == Fin n) → Σ (CPerm m n) (λ p → l == ua (perm-to-equiv p))
all-1-paths-fin {m} {n} = φ ∘ all-eqvs-fin ∘ path-to-eqv where
  φ : {l : Fin m == Fin n} → Σ (CPerm m n) (λ p → path-to-eqv l == perm-to-equiv p) →
                              Σ (CPerm m n) (λ p → l == ua (perm-to-equiv p))
  φ {l} (p , e) = p , ! (ua-η l) ◾ ap ua e

`Fin : (n : ℕ) → U[ Fin n ]
`Fin n = lift (Fin n)

all-1-paths : {n : ℕ} (l : `Fin n == `Fin n) →
  Σ (CPerm n n) (λ p → l == lift-equiv (perm-to-equiv p))
all-1-paths {n} = φ ∘ all-1-paths-fin ∘ dpair=-e₁ where
  φ : {l : `Fin n == `Fin n} → Σ (CPerm n n) (λ p → dpair=-e₁ l == ua (perm-to-equiv p)) →
                                Σ (CPerm n n) (λ p → l == lift-equiv (perm-to-equiv p))
  φ (p , e) = p , ap-dpair=-e-out (e ◾ ! (dpair=-β₁ (ua _ , _))) (prop-is-set identify _ _ _ _)
