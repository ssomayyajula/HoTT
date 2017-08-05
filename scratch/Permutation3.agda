module Reversible.Pi.Permutation3 where

open import Data.Vec
open import Data.Nat hiding (_+_; _≤_; _>_; Ordering; compare)

open import Type
open import DependentSum
open import Equivalences
open import Functions
open import Coproduct
open import Paths
open import Zero
open import Reversible.Utils

open import Data.Fin hiding (_+_; _<_)

has-init-seg : {n : ℕ} → Vec ℕ n → Type₀
has-init-seg {n} v = (m : ℕ) → m < n → m ∈ v

is-perm : {n : ℕ} → Vec ℕ n → Type₀
is-perm v = has-init-seg v

Perm : ℕ → Type₀
Perm n = Σ (Vec ℕ n) is-perm

suc-not-eq-zero : {n : ℕ} {x : Fin n} → ¬ (Data.Fin.suc x == zero)
suc-not-eq-zero ()

equiv-is-inj : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → is-equiv f → (x y : A) → f x == f y → x == y
equiv-is-inj _ (g , h , _) x y p = ! (h x) ◾ (ap g p) ◾ h y

tri : {n : ℕ} → (i j : Fin n) → (Data.Fin._<_ i j) + (i == j) + (Data.Fin._<_ j i)
tri zero zero    = i₂ (i₁ (refl zero))
tri (suc x) zero = i₂ (i₂ (s≤s z≤n))
tri zero (suc x) = i₁ (s≤s z≤n)
tri (suc x) (suc y) with tri x y
tri (suc x) (suc y) | i₁     x<y  = i₁ (s≤s x<y)
tri (suc x) (suc y) | i₂ (i₁ x=y) = i₂ (i₁ (ap suc x=y))
tri (suc x) (suc y) | i₂ (i₂ y<x) = i₂ (i₂ (s≤s y<x))

squeeze : {m n : ℕ} → (x : Fin n) → toℕ x < m → Fin m
squeeze {0}     _       ()
squeeze {suc _} zero    _         = zero
squeeze {suc _} (suc x) (s≤s x≤n) = suc (squeeze x x≤n)

fpred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
fpred zero    = zero
fpred (suc x) = x

fin-bound : {n : ℕ} (x : Fin n) → toℕ x < n
fin-bound {0} ()
fin-bound zero    = s≤s z≤n
fin-bound (suc x) = s≤s (fin-bound x)

demote : {x y : ℕ} → x < suc y → Data.Nat._≤_ x y
demote (s≤s l) = l

trans : {x y z : ℕ} → x < y → Data.Nat._≤_ y z → x < z
trans {0} (s≤s l) (s≤s l') = s≤s z≤n
trans {suc x} (s≤s l) (s≤s l') = s≤s (trans l l')

ex : Fin 3
ex = squeeze {3} {5} (suc (suc zero)) (s≤s (s≤s (s≤s z≤n)))

perm-succ : {n : ℕ} → ℕ → Perm n → Perm (suc n)
perm-succ _ ([] , isperm) = (0 ∷ []) , (λ { 0 → λ _ → here; (suc n) → λ { (s≤s ()) } })
perm-succ m (v , isperm) = {!!}

perm-pred : {n : ℕ} → Perm (suc n) → Perm n
perm-pred {n} ((x ∷ xs) , isperm) = ({!!} , (λ m m<n → {!!})) where
  eject : Perm (suc n) → Perm n
  eject = {!!}-- (x :: xs , _) with tri x 

fin-equiv-succ : {n : ℕ} → ℕ → Fin n ≃ Fin n → Fin (suc n) ≃ Fin (suc n)
fin-equiv-succ m (f , φ) = ({!!} , {!!})

fin-equiv-pred : {n : ℕ} → Fin (suc n) ≃ Fin (suc n) → Fin n ≃ Fin n
fin-equiv-pred {0}     _               = ide (Fin 0)
fin-equiv-pred {suc m} e@(f , (g , _)) =
  eject e , qinv-is-equiv ({!!} , {!!} , {!!}) where
  
  eject : Fin (suc (suc m)) ≃ Fin (suc (suc m)) → Fin (suc m) → Fin (suc m)
  eject (f , φ) x with tri (f (suc x)) (f zero)
  ...             | i₁ lt      = squeeze (f (suc x)) (trans lt (demote (fin-bound (f zero))))
  ...             | i₂ (i₁ eq) = rec𝟘 _ (suc-not-eq-zero (equiv-is-inj f φ (suc x) zero eq))
  ...             | _          = fpred (f (suc x))

perm-to-equiv : {n : ℕ} → Perm n → Fin n ≃ Fin n
perm-to-equiv ([] , _) = ide (Fin 0)
perm-to-equiv ((m ∷ v) , φ) =
  fin-equiv-succ m (perm-to-equiv (perm-pred ((m ∷ v) , φ)))

equiv-to-perm : {n : ℕ} → Fin n ≃ Fin n → Perm n
equiv-to-perm {zero} e = [] , (λ m ())
equiv-to-perm {suc n} (f , e) =
  perm-succ (toℕ (f zero)) (equiv-to-perm (fin-equiv-pred (f , e)))

