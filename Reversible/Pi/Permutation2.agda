module Reversible.Pi.Permutation2 where

open import Type
open import Zero
open import Paths
open import Functions
open import DependentSum
open import Equivalences
open import Univalence

open import Data.Nat
open import Data.Vec

open import Reversible.Pi.AFin

_∉_ : ∀ {ℓ} {X : Type ℓ} → X → {n : ℕ} → Vec X n → Type ℓ
x ∉ xs = ¬ (x ∈ xs)

data HasNoDups {ℓ} {A : Set ℓ} : {n : ℕ} → Vec A n → Type ℓ where
  nil  : HasNoDups []
  cons : {n : ℕ} {x : A} {xs : Vec A n} → x ∉ xs → HasNoDups xs → HasNoDups (x ∷ xs)

x∉[] : ∀ {ℓ} {X : Type ℓ} {x : X} → x ∉ []
x∉[] ()

ex1 : HasNoDups (1 ∷ 2 ∷ 3 ∷ [])
ex1 = cons g (cons f (cons x∉[] nil)) where
  f : 2 ∉ (3 ∷ [])
  f (there 2∈[]) = x∉[] 2∈[]

  g : 1 ∉ (2 ∷ 3 ∷ [])
  g (there (there 1∈[])) = x∉[] 1∈[]

ex2 : ¬ (HasNoDups (1 ∷ 2 ∷ 2 ∷ []))
ex2 (cons _ (cons 2∉2::[] (cons _ _))) = 2∉2::[] here

ex3 : ¬ (HasNoDups (2 ∷ 1 ∷ 2 ∷ []))
ex3 (cons 2∉1::2::[] (cons _ (cons _ _))) = 2∉1::2::[] (there here)

Perm : ℕ → Type₀
Perm n = Σ (Vec (AFin n) n) HasNoDups
{-
index-of : ∀ {ℓ} {A : Type ℓ} (x : A) {n : ℕ} (xs : Vec A n) → x ∈ xs → AFin n
index-of x xs = helper fzero x xs where
  helper : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → AFin n → (x : A) (xs : Vec A n) → x ∈ xs → AFin n
  helper i x xs here      = i
  helper {n = 0} ()
  helper {n = suc n} i x (y ∷ ys) (there y∈ys) = helper {!!} x ys y∈ys
 -}


finject : ∀ {m} → AFin m → AFin (suc m)
finject {0} ()
finject {suc n} fzero    = fzero
finject {suc n} (fsuc x) = fsuc (finject x)

fpred : ∀ {n} → AFin n → AFin n
fpred {0} ()
fpred {suc n} fzero    = fzero
fpred {suc n} (fsuc x) = finject {n} x

{-
tabulat : ∀ {n} → (AFin n → AFin n) → Vec (AFin n) n
tabulat {zero}  f = []
tabulat {suc n} f = f fzero ∷ (tabulat {n = n} (fpred ∘ f ∘ fsuc))
-}

perm-to-equiv : {n : ℕ} → Perm n → AFin n ≃ AFin n
perm-to-equiv (xs , nd) =
  {- Inverse looks up x in xs and returns index -}
  (λ x → lookup (coe (ua afin-fin-equiv) x) xs) , (λ x → {!!}) , {!!} , {!!} , {!!}

--(λ x → (λ { fzero → fzero; (fsuc n) → n }) (f (fsuc x)))

equiv-to-perm : {n : ℕ} → AFin n ≃ AFin n → Perm n
equiv-to-perm {0} _ = ([] , nil)
equiv-to-perm {suc n} (f , e) =
  let (g , η , ε) = hae-is-qinv e in
  let (xs , nd) = equiv-to-perm {n} ((λ x → {!!}) , qinv-is-equiv {!!}) in
  {!!} {-((f fzero) ∷ xs) , cons {!!} nd-}

perm-equiv : {n : ℕ} → Perm n ≃ (AFin n ≃ AFin n)
perm-equiv = perm-to-equiv , qinv-is-equiv (equiv-to-perm , {!!} , {!!})

φ : (f : AFin n → AFin n) → is-equiv f → Σ (Perm n) (λ p → f == perm-to-equiv p)
φ x with perm-equiv
φ x | (perm , e) → (perm-to-equiv  )
