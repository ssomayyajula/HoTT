module Reversible.Pi.AFin where

open import Type
open import Coproduct
open import DependentSum
open import Zero
open import One
open import Function
open import Homotopies
open import Paths
open import Equivalences

open import Data.Nat hiding (_+_)
open import Data.Fin hiding (_+_; _≤_; _-_)

AFin : ℕ → Type₀
AFin 0       = 𝟘
AFin (suc n) = 𝟙 + AFin n

pattern fzero  = i₁ 0₁
pattern fsuc x = i₂ x

{-
re-assoc : {m n : ℕ} → AFin (Data.Nat._+_ m n) ≃ AFin m + AFin n
re-assoc {0} = (λ x → i₂ x) , qinv-is-equiv ((λ { (i₁ ()); (i₂ x) → x }) , refl , (λ { (i₁ ()); (i₂ x) → refl (i₂ x) }))
re-assoc = {!!}
--re-assoc {suc m} = (λ { (i₁ m) → {!!}; (i₂ n) → {!!} }) , {!!}
--re-assoc {suc m} {n} = let (f , φ) = re-assoc {m} {n} in (λ { (i₁ x) → {!!}; (i₂ y) → (λ { (i₁ x') → {!!}; (i₂ y') → {!!} }) (f y) }) , {!!}

ex : AFin 5 ≃ AFin 3 + AFin 2
ex = re-assoc

--re-assoc z≤n = (λ x → i₂ x) , qinv-is-equiv ((λ { (i₁ ()); (i₂ x) → x }) , refl , (λ { (i₁ ()); (i₂ x) → refl (i₂ x) }))
--re-assoc (s≤s l) = let (f , φ) = re-assoc l in {!!} , {!!}
-}

private
  afin-to-fin : {n : ℕ} → AFin n → Fin n
  afin-to-fin {0}     ()
  afin-to-fin {suc n} fzero    = zero
  afin-to-fin {suc n} (fsuc x) = suc (afin-to-fin x)
  
  fin-to-afin : {n : ℕ} → Fin n → AFin n
  fin-to-afin {0} ()
  fin-to-afin     zero    = fzero
  fin-to-afin     (suc x) = fsuc (fin-to-afin x)
  
  ε : {n : ℕ} → (fin-to-afin {n} ∘ afin-to-fin) ∼ id
  ε {0}     ()
  ε {suc n} fzero    = refl fzero
  ε {suc n} (fsuc x) = ap fsuc (ε x)
  
  η : {n : ℕ} → (afin-to-fin {n} ∘ fin-to-afin) ∼ id
  η {0} ()
  η     zero    = refl zero
  η     (suc x) = ap suc (η x)

afin-fin-equiv : {n : ℕ} → AFin n ≃ Fin n
afin-fin-equiv = afin-to-fin , qinv-is-equiv (fin-to-afin , ε , η)
