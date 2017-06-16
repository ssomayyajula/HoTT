module Reversible.Pi.AFin where

open import UnivalentTypeTheory

data Fin : ℕ → Type₀ where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

AFin : ℕ → Type₀
AFin 0 = 𝟘
AFin (succ n) = 𝟙 + AFin n

pattern afzero   = i₁ 0₁
pattern afsucc x = i₂ x

private
  afin-to-fin : {n : ℕ} → AFin n → Fin n
  afin-to-fin {0}      ()
  afin-to-fin {succ n} afzero     = fzero
  afin-to-fin {succ n} (afsucc x) = fsucc (afin-to-fin x)
  
  fin-to-afin : {n : ℕ} → Fin n → AFin n
  fin-to-afin {0}      ()
  fin-to-afin {succ n} fzero     = afzero
  fin-to-afin {succ n} (fsucc x) = afsucc (fin-to-afin x)
  
  ε : {n : ℕ} → fin-to-afin {n} ∘ afin-to-fin ∼ id
  ε {0}      ()
  ε {succ n} afzero     = refl afzero
  ε {succ n} (afsucc x) = ap afsucc (ε x)
  
  η : {n : ℕ} → afin-to-fin {n} ∘ fin-to-afin ∼ id
  η {0}      ()
  η {succ n} fzero     = refl fzero
  η {succ n} (fsucc x) = ap fsucc (η x)

afin-fin-equiv : {n : ℕ} → AFin n ≃ Fin n
afin-fin-equiv = afin-to-fin , qinv-is-equiv (fin-to-afin , ε , η)

afin-eq-fin : {n : ℕ} → AFin n == Fin n
afin-eq-fin = ua afin-fin-equiv
