open import UnivalentTypeTheory
open import PropositionalTruncation

postulate
  K : Type₀
  base : K
  loop : base == base
  ρ : loop ◾ loop == refl base
  φ : is-1type K

`𝟚 : Type₁
`𝟚 = Σ Type₀ (λ X → ∥ X == 𝟚 ∥)

_ : K ≃ `𝟚
_ = f , qinv-is-equiv (g , {!!} , {!!}) where

  f : K → `𝟚
  f = {!!}

  g : `𝟚 → K
  g = {!!}
