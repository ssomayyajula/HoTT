open import UnivalentTypeTheory

data 𝕊¹ : Type₀ where
  base : 𝕊¹

postulate
  loop : base == base

module _ {l} where
  ind-𝕊¹ : (P : 𝕊¹ → Type l) (b : P base) → tpt P loop b == b → (x : 𝕊¹) → P x
  ind-𝕊¹ _ b _ base = b

  postulate
    ind-𝕊¹-loop : {P : 𝕊¹ → Type l}
                   {b : P base}
                   {ℓ : tpt P loop b == b} →
                   apd P (ind-𝕊¹ P b ℓ) loop == ℓ

non-deg : ¬ (loop == refl base)
non-deg = {!!}
