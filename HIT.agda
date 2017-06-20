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

data Susp {ℓ} (A : Type ℓ) : Type ℓ where
  N S : Susp A
  
postulate merid : ∀ {ℓ} {A : Type ℓ} → A → (_==_) {X = Susp A} N S

module _ {ℓ} {ℓ'} {A : Type ℓ} where
  ind-ΣA : (P : Susp A → Type ℓ') (n : P N) (s : P S) → ((a : A) → tpt P (merid a) n == s) → (x : Susp A) → P x
  ind-ΣA _ n _ _ N = n
  ind-ΣA _ _ s _ S = s


module _ {ℓ} {ℓ'} {A : Type ℓ} {P : Susp A → Type ℓ'} {n : P N} {s : P S} {m : (a : A) → tpt P (merid a) n == s} where
  postulate ind-ΣA-mcomp : (a : A) → apd P (ind-ΣA P n s m) (merid a) == m a

Σ𝟚≃𝕊¹ : Susp 𝟚 ≃ 𝕊¹
Σ𝟚≃𝕊¹ = (ind-ΣA _ base base (λ { 0₂ → {!!} ; 1₂ → {!!} })) , qinv-is-equiv ((λ x → {!!}) , {!!} , {!!})
