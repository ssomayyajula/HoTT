open import UnivalentTypeTheory
open import PropositionalTruncation

open import EmbeddingsInUniverse

open UnivalentUniverseOfFiniteTypes

plus-𝟘 : ∀ {ℓ} (X : Type ℓ) → X + 𝟘 ≃ X
plus-𝟘 _ = (λ { (i₁ x) → x; (i₂ ()) }) , qinv-is-equiv (i₁ , (λ { x@(i₁ _) → refl x; (i₂ ()) }) , refl)

module _ {ℓ₁} {ℓ₂} {ℓ₃} (X : Type ℓ₁) (Y : Type ℓ₂) (Z : Type ℓ₃) where
  +assoc : X + Y + Z ≃ (X + Y) + Z
  +assoc = (λ { (i₁ x) → i₁ (i₁ x); (i₂ (i₁ x)) → i₁ (i₂ x); (i₂ (i₂ x)) → i₂ x }) , qinv-is-equiv ((λ { (i₁ (i₁ x)) → i₁ x; (i₁ (i₂ x)) → i₂ (i₁ x); (i₂ x) → i₂ (i₂ x) }) , (λ { x@(i₁ _) → refl x; x@(i₂ (i₁ _)) → refl x; x@(i₂ (i₂ _)) → refl x }) , (λ { x@(i₁ (i₁ _)) → refl x; x@(i₁ (i₂ _)) → refl x; x@(i₂ _) → refl x }))

`𝟙+𝟘 : Σ Type₀ is-finite
`𝟙+𝟘 = 𝟙 + 𝟘 , `1+ `0 , ∣ refl _ ∣

`𝟚 : Σ Type₀ is-finite
`𝟚 = 𝟚 , `1+ (`1+ `0) , ∣ ! (ua (+assoc 𝟙 𝟙 𝟘) ◾ ua (plus-𝟘 (𝟙 + 𝟙)) ◾ ua 𝟙+𝟙≃𝟚) ∣

