module Reversible.Pi.K.PermutationGroup where

open import Type using (Type)
open import Paths
open import Equivalences
open import DependentSum
open import PathsInSigma
open import Functions
open import FunctionExtensionality

open import Reversible.Utils

open import Algebra using (Group)

module _ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} {W : Type ℓ₄} where
  ●trans : (e₁ : Z ≃ W) (e₂ : Y ≃ Z) (e₃ : X ≃ Y) → (e₁ ● e₂) ● e₃ == e₁ ● (e₂ ● e₃)
  ●trans (f , f⁻¹ , εf , ηf , τf) (g , g⁻¹ , εg , ηg , τg) (h , h⁻¹ , εh , ηh , τh) =
    dpair= (refl (f ∘ g ∘ h) , dpair= (refl (h⁻¹ ∘ g⁻¹ ∘ f⁻¹) ,
      dpair= (funext (λ x →
        ap h⁻¹ (ap g⁻¹ (εf (g (h x))) ◾ εg (h x)) ◾ εh x
          ==⟨ {!!} ⟩
        {!!}
      ) ,
      dpair= ({!!} , {!!}))))

permutationGroup : ∀ {ℓ} (X : Type ℓ) → Group ℓ ℓ
permutationGroup X = record {
  Carrier = X ≃ X ;
  _≈_ = _==_ ;
  _∙_ = _●_  ;
  ε = ide _ ;
  _⁻¹ = !e ;
  isGroup = record {
    isMonoid = record {
      isSemigroup = record {
        isEquivalence = record {
          refl = refl _ ;
          sym = ! ;
          trans = λ p q → p ◾ q
        } ;
        assoc = ●trans ;
        ∙-cong = λ x₁ x₂ → {!!}
      } ;
      identity = {!!}
    } ;
      inverse = {!!} ;
      ⁻¹-cong = {!!} } }
