module Pi.Topology.Equivalence where

open import lib.Basics
open import lib.Equivalence2 using (is-equiv-is-prop)
open import lib.types.Group using (Group; group; group-structure)
open import lib.NType2 using (≃-is-set)

invol-is-equiv : ∀ {ℓ} {A : Type ℓ} {f : A → A} → f ∘ f ∼ idf A → is-equiv f
invol-is-equiv {f = f} h = is-eq f f h h

module _ {ℓ} where
  ua-ide : (A : Type ℓ) → ua (ide A) == idp
  ua-ide _ = ua-η idp

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'}  where
  equiv= : {f g : A ≃ B} → fst f == fst g → f == g
  equiv= p = pair= p (from-transp _ _ (prop-has-all-paths is-equiv-is-prop _ _))

  ∘e-unit-l : (f : A ≃ B) → ide B ∘e f == f
  ∘e-unit-l f = equiv= idp

-- Equivalences on a set form a group under composition, inversion
≃-Group : ∀ {ℓ} {A : Type ℓ} → is-set A → Group ℓ
≃-Group {A = A} h = group (A ≃ A) (≃-is-set h h)
  (group-structure
    (ide _) _⁻¹ _∘e_
    ∘e-unit-l
    (λ _ _ _   → equiv= idp)
    (λ{(_ , e) → equiv= (λ= (is-equiv.g-f e))}))
