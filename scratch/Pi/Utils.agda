module Reversible.Utils where

open import Type
open import Paths
open import Functions
open import FunctionExtensionality

infix  2  _∎      -- equational reasoning
infixr 2  _==⟨_⟩_  -- equational reasoning

_==⟨_⟩_ : ∀ {ℓ} → {A : Type ℓ} (x : A) {y z : A} → x == y → y == z → x == z
_ ==⟨ p ⟩ q = p ◾ q 

_∎ : ∀ {ℓ} → {A : Type ℓ} (x : A) → x == x
_∎ x = refl x

module _ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} where
  ∘-assoc : (f : C → D) (g : B → C) (h : A → B) → f ∘ (g ∘ h) == (f ∘ g) ∘ h
  ∘-assoc f g h = funext (refl ∘ f ∘ g ∘ h)

module _ {ℓ₁} {ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where
  ∘-unit : (f : A → B) → id ∘ f == f
  ∘-unit f = funext (refl ∘ f)
