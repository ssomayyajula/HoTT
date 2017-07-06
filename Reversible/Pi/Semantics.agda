module Reversible.Pi.Semantics where

open import Type using (Type₀; Type₁)
open import Zero using (𝟘)
open import One using (𝟙)
open import Paths using (_==_; refl; _◾_; tpt)
open import Coproduct using (_+_; i₁; i₂)
open import DependentSum using (Σ; _,_; _×_; p₁)
open import PathsInSigma using (dpair=)
open import Functions using (_∘_)
open import Univalence using (ua)
open import Equivalences using (qinv-is-equiv; _≃_; _●_; ide)
open import NaturalNumbers
open import PropositionalTruncation using (∣_∣; recTrunc; identify)

open import Reversible.Pi.Syntax
open import Reversible.UnivalentFibrations using (U[_]; `_; `equiv)
--open import Reversible.Pi.FinUniverse using (all-1-paths)

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes

M : Type₁
M = Σ Type₀ is-finite

fromSize : ℕ → U
fromSize 0        = ZERO
fromSize (succ n) = PLUS ONE (fromSize n)

canonicalU : U → U
canonicalU = fromSize ∘ size

size+ : (n₁ n₂ : ℕ) → PLUS (fromSize n₁) (fromSize n₂) ⟷ fromSize (add n₁ n₂)
size+ 0         n₂ = unite₊l
size+ (succ n₁) n₂ = assocr₊ ◎ (id⟷ ⊕ size+ n₁ n₂)

size* : (n₁ n₂ : ℕ) → TIMES (fromSize n₁) (fromSize n₂) ⟷ fromSize (mult n₁ n₂)
size* 0         n₂ = absorbr
size* (succ n₁) n₂ = dist ◎ ((unite⋆l ⊕ size* n₁ n₂) ◎ size+ n₂ (mult n₁ n₂))

normalizeC : (t : U) → t ⟷ canonicalU t
normalizeC ZERO = id⟷
normalizeC ONE  = uniti₊l ◎ swap₊
normalizeC (PLUS t₀ t₁) =
  (normalizeC t₀ ⊕ normalizeC t₁) ◎ size+ (size t₀) (size t₁) 
normalizeC (TIMES t₀ t₁) =
  (normalizeC t₀ ⊗ normalizeC t₁) ◎ size* (size t₀) (size t₁)

#⟦_⟧₀ : U → Type₀
#⟦ ZERO ⟧₀        = 𝟘
#⟦ ONE  ⟧₀        = 𝟙
#⟦ PLUS  t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ + #⟦ t₂ ⟧₀
#⟦ TIMES t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ × #⟦ t₂ ⟧₀

#⟦_⟧₁ : {X Y : U} → X ⟷ Y → #⟦ X ⟧₀ ≃ #⟦ Y ⟧₀
#⟦ _ ⟧₁ = {!!}

⟦_⟧₀ : U → M
⟦ T ⟧₀ = #⟦ T ⟧₀ , fromU T , ∣ ua (eq T ● #⟦ normalizeC T ⟧₁) ∣ where
  toNames : ℕ → Names
  toNames 0        = `0
  toNames (succ n) = `1+ (toNames n)
  
  fromU : U → Names
  fromU = toNames ∘ size
  
  eq : (T : U) → #⟦ canonicalU T ⟧₀ ≃ El (fromU T)
  eq ZERO = ide _
  eq ONE  = ide _
  eq (PLUS t₁ t₂) =
    let e1 = eq t₁ in
    let e2 = eq t₂ in
    {!!}
  eq (TIMES t₁ t₂) =
    let e1 = eq t₁ in
    let e2 = eq t₂ in
    {!!}

⟦_⟧₀⁻¹ : M → U
⟦ T , flatT , eq ⟧₀⁻¹ = toU flatT where
  toU : Names → U
  toU `0      = ZERO
  toU (`1+ n) = PLUS ONE (toU n)

⟦⟦_⟧₀⟧₀⁻¹ : (T : U) → ⟦ ⟦ T ⟧₀ ⟧₀⁻¹ ⟷ T
⟦⟦ ZERO ⟧₀⟧₀⁻¹ = id⟷
⟦⟦ ONE ⟧₀⟧₀⁻¹ = unite₊r
⟦⟦ PLUS t₁ t₂ ⟧₀⟧₀⁻¹ = {!!}
⟦⟦ _ ⟧₀⟧₀⁻¹ = {!!}
