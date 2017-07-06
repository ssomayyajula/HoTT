module Reversible.Pi.Semantics where

open import Type using (Type; Type₀)
open import One using (𝟙; 0₁)
open import Zero using (𝟘; rec𝟘)

open import Paths using (_==_; refl; _◾_)
open import DependentSum using (Σ; _×_; _,_; p₁; p₂)
open import Coproduct using (_+_)
open import Functions using (_∘_)
open import Equivalences using (_≃_; qinv-is-equiv)
open import Univalence using (ua)

open import Data.Nat using (ℕ; zero; suc; _*_; _≤_; s≤s; z≤n)
open import Data.Fin using (Fin; inject+; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)

open import Reversible.Pi.Syntax
open import Reversible.Pi.FinUniverse using (all-1-paths-fin)
--open import Reversible.UnivalentFibrations
open import Reversible.Pi.CPerm using (CPerm)

-- Write types for translations and manual inverses

-- (T : U) → Σ Type₀ (λ X → ∥ X == Fin (size T) ∥)
⟦_⟧ₜ : U → Type₀
⟦ ZERO ⟧ₜ        = 𝟘
⟦ ONE  ⟧ₜ        = 𝟙
⟦ PLUS  t₁ t₂ ⟧ₜ = ⟦ t₁ ⟧ₜ + ⟦ t₂ ⟧ₜ
⟦ TIMES t₁ t₂ ⟧ₜ = ⟦ t₁ ⟧ₜ × ⟦ t₂ ⟧ₜ

fromSize : ℕ → U
fromSize 0       = ZERO
fromSize (suc n) = PLUS ONE (fromSize n)

canonicalU : U → U
canonicalU = fromSize ∘ size

size+ : (n₁ n₂ : ℕ) → PLUS (fromSize n₁) (fromSize n₂) ⟷ fromSize (Data.Nat._+_ n₁ n₂)
size+ 0        n₂ = unite₊l
size+ (suc n₁) n₂ = assocr₊ ◎ (id⟷ ⊕ size+ n₁ n₂)

size* : (n₁ n₂ : ℕ) → TIMES (fromSize n₁) (fromSize n₂) ⟷ fromSize (n₁ * n₂)
size* 0        n₂ = absorbr
size* (suc n₁) n₂ = dist ◎ ((unite⋆l ⊕ size* n₁ n₂) ◎ size+ n₂ (n₁ * n₂))

normalizeC : (t : U) → t ⟷ canonicalU t
normalizeC ZERO = id⟷
normalizeC ONE  = uniti₊l ◎ swap₊
normalizeC (PLUS t₀ t₁) =
  (normalizeC t₀ ⊕ normalizeC t₁) ◎ size+ (size t₀) (size t₁) 
normalizeC (TIMES t₀ t₁) =
  (normalizeC t₀ ⊗ normalizeC t₁) ◎ size* (size t₀) (size t₁) 

data Transposition (n : ℕ) : Type₀ where
  _X_ : (i j : Fin n) → {p : toℕ i ≤ toℕ j} → Transposition n

Transposition* : ℕ → Set
Transposition* n = List (Transposition n)

swapFin : {n : ℕ} → (a b : Fin n) → (leq : toℕ a ≤ toℕ b) → fromSize n ⟷ fromSize n
swapFin fzero fzero z≤n = id⟷
swapFin fzero (fsuc fzero) z≤n = assocl₊ ◎ ((swap₊ ⊕ id⟷) ◎ assocr₊)
swapFin fzero (fsuc (fsuc b)) z≤n =
  (assocl₊ ◎ ((swap₊ ⊕ id⟷) ◎ assocr₊)) ◎
  ((id⟷ ⊕ swapFin fzero (fsuc b) z≤n) ◎
  (assocl₊ ◎ ((swap₊ ⊕ id⟷) ◎ assocr₊)))
swapFin (fsuc a) fzero ()
swapFin (fsuc a) (fsuc b) (s≤s leq) = id⟷ ⊕ swapFin a b leq 

-- permutation to combinator

transposition*2c : (m n : ℕ) (m≡n : m == n) → Transposition* m → fromSize m ⟷ fromSize n
transposition*2c m n (refl _) [] = id⟷ 
transposition*2c m n (refl _) (_X_ i j {leq} ∷ π) =
  swapFin i j leq ◎ transposition*2c n n (refl _) π

-- https://groupprops.subwiki.org/wiki/Transpositions_generate_the_finitary_symmetric_group
postulate
  trans-perm-equiv : {m n : ℕ} {p : m == n} → Transposition* m ≃ CPerm m n

perm-to-trans : {m n : ℕ} {p : m == n} → CPerm m n → Transposition* m
perm-to-trans {p = p} = p₁ (p₂ (trans-perm-equiv {p = p}))

reify : {m n : ℕ} {p : m == n} → CPerm m n → fromSize m ⟷ fromSize n
reify {m} {n} {p} π = transposition*2c m n p (perm-to-trans {p = p} π)

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ _ ⟧₁ = {!!}

fromSize∘size : (X : U) → fromSize (size X) ⟷ X
fromSize∘size ZERO = id⟷
fromSize∘size ONE = unite₊r
fromSize∘size (PLUS t₁ t₂) = ! (size+ (size t₁) (size t₂)) ◎ (fromSize∘size t₁ ⊕ fromSize∘size t₂)
fromSize∘size (TIMES t₁ t₂) = ! (size* (size t₁) (size t₂)) ◎ (fromSize∘size t₁ ⊗ fromSize∘size t₂)

postulate
  norm : (X : U) → ⟦ X ⟧ₜ ≃ Fin (size X)
  size-eq : {X Y : U} → ⟦ X ⟧ₜ == ⟦ Y ⟧ₜ → size X == size Y


cmpl1 : {X Y : U} → (p : ⟦ X ⟧ₜ == ⟦ Y ⟧ₜ) → Σ (X ⟷ Y) (λ `p → ua ⟦ `p ⟧₁ == p)
cmpl1 {X = X} {Y} p with all-1-paths-fin (Paths.! (⟦ normalizeC X ⟧₁ ◾ ua (norm (canonicalU X))) ◾ p ◾ ⟦ normalizeC Y ⟧₁ ◾ ua (norm (canonicalU Y)))
...                 | (p' , e) = (! (fromSize∘size X) ◎ ((reify p') ◎ (fromSize∘size Y))) , {!!}

{-⟦ ZERO ⟧₀ = Fin 0 , ∣ refl (Fin 0) ∣
⟦ ONE ⟧₀ = Fin 1 , ∣ refl (Fin 1)  ∣
⟦ PLUS t₁ t₂ ⟧₀ = Fin (size t₁ + size t₂)-}
{-⟦ T@(PLUS t₁ t₂) ⟧₀ with ⟦ t₁ ⟧₀ | ⟦ t₂ ⟧₀
... | (t₁' , p₁) | (t₂' , p₂) = t₁' + t₂' , recTrunc _ (λ p₁' → recTrunc _ (λ p₂' → ∣ f p₁' p₂' ∣) identify p₂) identify p₁ where
  f : t₁' == Fin (size t₁) → t₂' == Fin (size t₂) → t₁' + t₂' == Fin (size T)
  f (refl _) (refl _) = {!!}
⟦ T@(TIMES t₁ t₂) ⟧₀ with ⟦ t₁ ⟧₀ | ⟦ t₂ ⟧₀
... | (t₁' , p₁) | (t₂' , p₂) = t₁' × t₂' , recTrunc _ (λ p₁' → recTrunc _ (λ p₂' → ∣ f p₁' p₂' ∣) identify p₂) identify p₁ where
  f : t₁' == Fin (size t₁) → t₂' == Fin (size t₂) → t₁' × t₂' == Fin (size T)
  f (refl _) (refl _) = {!!}-}
{-
⟦_⟧₀⁻¹ : {n : ℕ} → U[ Fin n ] → U
⟦ (t , |p|) ⟧₀⁻¹ = 

size= : {X Y : U} → X ⟷ Y → size X == size Y
size= unite₊l = refl _
size= assocl⋆ = {!!} -- associativity of multiplication, etc.
size= = {!!}

PathOverPi1 : (X Y : U) (c : size X == size Y) → Type₁
PathOverPi1 X Y c = tpt (U[_] ∘ Fin) c ⟦ X ⟧₀ == ⟦ Y ⟧₀

syntax PathOverPi1 X Y c = X =[ c ]= Y

⟦_⟧₁ : {X Y : U} → (c : X ⟷ Y) → X =[ size= c ]= Y
⟦ unite₊l ⟧₁ = refl _
⟦ assocl₊ ⟧₁ = {!!}
⟦ _ ⟧₁ = {!!}

-- ⟦_⟧₂ : {X Y : U} {p q : X ⟷ Y} → p ⇔ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
-- ⟦_⟧₃ : {X Y : U} {p q : X ⟷ Y} {α β : p ⇔ q} → ⟦ α ⟧₂ == ⟦ β ⟧₂ by truncation


-- Rewrite all-1-paths in terms of (p : m == n) → tpt Fin p m == Fin n
⟦_⟧₁⁻¹ : {m n : ℕ} {X : U[Fin m]} {Y : U[  ]} =[ c ]= Y → X ⟷ Y
⟦_⟧₁⁻¹ with all-1-paths {!!}
...          | _ = {!!}
-}
