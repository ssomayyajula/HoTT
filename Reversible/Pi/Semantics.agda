module Reversible.Pi.Semantics where

open import Type using (Type₀)
open import One using (𝟙)
open import Zero using (𝟘)

open import Paths
open import DependentSum using (Σ; _×_; _,_)
open import Coproduct
open import Functions using (_∘_)
open import Equivalences
open import Univalence
open import PathsInSigma

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; inject+)
open import Data.Vec
--open import Agda.Builtin.Equality using (subst)

open import Reversible.Pi.Syntax
open import Reversible.Pi.FinUniverse
open import Reversible.UnivalentFibrations
open import Reversible.Pi.AFin
open import Reversible.Pi.CPerm

⟦_⟧ₜ : U → Type₀
⟦ ZERO ⟧ₜ        = 𝟘
⟦ ONE  ⟧ₜ        = 𝟙
⟦ PLUS  t₁ t₂ ⟧ₜ = ⟦ t₁ ⟧ₜ + ⟦ t₂ ⟧ₜ
--⟦ TIMES t₁ t₂ ⟧ₜ = ⟦ t₁ ⟧ₜ × ⟦ t₂ ⟧ₜ

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧ₜ ≃ ⟦ Y ⟧ₜ
⟦ unite₊l ⟧₁ = (λ { (i₁ ()); (i₂ x) → x }) , qinv-is-equiv (i₂ , (λ { (i₁ ()); (i₂ x) → refl (i₂ x) }) , refl)
⟦ uniti₊l ⟧₁ = !e ⟦ unite₊l ⟧₁
⟦ _ ⟧₁ = {!!}

⟦_⟧ₚ : {X Y : U} → X ⟷ Y → CPerm (size X) (size Y)
⟦ _ ⟧ₚ = {!!}

cmpl1-lem : {X Y : U} → (p : CPerm (size X) (size Y)) → Σ (X ⟷ Y) (λ `p → ⟦ `p ⟧ₚ == p)
cmpl1-lem = {!!}

{-norm : (X : U) → ⟦ X ⟧ₜ ≃ Fin (size X)
norm ZERO = {!!}
norm ONE = {!!}
norm _ = {!!}-}

{-# TERMINATING #-}
comm : (m n : ℕ) → Data.Nat._+_ m n == Data.Nat._+_ n m
comm 0 0 = refl 0
comm 0 (suc n) = {!!}
comm (suc m) 0 = ! (comm 0 (suc m))
comm (suc m) (suc n) = {!!}

norm : (X : U) → ⟦ X ⟧ₜ ≃ Fin (size X)
norm ZERO = {!!}
norm ONE = {!!} --(i₁ , qinv-is-equiv ((λ { (i₁ x) → x; (i₂ ()) }) , refl , (λ { (i₁ x) → refl (i₁ x); (i₂ ()) })))
norm (PLUS X Y) = let (fx , ex) = norm X in
                  let (fy , ey) = norm Y in
                  let (gx , εx , ηx) = hae-is-qinv ex in
                  let (gy , εy , ηy) = hae-is-qinv ey in
                  (λ { (i₁ x) → inject+ (size Y) (fx x);
                       (i₂ y) → let l = inject+ (size X) (fy y) in {!!} }) ,
                  qinv-is-equiv ({!!} , {!!} , {!!})

cmpl1 : {X Y : U} → (p : ⟦ X ⟧ₜ ≃ ⟦ Y ⟧ₜ) → Σ (X ⟷ Y) (λ `p → ⟦ `p ⟧₁ == p)
cmpl1 p with cmpl1-lem (equiv-to-perm ({!!} p)) -- use norm
...   | (`p , e) = (`p , {!!})

{-
cmpl1 : {X Y : U} → (p : ⟦ X ⟧ₜ ≃ ⟦ Y ⟧ₜ) → Σ (X ⟷ Y) (λ `p → ⟦ `p ⟧₁ == p)
cmpl1 (f , g , ε , η , τ) with cmpl1-lem (equiv-to-perm {!!}) -- use norm
...     | (`p , e) = (`p , {!!})
-}
