{-# OPTIONS --without-K --rewriting #-}

module Pi.Topology.KS21 where

open import lib.Basics using (Type; Type₀; Type₁; cst; _==_; idp; Σ; _,_; _≃_; equiv; has-level)
open import lib.types.Truncation using (Trunc; [_]; Trunc-level; Trunc-rec)
open import lib.types.TLevel using (⟨_⟩)
open import lib.types.Bool using (Bool; Bool-is-set)
open import lib.types.Group using (Group; group)
open import lib.groups.Homomorphism using (group-hom)
open import lib.types.EilenbergMacLane1

open import Pi.Topology.SymmetricGroup

M : Type₁
M = Σ Type₀ (λ X → Trunc ⟨ 1 ⟩ (X == Bool)) 

T : Type₀
T = EM₁ (S Bool Bool-is-set)

-- TODO: Show that 3-paths are trivial, TwoUniverse style
M-level : has-level ⟨ 1 ⟩ M
M-level = {!!}

model-is-em : M ≃ T
model-is-em = equiv f g {!!} {!!} where
  f : M → T
  f (_ , p) = Trunc-rec EM₁-level (cst embase) p
  
  g : T → M
  g = EM₁-rec M-level (Bool , [ idp ]) (group-hom {!!} {!!})
