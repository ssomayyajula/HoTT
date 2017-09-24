{-# OPTIONS --without-K --rewriting #-}

module Pi.Topology.KS21 where

open import lib.Basics using (Type; Type₀; Type₁; cst; _==_; idp; Σ; _,_; pair=; _≃_; equiv; has-level)
open import lib.types.Truncation using (Trunc; [_]; Trunc-level; Trunc-rec)
open import lib.PathOver using (from-transp)
open import lib.types.Bool using (Bool; Bool-level)
open import lib.groups.Homomorphism using (group-hom)
open import lib.types.EilenbergMacLane1

open import Pi.Topology.SymmetricGroup

-- NOT propositional truncation, need to fix
U : Type₁
U = Σ Type₀ (λ X → Trunc 1 (X == Bool)) 

`𝟚 : U
`𝟚 = Bool , [ idp ]

K : Type₀
K = EM₁ (S Bool-level)

-- TODO: Show that 3-paths are trivial, TwoUniverse style
U-level : has-level 1 U
U-level x y x₁ y₁ x₂ y₂ = {!!}

model-is-em : U ≃ K
model-is-em = equiv f g {!!} {!!} where
  f : U → K
  f (_ , p) = Trunc-rec EM₁-level (cst embase) p
  
  g : K → U
  g = EM₁-rec U-level `𝟚 (group-hom {!!} {!!})
