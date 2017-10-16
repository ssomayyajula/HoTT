{-# OPTIONS --without-K --rewriting #-}

module Pi.Topology.KS21 where

open import lib.Basics
open import lib.types.Bool using (Bool; Bool-level)
open import lib.types.Truncation
open import lib.Equivalence2 using (∘e-unit-r)
open import lib.groups.Homomorphism using (group-hom)
open import lib.types.EilenbergMacLane1

open import Pi.Topology.Universe
open import Pi.Topology.TwoUniverse
open import Pi.Topology.Equivalence using (≃-Group; ∘e-unit-l)

K : Type₀
K = EM₁ (≃-Group Bool-level)

model-is-em : U[ Bool ] ≃ K
model-is-em = equiv f g {!!} {!!} where
  f : U[ Bool ] → K
  -- TODO: EM₁-level not compatible with prop truncation
  f (_ , p) = Trunc-rec {!!} (cst embase) p
  
  g : K → U[ Bool ]
  g = EM₁-rec U[Bool]-level (` Bool) (group-hom ~
    (Bool-equiv-induction
      (Bool-equiv-induction
        (ap ~ (∘e-unit-l _) ∙ {!!})
        {!!})
      (Bool-equiv-induction
        {!!}    -- h (not ∘ id)  == h id ∙ h not (easy)
        {!!}))) -- h (not ∘ not) == h not ∙ h not (use not ∘ not == id, `not ∙ `not == `id)

--(ap lift (∘e-lunit _) ∙ ap (λ x → pair= x (from-transp _ _ (prop-has-all-paths Trunc-level _ _))) (ua-ide Bool) ∙ {!!})

{-
((Bool-equiv-induction
        {!!}    -- h (id ∘ id)   == h id ∙ h id (easy)
        {!!}))   -- h (id ∘ not)  == h not ∙ h id (easy))
-}
