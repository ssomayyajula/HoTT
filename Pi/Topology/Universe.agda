{-# OPTIONS --without-K --rewriting  --allow-unsolved-metas #-}

module Pi.Topology.Universe where

open import lib.Basics
open import lib.types.Truncation

open import Pi.Topology.Equivalence using (ua-ide)

U[_] : Type₀ → Type₁
U[ X ] = Σ Type₀ (λ Y → Trunc -1 (Y == X))

`_ : (X : Type₀) → U[ X ]
` X = X , [ idp ]

module _ {X} where
  ~ : {A B : U[ X ]} → fst A ≃ fst B → A == B
  ~ e = pair= (ua e) $ from-transp _ _ $ prop-has-all-paths Trunc-level _ _

  --postulate
  ~ide=idp : {A : U[ X ]} → ~ {A} (ide (fst A)) == idp
  ~ide=idp {A} = ap (λ x → pair= x (from-transp _ _ (prop-has-all-paths Trunc-level _ _))) (ua-ide (fst A)) ∙
    {!!}
