{-# OPTIONS --without-K --rewriting #-}

module Pi.Topology.X where

open import lib.Basics
open import lib.types.Bool 

f : Bool → Bool
f false = {!!}
f true = false

g : Bool → Bool
g false = false
g true = {!!}

α : ∀ b → f (g b) == b
α false = idp 
α true = idp 

