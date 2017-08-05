{-# OPTIONS --without-K --rewriting #-}

module HITProofs where

open import UnivalentTypeTheory

open import S1
open import Suspension

open import Reversible.Utils

Σ𝟚≃S¹ : Susp 𝟚 ≃ S¹
Σ𝟚≃S¹ = f , qinv-is-equiv (g ,
  indSusp _ (refl north) (merid 1₂) (λ y →
    tpt (λ x → g (f x) == id x) (merid y) (refl north)
      ==⟨ tpt-paths (g ∘ f) id (merid y) (refl north) ⟩
    ! (ap (g ∘ f) (merid y)) ◾ refl north ◾ ap id (merid y)
      ==⟨ ap (λ p → ! (ap (g ∘ f) (merid y)) ◾ refl north ◾ p) (ap-id (merid y)) ⟩
    ! (ap (g ∘ f) (merid y)) ◾ refl north ◾ merid y
      ==⟨ ap (λ p → ! p ◾ refl north ◾ merid y) (ap∘ g f (merid y)) ⟩
    ! (ap g (ap f (merid y))) ◾ refl north ◾ merid y
      ==⟨ ap (! (ap g (ap f (merid y))) ◾-) (◾unitl (merid y)) ⟩
    ! (ap g (ap f (merid y))) ◾ merid y
      ==⟨ ind𝟚 (λ y → ! (ap g (ap f (merid y))) ◾ merid y == merid 1₂)
            (! (ap g (ap f (merid 0₂))) ◾ merid 0₂
               ==⟨ ap (λ p → ! (ap g p) ◾ merid 0₂) (RecSusp.merid-β _ _ _ _ 0₂) ⟩
             ! (ap g loop) ◾ merid 0₂
               ==⟨ ap (λ p → ! p ◾ merid 0₂) (RecS¹.loop-β _ _ _ ) ⟩
             ! (merid 0₂ ◾ ! (merid 1₂)) ◾ merid 0₂
               ==⟨ ap (-◾ merid 0₂) (!◾ (merid 0₂) (! (merid 1₂))) ⟩
             (! (! (merid 1₂)) ◾ ! (merid 0₂)) ◾ merid 0₂
               ==⟨ ◾assoc (! (! (merid 1₂))) (! (merid 0₂)) (merid 0₂) ⟩
             ! (! (merid 1₂)) ◾ ! (merid 0₂) ◾ merid 0₂
               ==⟨ ap (! (! (merid 1₂)) ◾-) (◾invl (merid 0₂)) ⟩
             ! (! (merid 1₂)) ◾ refl south
               ==⟨ ◾unitr (! (! (merid 1₂))) ⟩
             ! (! (merid 1₂))
               ==⟨ !! (merid 1₂) ⟩
             (merid 1₂ ∎))
            (! (ap g (ap f (merid 1₂))) ◾ merid 1₂
               ==⟨ ap (λ p → ! (ap g p) ◾ merid 1₂) (RecSusp.merid-β _ _ _ _ 1₂) ⟩
             ! (ap g (refl base)) ◾ merid 1₂
               ==⟨ refl _ ⟩
             refl north ◾ merid 1₂
               ==⟨ ◾unitl _ ⟩
             (merid 1₂ ∎))
            y ⟩
    (merid 1₂ ∎)) ,
  indS¹ _ (refl base) (
    tpt (λ x → f (g x) == id x) loop (refl base)
      ==⟨ tpt-paths (f ∘ g) id loop (refl base) ⟩
    ! (ap (f ∘ g) loop) ◾ refl base ◾ ap id loop
      ==⟨ ap (λ p → ! (ap (f ∘ g) loop) ◾ refl base ◾ p) (ap-id loop) ⟩
    ! (ap (f ∘ g) loop) ◾ refl base ◾ loop
      ==⟨ ap (λ p → ! p ◾ refl base ◾ loop) (ap∘ f g loop) ⟩
    ! (ap f (ap g loop)) ◾ refl base ◾ loop
      ==⟨ ap (! (ap f (ap g loop)) ◾-) (◾unitl loop) ⟩
    ! (ap f (ap g loop)) ◾ loop
      ==⟨ ap (λ p → ! (ap f p) ◾ loop) (RecS¹.loop-β _ _ _) ⟩
    ! (ap f (merid 0₂ ◾ ! (merid 1₂))) ◾ loop
      ==⟨ ap (λ p → ! p ◾ loop) (ap◾ f (merid 0₂) (! (merid 1₂))) ⟩
    ! (ap f (merid 0₂) ◾ ap f (! (merid 1₂))) ◾ loop
      ==⟨ ap (λ p → ! (ap f (merid 0₂) ◾ p) ◾ loop) (ap! f (merid 1₂)) ⟩
    ! (ap f (merid 0₂) ◾ ! (ap f (merid 1₂))) ◾ loop
      ==⟨ ap (λ p → ! (p ◾ ! (ap f (merid 1₂))) ◾ loop) (RecSusp.merid-β _ _ _ _ 0₂) ⟩
    ! (loop ◾ ! (ap f (merid 1₂))) ◾ loop
      ==⟨ ap (λ p → ! (loop ◾ ! p) ◾ loop) (RecSusp.merid-β _ _ _ _ 1₂) ⟩
    ! (loop ◾ ! (refl base)) ◾ loop
      ==⟨ ap (-◾ loop) (!◾ loop (! (refl base))) ⟩
    (! (! (refl base)) ◾ (! loop)) ◾ loop
      ==⟨ ◾assoc (! (! (refl base))) (! loop) loop ⟩
    ! (! (refl base)) ◾ (! loop) ◾ loop
      ==⟨ ap (_ ◾-) (◾invl loop) ⟩
    ! (! (refl base)) ◾ refl base
      ==⟨ ◾unitr _ ⟩
    ! (! (refl base))
      ==⟨ !! _ ⟩
    (refl base ∎))) where

  f : Susp 𝟚 → S¹
  f = recSusp _ base base (rec𝟚 _ loop (refl base))

  g : S¹ → Susp 𝟚
  g = recS¹ _ north (merid 0₂ ◾ ! (merid 1₂))
