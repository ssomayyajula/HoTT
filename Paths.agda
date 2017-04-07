{-# OPTIONS --without-K #-}
module Paths where


---------------------------------------------------------------------------
-- Preamble
---------------------------------------------------------------------------

module Universe where

  {- Agda provides a type universe which is nearly adequate for doing
  HoTT (it's not cumulative). Unfortunately, it is called `Set', a
  word we would reserve to denote 0-types. So we call Set `Type'. I
  would be happy to learn of a way of doing this so that Agda always
  uses the word `Type' instead of `Set'. -}
  
  open import Agda.Primitive public using (Level ; lsuc ; lzero ; _⊔_)

  Type : (ℓ : Level) → Set (lsuc ℓ)
  Type ℓ = Set ℓ

  Type₀ = Type lzero
  Type₁ = Type (lsuc lzero)

open Universe public


-- Exercise. Define dependent function composition and identity.
module Functions {ℓ₁ ℓ₂ ℓ₃} where

  infixr 80 _∘_
  _∘_ : {X : Type ℓ₁} → {P : X → Type ℓ₂}
        → {Q : {x : X} → P x → Type ℓ₃}
        → {!!} → {!!} → {!!}
  g ∘ f = {!!}

  id : {X : Type ℓ₁} → {!!} → {!!}
  id = {!!}

open Functions


-- Exercise. Define cartesian product in terms of Σ.
module DependentSum {ℓ₁ ℓ₂ : Level} where

  infixr 60 _,_
  record Σ (X : Type ℓ₁) (P : X → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
      p₁ : X
      p₂ : P p₁
  open Σ public

  infixr 80 _×_
  _×_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
  X × Y = {!!}

open DependentSum


-- Exercise. Complete the recursion and induction principles for
-- Σ. Define curry for functions on dependent sums.
module InductionOnSigma {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  -- recΣ
  uncurry : {Y : Type ℓ₃} → {!!} → (Σ X P → Y)
  uncurry f (x , ux) = {!!}

  indΣ : (Q : Σ X P → Type ℓ₃) → {!!}
         → (w : Σ X P) → Q w
  indΣ Q f (x , ux) = {!!}

  curry : {!!}
  curry = {!!}

open InductionOnSigma

---------------------------------------------------------------------------
---------------------------------------------------------------------------


module PathType {ℓ} where

  infixr 30 _==_
  data _==_ {X : Type ℓ} : X → X → Type ℓ where
    refl : (x : X) →  x == x 

open PathType


module PathInduction {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  ind= : (P : {x y : X} → (p : x == y) → Type ℓ₂)
         → ((x : X) → P (refl x))
         → {x y : X} → (p : x == y) → P p
  ind= P r (refl x) = r x 

  ind=l : {x : X} → (P : {y : X} → (p : x == y) → Type ℓ₂)
          → P (refl x)
          → {y : X} → (p : x == y) → P p
  ind=l P r (refl x) = r

  ind=r : {y : X} → (P : {x : X} → (p : x == y) → Type ℓ₂)
          → P (refl y)
          → {x : X} → (p : x == y) → P p
  ind=r P r (refl x) = r


-- Exercise. Define all of the following twice. The first time using
-- ind=, ind=l or ind=r. The second time using pattern matching.
module _ {ℓ} {X : Type ℓ} where

  infix 100 !
  module Inverse where
    -- ind= definition here
    ! : {x y : X} → x == y → y == x
    ! = {!!}

  -- pattern-matching definition here
  ! : {x y : X} → x == y → y == x
  ! = {!!}
  

  infixr 80 _◾_
  module PathComposition where
    _◾_ : {x y : X} → x == y → {z : X} → y == z → x == z
    _◾_ = {!!}

  _◾_ : {x y : X} → x == y → {z : X} → y == z → x == z
  _◾_ = {!!}


module _ {ℓ} where

  module Coerce where
    coe : {X Y : Type ℓ} → X == Y → X → Y
    coe = {!!}

  coe : {X Y : Type ℓ} → X == Y → X → Y
  coe = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  module Apply where
    ap : (f : X → Y) → {x y : X} → x == y → f x == f y
    ap = {!!}

  ap : (f : X → Y) → {x y : X} → x == y → f x == f y
  ap = {!!}


module _ {ℓ} {X : Type ℓ} where

  -- Notice that all of these laws are in fact functions taking a path
  -- of dimension n and returning a path of dimension (n + 1).

  module PathCompositionRightUnit where
    ◾unitr : {x y : X} → (p : x == y) → p ◾ refl y == p
    ◾unitr = {!!}

  ◾unitr : {x y : X} → (p : x == y) → p ◾ refl y == p
  ◾unitr = {!!}

  module PathCompositionLeftUnit where
    ◾unitl : {x y : X} → (p : x == y) → {!!}
    ◾unitl = {!!}

  ◾unitl : {x y : X} → (p : x == y) → {!!}
  ◾unitl = {!!}

  module PathCompositionLeftInverse where
    ◾invl : {x y : X} → (p : x == y) → ! p ◾ p == refl y
    ◾invl = {!!}

  ◾invl : {x y : X} → (p : x == y) → ! p ◾ p == refl y
  ◾invl = {!!}

  module PathCompositionRightInverse where
    ◾invr : {x y : X} → (p : x == y) → {!!}
    ◾invr = {!!}

  ◾invr : {x y : X} → (p : x == y) → {!!}
  ◾invr = {!!}

  module InverseInverseIsId where
    !! : {x y : X} → (p : x == y) → ! (! p) == p
    !! = {!!}

  !! : {x y : X} → (p : x == y) → ! (! p) == p
  !! = {!!}

  module InverseCommutesWithDoubleInverse where
    !!! : {x y : X} → (p : x == y) → ap ! (!! p) == !! (! p)
    !!! = {!!}

  !!! : {x y : X} → (p : x == y) → ap ! (!! p) == !! (! p)
  !!! = {!!}

  module InverseAntiDistOverPathComp where
    !◾ : {x y z : X} → (p : x == y) → (q : y == z) → ! (p ◾ q) == ! q ◾ ! p
    !◾ = {!!}

  !◾ : {x y z : X} → (p : x == y) → (q : y == z) → ! (p ◾ q) == ! q ◾ ! p
  !◾ = {!!}

