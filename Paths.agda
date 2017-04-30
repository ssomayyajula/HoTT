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
  _∘_ : {X : Type ℓ₁}
     → {P : X → Type ℓ₂}
     → {Q : {x : X} → P x → Type ℓ₃}
     → ({x : X} → (px : P x) → Q px)
     → (f : (x : X) → P x)
     → (x : X) → Q (f x)
  (g ∘ f) x = g (f x)
  
  id : {X : Type ℓ₁} → X → X
  id x = x

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
  X × Y = Σ X (λ _ → Y)

open DependentSum


-- Exercise. Complete the recursion and induction principles for
-- Σ. Define curry for functions on dependent sums.
module InductionOnSigma {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  -- recΣ
  uncurry : {Y : Type ℓ₃} → ((x : X) → P x → Y) → (Σ X P → Y)
  uncurry f (x , ux) = f x ux

  indΣ : (Q : Σ X P → Type ℓ₃) → (((x : X) → (ux : P x) → Q (x , ux)))
         → (w : Σ X P) → Q w
  indΣ Q f (x , ux) = f x ux

  curry : {Y : Type ℓ₃} → (Σ X P → Y) → (x : X) → P x → Y
  curry f x ux = f (x , ux)

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

open PathInduction

-- Exercise. Define all of the following twice. The first time using
-- ind=, ind=l or ind=r. The second time using pattern matching.
module _ {ℓ} {X : Type ℓ} where

  infix 100 !
  module Inverse where
    -- ind= definition here
    ! : {x y : X} → x == y → y == x
    ! {x} = ind=l (λ {y} _ → y == x) (refl x)

  -- pattern-matching definition here
  ! : {x y : X} → x == y → y == x
  ! (refl x) = refl x
  

  infixr 80 _◾_
  module PathComposition where
    _◾_ : {x y : X} → x == y → {z : X} → y == z → x == z
    _◾_ {x} = ind=l (λ {y} _ → ∀ {z} → y == z → x == z) (λ p → p)

  _◾_ : {x y : X} → x == y → {z : X} → y == z → x == z
  _◾_ (refl x) (refl .x) = refl x


module _ {ℓ} where

  module Coerce where
    coe : {X Y : Type ℓ} → X == Y → X → Y
    coe {X} = ind=l (λ {Y} _ → X → Y) (λ y → y)

  coe : {X Y : Type ℓ} → X == Y → X → Y
  coe (refl x) y = y


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  module Apply where
    ap : (f : X → Y) → {x y : X} → x == y → f x == f y
    ap f {x} = ind=l (λ {y} _ → f x == f y) (refl (f x))

  ap : (f : X → Y) → {x y : X} → x == y → f x == f y
  ap f (refl x) = refl (f x)


module _ {ℓ} {X : Type ℓ} where

  -- Notice that all of these laws are in fact functions taking a path
  -- of dimension n and returning a path of dimension (n + 1).

  module PathCompositionRightUnit where
    ◾unitr : {x y : X} → (p : x == y) → p ◾ refl y == p
    ◾unitr {x} {y} = ind=r (λ p → p ◾ refl y == p) (refl (refl y))

  ◾unitr : {x y : X} → (p : x == y) → p ◾ refl y == p
  ◾unitr (refl x) = refl (refl x)

  module PathCompositionLeftUnit where
    ◾unitl : {x y : X} → (p : x == y) → refl x ◾ p == p
    ◾unitl {x} = ind=l (λ p → refl x ◾ p == p) (refl (refl x))

  ◾unitl : {x y : X} → (p : x == y) → refl x ◾ p == p
  ◾unitl (refl x) = refl (refl x)

  module PathCompositionLeftInverse where
    ◾invl : {x y : X} → (p : x == y) → ! p ◾ p == refl y
    ◾invl {_} {y} = ind=r (λ p → ! p ◾ p == refl y) (refl (refl y))

  ◾invl : {x y : X} → (p : x == y) → ! p ◾ p == refl y
  ◾invl (refl y) = refl (refl y)

  module PathCompositionRightInverse where
    ◾invr : {x y : X} → (p : x == y) → p ◾ ! p == refl x
    ◾invr {x} {_} = ind=l (λ p → p ◾ ! p == refl x) (refl (refl x))

  ◾invr : {x y : X} → (p : x == y) → p ◾ ! p == refl x
  ◾invr (refl x) = refl (refl x)

  module InverseInverseIsId where
    !! : {x y : X} → (p : x == y) → ! (! p) == p
    !! {x} {_} = ind=l (λ p → ! (! p) == p) (refl (refl x))

  !! : {x y : X} → (p : x == y) → ! (! p) == p
  !! (refl x) = refl (refl x)

  module InverseCommutesWithDoubleInverse where
    !!! : {x y : X} → (p : x == y) → ap ! (!! p) == !! (! p)
    !!! {x} {_} = ind=l (λ p → ap ! (!! p) == !! (! p)) (refl (refl (refl x)))

  !!! : {x y : X} → (p : x == y) → ap ! (!! p) == !! (! p)
  !!! (refl x) = refl (refl (refl x))

  module InverseAntiDistOverPathComp where
    !◾ : {x y z : X} → (p : x == y) → (q : y == z) → ! (p ◾ q) == ! q ◾ ! p
    !◾ {x} {_} {_} = ind=l (λ p → ∀ q → ! (p ◾ q) == ! q ◾ ! p)
                       (ind=l (λ q → ! (refl x ◾ q) == ! q ◾ ! (refl x)) (refl (refl x)))

  !◾ : {x y z : X} → (p : x == y) → (q : y == z) → ! (p ◾ q) == ! q ◾ ! p
  !◾ (refl x) (refl .x) = refl (refl x)

module Ind=' {ℓ} {X : Type ℓ} where
  ind=' : (P : {x y : X} → x == y → Type ℓ)
             → ((x : X) → P (refl x))
             → {x y : X} → (p : x == y) → P p
  ind=' P r {_} {y} = ind=r P (r y)

module Ind=r' {ℓ} {X : Type ℓ} where
  ind=r' : {y : X} → (P : (x : X) → (p : y == x) → Type ℓ)
         → P y (refl y)
         → {x : X} → (p : y == x) → P x p
  ind=r' P r p = ind= (λ {x} {y} p → ∀ (P : (z : X) → x == z → Type ℓ) → P x (refl x) → P y p) (λ _ _ d → d) p P r

{-module _ {ℓ} {X : Type ℓ} {a b c d : X} where
  ◾assoc : (p : a == b) (q : b == c) (r : c == d) → p ◾ (q ◾ r) == (p ◾ q) ◾ r
  ◾assoc (refl a) (refl _) (refl _) = refl (refl a)-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

{- The type of pointed types in the ℓth universe -}
Pointed : ∀ ℓ → Type (lsuc ℓ)
Pointed ℓ = Σ (Type ℓ) (λ A → A)

{- n-fold iterated loop space -} 
Ω : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
Ω 0       (A , a) = (A , a)
Ω (suc n) (A , a) = Ω n ((a == a) , refl a)

ΩS : ∀ {ℓ} → ℕ → Pointed ℓ → Type ℓ
ΩS n X = p₁ (Ω n X)

infix  2  _∎      -- equational reasoning
infixr 2  _==⟨_⟩_  -- equational reasoning

_==⟨_⟩_ : ∀ {ℓ} → {A : Type ℓ} (x : A) {y z : A} → x == y → y == z → x == z
_ ==⟨ p ⟩ q = p ◾ q 

_∎ : ∀ {ℓ} → {A : Type ℓ} (x : A) → x == x
_∎ x = refl x

module EckmannHilton {ℓ : Level} where
  {- Just definitions from the book... -}
  module Whiskering {X : Type ℓ} {a b c : X} where
    module RightWhisker {p q : a == b} where
      _◾ᵣ_ : (α : p == q) → (r : b == c) → p ◾ r == q ◾ r
      α ◾ᵣ refl _ = ◾unitr p ◾ α ◾ ! (◾unitr q)
    module LeftWhisker {r s : b == c} where
      _◾ₗ_ : (q : a == b) (β : r == s) → q ◾ r == q ◾ s
      refl _ ◾ₗ β = ◾unitl r ◾ β ◾ ! (◾unitl s)

  open Whiskering.LeftWhisker
  open Whiskering.RightWhisker
  
  module HorizontalComposition {X : Type ℓ} {a b c : X} {p q : a == b} {r s : b == c} where
    infixr 80 _★_
    _★_ : (α : p == q) → (β : r == s) → p ◾ r == q ◾ s
    α ★ β = (α ◾ᵣ r) ◾ (q ◾ₗ β)

    infixr 80 _★'_
    _★'_ : (α : p == q) → (β : r == s) → p ◾ r == q ◾ s
    α ★' β = (p ◾ₗ β) ◾ (α ◾ᵣ s)

  open HorizontalComposition

  module _ {X : Type ℓ} {a : X} where
    ★==◾ : (α β : refl a == refl a) → α ★ β == α ◾ β
    ★==◾ α β = α ★ β
                  ==⟨ refl _ ⟩
                (α ◾ᵣ refl a) ◾ (refl a ◾ₗ β)
                  ==⟨ refl _ ⟩
                (◾unitr (refl a) ◾ α ◾ ! (◾unitr (refl a))) ◾
                  (◾unitl (refl a) ◾ β ◾ ! (◾unitl (refl a)))
                  ==⟨ refl _ ⟩
                (refl (refl a) ◾ (α ◾ refl (refl a))) ◾
                  (refl (refl a) ◾ (β ◾ refl (refl a)))
                  ==⟨ ap (λ x → (_ ◾ x) ◾ _) (◾unitr α) ⟩
                (refl (refl a) ◾ α) ◾ (refl (refl a) ◾ (β ◾ refl (refl a)))
                  ==⟨ ap (λ x → x ◾ _) (◾unitl α) ⟩
                α ◾ (refl (refl a) ◾ β ◾ refl (refl a))
                  ==⟨ ap (λ x → _ ◾ (_ ◾ x)) (◾unitr β) ⟩
                α ◾ (refl (refl a) ◾ β)
                  ==⟨ ap (λ x → _ ◾ x) (◾unitl β) ⟩
                (α ◾ β ∎)
    
    ★'==◾ : (α β : refl a == refl a) → α ★' β == β ◾ α
    ★'==◾ α β = α ★' β
                   ==⟨ refl _ ⟩
                 (refl a ◾ₗ β) ◾ (α ◾ᵣ refl a)
                   ==⟨ refl _ ⟩
                 (◾unitl (refl a) ◾ β ◾ ! (◾unitl (refl a))) ◾
                   (◾unitr (refl a) ◾ α ◾ ! (◾unitr (refl a)))
                   ==⟨ refl _ ⟩
                 (refl (refl a) ◾ (β ◾ refl (refl a))) ◾
                   (refl (refl a) ◾ (α ◾ refl (refl a)))
                   ==⟨ ap (λ x → (_ ◾ x) ◾ _) (◾unitr β) ⟩
                 (refl (refl a) ◾ β) ◾ (refl (refl a) ◾ (α ◾ refl (refl a)))
                   ==⟨ ap (λ x → x ◾ _) (◾unitl β) ⟩
                 β ◾ (refl (refl a) ◾ (α ◾ refl (refl a)))
                   ==⟨ ap (λ x → _ ◾ (_ ◾ x)) (◾unitr α) ⟩
                 β ◾ (refl (refl a) ◾ α)
                   ==⟨ ap (λ x → _ ◾ x) (◾unitl α) ⟩
                 (β ◾ α ∎)

    {- Refl. Refl? Refl! -}
    ★==★' : {a b : X} → {p q : a == b} → (α : p == q)
          → {c : X} → {r s : b == c} → (β : r == s)
          → α ★ β == α ★' β
    ★==★' {a} {b} {p} = ind=l P f
      where P : {q : a == b} → p == q → Type ℓ
            P α = {c : X} → {r s : b == c} → (β : r == s) → α ★ β == α ★' β
            f : {c : X} → {r s : b == c} → (β : r == s) → refl p ★ β == refl p ★' β
            f {c} {r} = ind=l (λ β → refl p ★ β == refl p ★' β)
                          (ind=l (λ r → refl p ★ refl r == refl p ★' refl r)
                            (ind=l (λ {b} p → refl p ★ refl (refl b) == refl p ★' refl (refl b))
                              ((refl (refl (refl a)))) p) r)
 
    eckmann-hilton : (α β : refl a == refl a) → α ◾ β == β ◾ α
    eckmann-hilton α β = α ◾ β
                      ==⟨ ! (★==◾ α β) ⟩
                         α ★ β
                      ==⟨ ★==★' α β ⟩
                         α ★' β
                      ==⟨ ★'==◾ α β ⟩
                         (β ◾ α ∎)
