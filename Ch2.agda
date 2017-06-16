{-# OPTIONS --without-K #-}

module Chapter2 where

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

module Functions {ℓ₁ ℓ₂ ℓ₃} where

  infixr 80 _∘_
  _∘_ : {X : Type ℓ₁}
     → {P : X → Type ℓ₂}
     → {Q : {x : X} → P x → Type ℓ₃}
     → ({x : X} → (px : P x) → Q px)
     → (f : (x : X) → P x)
     → (x : X) → Q (f x)
  (g ∘ f) x = g (f x)

module _ {ℓ} {X : Type ℓ} where
  id : X → X
  id x = x

open Functions

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

module PathType {ℓ} where

  infixr 30 _==_
  data _==_ {X : Type ℓ} : X → X → Type ℓ where
    refl : (x : X) →  x == x

  infixr 80 _◾_
  _◾_ : {X : Type ℓ} {x y : X} → x == y → {z : X} → y == z → x == z
  _◾_ (refl x) (refl .x) = refl x

open PathType

module _ {ℓ} where
  coe : {X Y : Type ℓ} → (X == Y) → X → Y
  coe (refl x) y = y

module _ {ℓ} {ℓ'} where
  ap : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → {x y : X} → x == y → f x == f y
  ap f (refl x) = refl (f x)

module _ {ℓ} {ℓ'} {X : Type ℓ} {P : X → Type ℓ'} where
  _~_ : (f g : (x : X) → P x) → Type (ℓ ⊔ ℓ')
  f ~ g = (x : X) → f x == g x 

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  isequiv : (f : A → B) → Type (ℓ ⊔ ℓ')
  isequiv f = Σ (B → A) (λ g → f ∘ g ~ id) × Σ (B → A) (λ h → h ∘ f ~ id)

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  qinv : (f : A → B) → Type (ℓ ⊔ ℓ')
  qinv f = Σ (B → A) (λ g → (f ∘ g ~ id) × (g ∘ f ~ id))

module _ {ℓ}  where
  _≅_ : Type ℓ → Type ℓ → Type ℓ
  A ≅ B = Σ (A → B) isequiv

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} where
  eq-to-qinv : isequiv f → qinv f
  eq-to-qinv ((g , α) , h , β) = {!!}
    {-let γ x = (β (g x)) ◾ (ap h (α x)) in
    let β' x = γ (f x) ◾ β x         in
      g , α , β'-}
  
  qinv-to-eq : qinv f → isequiv f
  qinv-to-eq (g , α , β) = (g , α) , (g , β)

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) -> B x} where
  happly : f == g → f ~ g
  happly (refl f) x = refl (f x)

  postulate
    ext : isequiv happly

  funext : f ~ g → f == g
  funext = p₁ (p₂ ext)

  fun-comp : {h : (x : A) → f x == g x} → happly ∘ funext ~ id
  fun-comp = let inv = eq-to-qinv ext in p₁ (p₂ inv)

  fun-up : {p : f == g} → p == funext (happly p)
  fun-up {p} = let inv = eq-to-qinv ext in {!!}

{-
  postulate
    {- Function extensionality -}
    funext : f ~ g → f == g
    {- Propositional computation rule -}
    comp : {h : (x : A) → f x == g x} → happly (funext h) ~ h
    {- UP -}
    up : {p : f == g} → p == funext (happly p)

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) -> B x} where
  funequiv : (f == g) ≅ (f ~ g)
  funequiv = happly , (funext , comp) , funext , up
-}


{-
module Equiv {ℓ} {A B C : Type ℓ} where
  reflexivity : A ≅ A
  reflexivity = (id , ((id , refl) , (id , refl)))

  sym : A ≅ B → B ≅ A
  sym (f , ((g , h1) , (h , h2))) = (g , ((f , {!!}) , ()))
-}

data _+_ {ℓ} {ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : A → A + B
  inr : B → A + B

module _ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ} {B : Type ℓ'} {P : (A + B) → Type ℓ''} where
  ind-co : ((l : A) → P (inl l)) → ((r : B) → P (inr r)) → (x : (A + B)) → P x
  ind-co f g (inl l) = f l
  ind-co f g (inr r) = g r

data 𝟙 : Type₀ where
  ★ : 𝟙

module _ {ℓ} {P : 𝟙 → Type ℓ} where
  ind-𝟙 : P ★ → (x : 𝟙) → P x
  ind-𝟙 x ★ = x

data 𝟚 : Type₀ where
  t : 𝟚
  f : 𝟚

module _ {ℓ} {P : 𝟚 → Type ℓ} where
  ind-𝟚 : P t → P f → (x : 𝟚) → P x
  ind-𝟚 tt ff t = tt
  ind-𝟚 tt ff f = ff

{- 1 + 1 = 2, but cooler -}
one-plus-one : (𝟙 + 𝟙) ≅ 𝟚
one-plus-one =
  let f1  = ind-co (λ _ → t) (λ _ → f) in
  let inv = ind-𝟚 (inl ★) (inr ★)      in
  (f1 , ((inv , ind-𝟚 (refl t) (refl f)) ,
         (inv , ind-co (ind-𝟙 (refl (inl ★))) (ind-𝟙 (refl (inr ★))))))

module _ {ℓ} {ℓ'} {A : Type ℓ} {x y : A} where
  transport : (P : A → Type ℓ') → x == y → P x → P y
  transport P (refl x) px = px

module _ {ℓ} {A B : Type ℓ} where
  idtoeqv : A == B → A ≅ B
  idtoeqv (refl A) = id , (id , refl) , id , refl

  {- The Univalence Axiom -}
  postulate
    univalence : isequiv idtoeqv

  ua : A ≅ B → A == B
  ua = p₁ (p₂ univalence)

  type-comp : {e : A ≅ B} → transport id (ua e) ~ p₁ e
  type-comp = {!!}

module _ {ℓ} {X : Type ℓ} where
  ! : {x y : X} → x == y → y == x
  ! (refl x) = refl x

{-
{- A computation on the booleans that internally switches to 1 + 1 -}
ex : 𝟚 → 𝟚
ex = let equiv = ua one-plus-one in
  coe (! equiv) (coe equiv (inl ★))
-}
