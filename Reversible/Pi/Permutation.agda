module Reversible.Pi.Permutation where

open import UnivalentTypeTheory
open import Reversible.Pi.AFin

infix  2  _∎      -- equational reasoning
infixr 2  _==⟨_⟩_  -- equational reasoning

_==⟨_⟩_ : ∀ {ℓ} → {A : Type ℓ} (x : A) {y z : A} → x == y → y == z → x == z
_ ==⟨ p ⟩ q = p ◾ q 

_∎ : ∀ {ℓ} → {A : Type ℓ} (x : A) → x == x
_∎ x = refl x

{-
mutual
  data Unique {ℓ} : Set ℓ → Set ℓ where
    nil   : {A : Set ℓ} → Unique A
    _:::_ : {A : Set ℓ} (x : A) (l : Unique A) {_ : ¬ (x ∈ l)} → Unique A

  _∈_ : ∀ {ℓ} {A : Set ℓ} → A → Unique A → Set
  y ∈ nil               = 𝟘
  y ∈ (x ::: _) with 0
  _ ∈ (_ ::: _)    | 0  = 𝟙
  y ∈ (_ ::: xs)   | _ = y ∈ xs
-}

data Perm (n : ℕ) : Type₀ where
  swap12 right-shift : Perm n
  _□_ : Perm n → Perm n → Perm n

module _ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} where
  ∘-assoc : (f : C → D) (g : B → C) (h : A → B) → f ∘ (g ∘ h) == (f ∘ g) ∘ h
  ∘-assoc f g h = funext (λ x → refl (f (g (h x))))

  ∘-unit : (f : A → B) → id ∘ f == f
  ∘-unit f = funext (λ x → refl (f x))
  
perm-to-equiv : {n : ℕ} → Perm n → AFin n ≃ AFin n
perm-to-equiv swap12      = {!!}
perm-to-equiv right-shift = {!!}
perm-to-equiv (p □ q) =
  let (f1 , e1)      = perm-to-equiv p in
  let (f2 , e2)      = perm-to-equiv q in
  let (g1 , η1 , ε1) = hae-is-qinv e1  in
  let (g2 , η2 , ε2) = hae-is-qinv e2  in
  f1 ∘ f2 , qinv-is-equiv (g2 ∘ g1 , (λ x →
    ((g2 ∘ g1) ∘ (f1 ∘ f2)) x
      ==⟨ ap (λ f → f x) (! (∘-assoc g2 g1 (f1 ∘ f2))) ⟩
    (g2 ∘ (g1 ∘ (f1 ∘ f2))) x
      ==⟨ {!!} ⟩
    (g2 ∘ ((g1 ∘ f1) ∘ f2)) x
      ==⟨ {!!} ⟩
    (g2 ∘ (id ∘ f2)) x
      ==⟨ {!!} ⟩
    (g2 ∘ f2) x
      ==⟨ η2 x ⟩
    (id x ∎)) , {!!})

equiv-to-perm : {n : ℕ} → AFin n ≃ AFin n → Perm n
equiv-to-perm (f , e) =
  let (g , η , ε) = hae-is-qinv e in
  {!!}
