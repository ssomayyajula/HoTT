module Ch1 where

infix  4  _≡_     -- propositional equality
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

-- Exercises 1.4, 1.8, 1.9, 1.10, 1.16

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Propositional Equality

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f (refl x) = refl (f x)

sym : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
sym (refl x) = refl x

trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans (refl x) (refl .x) = refl x

-- Defining functions

-- Pattern-matching style

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

c₀ : ℕ → ℕ
c₀ n = n

cₛ : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
cₛ m g n = suc (g n)

add : ℕ → ℕ → ℕ
add zero = c₀
add (suc n) = cₛ n (add n)

assoc : ∀ (i j k : ℕ) → (add i (add j k)) ≡ (add (add i j) k)
assoc zero j k = refl (add j k) 
assoc (suc i) j k = cong suc (assoc i j k) 

-- Recursion principle

recℕ : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ C c₀ cₛ zero = c₀
recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)

double' : ℕ → ℕ
double' = recℕ ℕ 0 (λ _ y → suc (suc y))

add' : ℕ → ℕ → ℕ
add' = recℕ (ℕ → ℕ) (λ n → n) (λ n g m → suc (g m))

-- Induction principle

indℕ : ∀ (C : ℕ → Set) → C zero → (∀ (n : ℕ) → C n → C (suc n)) → (∀ (n : ℕ) → C n)
indℕ C c₀ cₛ zero = c₀
indℕ C c₀ cₛ (suc n) = cₛ n (indℕ C c₀ cₛ n)

assoc' : ∀ (i j k : ℕ) → (add i (add j k)) ≡ (add (add i j) k)
assoc' = indℕ
           (λ i → ∀ (j k : ℕ) → (add i (add j k) ≡ add (add i j) k))
           (λ j k → refl (add j k))
           (λ i r j k → cong suc (r j k))

-- Equational reasoning

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = trans p q 

_∎ : {A : Set} (x : A) → x ≡ x
_∎ x = refl x

-- Example

unitr : ∀ (i : ℕ) → add i 0 ≡ i
unitr 0 = refl 0
unitr (suc i) =
  add (suc i) 0
    ≡⟨ refl _ ⟩ 
  suc (add i 0)
    ≡⟨ cong suc (unitr i) ⟩ 
  (suc i ∎)

sucr : ∀ (i j : ℕ) → (add (suc i) j) ≡ add i (suc j)
sucr 0 j = refl (suc j)
sucr (suc i) j =
  add (suc (suc i)) j
    ≡⟨ refl _ ⟩
  suc (add (suc i) j)
    ≡⟨ cong suc (sucr i j) ⟩
  suc (add i (suc j))
    ≡⟨ refl _ ⟩
  (add (suc i) (suc j) ∎)

comm : ∀ (i j : ℕ) → add i j ≡ add j i
comm 0 j = sym (unitr j)
comm (suc i) j =
  add (suc i) j
    ≡⟨ refl _ ⟩
  suc (add i j)
    ≡⟨ cong suc (comm i j) ⟩
  suc (add j i)
    ≡⟨ sucr j i ⟩
  (add j (suc i) ∎)

