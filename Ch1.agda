module Ch1 where

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

assoc : ∀ (i j k : ℕ) → (add i (add j k)) ≡ (add (add i j) k)
assoc zero j k = refl (add j k) 
assoc (suc i) j k = cong suc (assoc i j k) 

