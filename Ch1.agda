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

-- Dependent pattern matching...very interesting
trans : {A : Set} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
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

-- Exercise 1.16
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

-- Exercise 1.4
iter : ∀(C : Set) → C → (C → C) → ℕ → C
iter C c₀ cₛ zero    = c₀
iter C c₀ cₛ (suc n) = cₛ (iter C c₀ cₛ n)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

recℕ' : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ' C c₀ cₛ n = iter C c₀ (cₛ (pred n)) n
{-
recℕ'eqrecℕ : ∀ (C : Set) → ∀ (c₀ : C) → ∀ (cₛ : ℕ → C → C) → ∀ (n : ℕ) → (recℕ' C c₀ cₛ n ≡ recℕ C c₀ cₛ n)
recℕ'eqrecℕ C c₀ cₛ = indℕ
                         (λ n → (recℕ' C c₀ cₛ n ≡ recℕ C c₀ cₛ n))
                         (refl c₀)
                         (λ n cn →
                            recℕ' C c₀ cₛ (suc n)
                              ≡⟨ refl _ ⟩
                            cₛ n (iter C c₀ (cₛ n) n)
                              ≡⟨ cong (cₛ _) cn ⟩
                            _
                              ≡⟨ _ ⟩
                            _)

-}
-- Exercise 1.8
_×_ : ℕ → ℕ → ℕ
x × y = recℕ ℕ 0 (λ _ xpy → add x xpy) y

_^_ : ℕ → ℕ → ℕ
x ^ y = recℕ
            ℕ
            -- "When you only have a recursor, even case analysis looks
            --  like recursion"
            -- 0 ^ 0 = 0, x ^ 0 = 1
            ((recℕ ℕ 0 (λ _ _ → 1)) x)
            (λ _ xpy → xpy × x)
            y

addRightIdent : ∀ (x : ℕ) → (add x zero ≡ x)
addRightIdent = indℕ
                  (λ x → (add x zero ≡ x))
                  (refl 0)
                  (λ _ cx → cong suc cx)

addLeftIdent : ∀ (x : ℕ) → (add zero x ≡ x)
addLeftIdent x = refl x

multRightIdent : ∀ (x : ℕ) → ((x × 1) ≡ x)
multRightIdent = indℕ
                   (λ x → ((x × 1) ≡ x))
                   (refl 0)
                   (λ _ cx → cong suc cx)

multLeftIdent : ∀ (x : ℕ) → 1 × x ≡ x
multLeftIdent = indℕ
                  (λ x → 1 × x ≡ x)
                  (refl 0)
                  (λ x cx →
                    1 × suc x
                      ≡⟨ refl _ ⟩
                    suc (recℕ ℕ 0 (λ _ → suc) x)
                      ≡⟨ cong suc cx ⟩
                    suc x ∎)

multLeftAnni : ∀ (x : ℕ) → ((x × 0) ≡ 0)
multLeftAnni x = refl 0

multRightAnni : ∀ (x : ℕ) → 0 × x ≡ 0
multRightAnni = indℕ
                  (λ x → 0 × x ≡ 0)
                  (refl 0)
                  (λ x cx →
                    0 × suc x
                      ≡⟨ refl _ ⟩
                    recℕ ℕ 0 (λ _ → add 0) x
                      ≡⟨ cx ⟩
                    0 ∎)

multRightDistrib : ∀ (i j k : ℕ) → (i × (add j k)) ≡ add (i × j) (i × k)
multRightDistrib i j k = indℕ
                          (λ i → (i × (add j k)) ≡ add (i × j) (i × k))
                          (0 × add j k
                             ≡⟨ multRightAnni (add j k) ⟩
                           0
                             ≡⟨ refl _ ⟩
                           add 0 0
                             ≡⟨ cong (λ ij → add ij 0) (sym (multRightAnni j)) ⟩
                           add (0 × j) 0
                             ≡⟨ cong (λ ik → add (0 × j) ik) (sym (multRightAnni k)) ⟩
                           add (0 × j) (0 × k) ∎)
                          (λ x cx →
                            {- IH: i * (j + k) = (i * j) + (i * k) -}
                            {- WTS: (x + 1) * (j + k) = (i + 1) * j + (i + 1) * k -}
                            
                            _)
                          i



multAssoc : ∀ (i j k : ℕ) → (i × (j × k)) ≡ ((i × j) × k)
multAssoc i j k = indℕ
                    (λ i → (i × (j × k)) ≡ ((i × j) × k))
                    (0 × (j × k)
                       ≡⟨ multRightAnni (j × k) ⟩
                     0
                       ≡⟨ sym (multRightAnni k) ⟩
                     0 × k
                       ≡⟨ cong (λ x → x × k) (sym (multRightAnni j)) ⟩
                     (0 × j) × k ∎)
                     (λ i ci →
                       suc i × (j × k)
                         ≡⟨ refl _ ⟩
                       recℕ ℕ 0 (λ _ x → suc (add i x)) (j × k)
                         ≡⟨ _ ⟩
                       _)
                     i


-- (ℕ, +, 0, ×, 1) is a semiring by: *assoc, *Ident, comm, mult*Distrib, and *Anni

-- Exercise 1.9
data Fin : ℕ → Set where
  -- ∀n:ℕ. 0ₙ : Fin n+1
  fzero : ∀ (n : ℕ) → Fin (suc n)
  -- ∀n:ℕ, xₙ : Fin n → ((x+1)ₙ₊₁ ≝ xₙ + 1) : Fin n+1
  fsuc : ∀ (n : ℕ) → Fin n → Fin (suc n)

fmax : ∀ (n : ℕ) → Fin (suc n)
fmax zero    = fzero 0
fmax (suc n) = fsuc (suc n) (fmax n)

-- Excerise 1.10
-- This one took a while...the trick is you need more recursion!
ack : ℕ → ℕ → ℕ
ack = recℕ
        (ℕ → ℕ)
        suc
        (λ _ am → recℕ ℕ (am 1) (λ _ → am))
