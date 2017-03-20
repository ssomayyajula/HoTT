module Ch1 where

infix  4  _≡_     -- propositional equality
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

-- Exercises 1.4, 1.8, 1.9, 1.10, 1.16

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

record Prod (A : Set) (B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B

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

{- Uses products to save n - 1 to pass to cₛ -}
recℕ' : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ' C c₀ cₛ n = Prod.π₂
                     (iter (Prod ℕ C) (0 , c₀)
                       (λ p → let n = Prod.π₁ p in
                               let c = Prod.π₂ p in
                               (suc n , cₛ n c)) n)

lemma : ∀ (C : Set) → ∀ (c₀ : C) → ∀ (cₛ : ℕ → C → C) → ∀ (n : ℕ) →
  n ≡ Prod.π₁ (iter (Prod ℕ C) (0 , c₀) (λ p → let n = Prod.π₁ p in
                                                 let c = Prod.π₂ p in
                                                 (suc n , cₛ n c)) n)
lemma C c₀ cₛ = indℕ
                  (λ n → n ≡ Prod.π₁ (iter (Prod ℕ C) (0 , c₀)
                                        (λ p → let n = Prod.π₁ p in
                                                let c = Prod.π₂ p in
                                                (suc n , cₛ n c)) n))
                  (refl _)
                  (λ n cn →
                    let cₛ' =  (λ p → let n = Prod.π₁ p in
                                       let c = Prod.π₂ p in
                                       (suc n , cₛ n c)) in
                    sym (
                       Prod.π₁ (iter (Prod ℕ C) (0 , c₀) cₛ' (suc n))
                         ≡⟨ refl _ ⟩
                       let p = iter (Prod ℕ C) (0 , c₀) cₛ' n in
                       let c = Prod.π₂ p in
                       Prod.π₁ (suc (Prod.π₁ p) , cₛ n c)
                         ≡⟨ cong (λ x → Prod.π₁ (suc x , cₛ n c)) (sym cn) ⟩
                       ((suc n) ∎)
                    ))

recℕ'eqrecℕ : ∀ (C : Set) → ∀ (c₀ : C) → ∀ (cₛ : ℕ → C → C) → ∀ (n : ℕ) → (recℕ' C c₀ cₛ n ≡ recℕ C c₀ cₛ n)
recℕ'eqrecℕ C c₀ cₛ = indℕ
                         (λ n → (recℕ' C c₀ cₛ n ≡ recℕ C c₀ cₛ n))
                         (refl c₀)
                         (λ n cn →
                           let cₛ' = (λ p → let n = Prod.π₁ p in
                                             let c = Prod.π₂ p in
                                             (suc n , cₛ n c)) in
                           recℕ' C c₀ cₛ (suc n)
                             ≡⟨ refl _ ⟩
                           let p = iter (Prod ℕ C) (0 , c₀) cₛ' n in
                           cₛ (Prod.π₁ p) (Prod.π₂ p)
                             ≡⟨ cong (λ x → cₛ (Prod.π₁ p) x) cn ⟩
                           cₛ (Prod.π₁ p) (recℕ C c₀ cₛ n)
                             ≡⟨ cong (λ x → cₛ x (recℕ C c₀ cₛ n)) (sym (lemma C c₀ cₛ n)) ⟩
                           ((recℕ C c₀ cₛ (suc n)) ∎))


-- Exercise 1.8
_×_ : ℕ → ℕ → ℕ
(_×_) x = recℕ ℕ 0 (λ _ → add x)

_^_ : ℕ → ℕ → ℕ
(_^_) x = recℕ
            ℕ
            -- "When you only have a recursor, even case analysis looks
            --  like recursion"
            -- 0 ^ 0 = 0, x ^ 0 = 1
            ((recℕ ℕ 0 (λ _ _ → 1)) x)
            (λ _ → (_×_) x)

addRightIdent : ∀ (x : ℕ) → add x zero ≡ x
addRightIdent = indℕ
                  (λ x → add x zero ≡ x)
                  (refl _)
                  (λ _ → cong suc)

addLeftIdent : ∀ (x : ℕ) → add zero x ≡ x
addLeftIdent _ = refl _

multRightIdent : ∀ (x : ℕ) → x × 1 ≡ x
multRightIdent = indℕ
                   (λ x → x × 1 ≡ x)
                   (refl _)
                   (λ _ → cong suc)

multLeftIdent : ∀ (x : ℕ) → 1 × x ≡ x
multLeftIdent = indℕ
                  (λ x → 1 × x ≡ x)
                  (refl _)
                  (λ _ → cong suc)

multLeftAnni : ∀ (x : ℕ) → x × 0 ≡ 0
multLeftAnni _ = refl _

multRightAnni : ∀ (x : ℕ) → 0 × x ≡ 0
multRightAnni = indℕ
                  (λ x → 0 × x ≡ 0)
                  (refl _)
                  (λ x cx → cx)

sucAdd1 : ∀ (i : ℕ) → suc i ≡ add i 1
sucAdd1 = indℕ
            (λ i → suc i ≡ add i 1)
            (refl _)
            (λ _ → cong suc)

multLeftDistrib : ∀ (i j k : ℕ) → i × (add j k) ≡ add (i × j) (i × k)
multLeftDistrib i j k = indℕ
                          (λ j → i × (add j k) ≡ add (i × j) (i × k))
                          (refl _)
                          (λ j cj →
                            i × (add (suc j) k)
                              ≡⟨ refl _ ⟩
                            add i (i × (add j k))
                              ≡⟨ cong (add i) cj ⟩
                            add i (add (i × j) (i × k))
                              ≡⟨ refl _ ⟩
                            add i (add (i × j) (i × k))
                              ≡⟨ assoc i (i × j) (i × k) ⟩
                            add (add i (i × j)) (i × k)
                              ≡⟨ refl _ ⟩
                            ((add (i × suc j) (i × k)) ∎))
                          j

multRightDistrib : ∀ (i j k : ℕ) → (add i j) × k ≡ add (i × k) (j × k)
multRightDistrib i j = indℕ
                         (λ k → (add i j) × k ≡ add (i × k) (j × k))
                         (refl _)
                         (λ k ck →
                           (add i j) × suc k
                             ≡⟨ refl _ ⟩
                           add (add i j) ((add i j) × k)
                             ≡⟨ cong (add (add i j)) ck ⟩
                           add (add i j) (add (i × k) (j × k))
                             ≡⟨ assoc (add i j) (i × k) (j × k) ⟩
                           add (add (add i j) (i × k)) (j × k)
                             ≡⟨ cong (λ x → add (add x (i × k)) (j × k)) (comm i j) ⟩
                           add (add (add j i) (i × k)) (j × k)
                             ≡⟨ cong (λ x → add x (j × k)) (sym (assoc j i (i × k))) ⟩
                           add (add j (add i (i × k))) (j × k)
                             ≡⟨ refl _ ⟩
                           add (add j (i × suc k)) (j × k)
                             ≡⟨ sym (assoc j (i × suc k) (j × k)) ⟩
                           add j (add (i × suc k) (j × k))
                             ≡⟨ cong (add j) (comm (i × suc k) (j × k)) ⟩
                           add j (add (j × k) (i × suc k))
                             ≡⟨ assoc j (j × k) (i × suc k) ⟩
                           add (add j (j × k)) (i × suc k)
                             ≡⟨ refl _ ⟩
                           add (j × suc k) (i × suc k)
                             ≡⟨ comm (j × suc k) (i × suc k) ⟩
                           ((add (i × suc k) (j × suc k)) ∎))

multAssoc : ∀ (i j k : ℕ) → i × (j × k) ≡ (i × j) × k
multAssoc i j = indℕ
                  (λ k → i × (j × k) ≡ (i × j) × k)
                  (refl _)
                  (λ k ck →
                    i × (j × suc k)
                      ≡⟨ refl _ ⟩
                    i × (add j (j × k))
                      ≡⟨ multLeftDistrib i j (j × k) ⟩
                    add (i × j) (i × (j × k))
                      ≡⟨ cong (add (i × j)) ck ⟩
                    add (i × j) ((i × j) × k)
                      ≡⟨ refl _ ⟩
                    (((i × j) × suc k) ∎))

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
