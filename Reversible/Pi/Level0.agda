{-# OPTIONS --without-K #-}

module Reversible.Pi.Level0 where

open import Type using (Type; Type₀; Type₁)
open import Zero using (𝟘)
open import One
open import Paths using (_==_; refl; _◾_; !; ap; tpt; apd; tpt◾; tpt∘)
open import Coproduct
open import DependentSum using (Σ; _×_; _,_; p₁; p₂)
open import PathsInSigma using (dpair=; pair=)
open import Functions using (_∘_)
open import Equivalences using (_≃_; ide; !e; _●_; qinv-is-equiv; hae-is-qinv; is-retract)
open import Univalence using (ua)
open import NaturalNumbers
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; indTrunc; identify)
open import Homotopies using (happly)

open import Reversible.Pi.Syntax hiding (!)
open import Reversible.Utils

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El; is-finite)

M : Type₁
M = Σ Type₀ is-finite

size : U → ℕ
size ZERO = 0
size ONE  = 1
size (PLUS  t₁ t₂) = add (size t₁) (size t₂)
size (TIMES t₁ t₂) = mult (size t₁) (size t₂)

fromSize : ℕ → U
fromSize = recℕ U ZERO (λ _ → PLUS ONE)

ℕ-U-is-retract : is-retract ℕ U
ℕ-U-is-retract = size , fromSize , indℕ _ (refl _) (λ _ → ap succ)

#⟦_⟧₀ : U → Type₀
#⟦ ZERO ⟧₀        = 𝟘
#⟦ ONE  ⟧₀        = 𝟙
#⟦ PLUS  t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ + #⟦ t₂ ⟧₀
#⟦ TIMES t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ × #⟦ t₂ ⟧₀

canonicalU : U → U
canonicalU = fromSize ∘ size

size+ : (n₁ n₂ : ℕ) → PLUS (fromSize n₁) (fromSize n₂) ⟷ fromSize (add n₁ n₂)
size+ 0         n₂ = unite₊l
size+ (succ n₁) n₂ = assocr₊ ◎ (id⟷ ⊕ size+ n₁ n₂)

size* : (n₁ n₂ : ℕ) → TIMES (fromSize n₁) (fromSize n₂) ⟷ fromSize (mult n₁ n₂)
size* 0         n₂ = absorbr
size* (succ n₁) n₂ = dist ◎ ((unite⋆l ⊕ size* n₁ n₂) ◎ size+ n₂ (mult n₁ n₂))

normalizeC : (t : U) → t ⟷ canonicalU t
normalizeC ZERO = id⟷
normalizeC ONE  = uniti₊l ◎ swap₊
normalizeC (PLUS t₀ t₁) =
  (normalizeC t₀ ⊕ normalizeC t₁) ◎ size+ (size t₀) (size t₁) 
normalizeC (TIMES t₀ t₁) =
  (normalizeC t₀ ⊗ normalizeC t₁) ◎ size* (size t₀) (size t₁)

size-el : (n : ℕ) → #⟦ fromSize n ⟧₀ == El n
size-el 0        = refl 𝟘
size-el (succ n) = ap (_+_ 𝟙) (size-el n)

#⟦_⟧₁ : {X Y : U} → X ⟷ Y → #⟦ X ⟧₀ ≃ #⟦ Y ⟧₀
#⟦ id⟷ ⟧₁ = ide _
#⟦ unite₊l ⟧₁ = (λ { (i₁ ()); (i₂ x) → x }) ,
  qinv-is-equiv (i₂ , (λ { (i₁ ()); x@(i₂ _) → refl x }) , refl)
#⟦ swap₊ ⟧₁ = (λ { (i₁ x) → i₂ x; (i₂ x) → i₁ x }) ,
  qinv-is-equiv ((λ { (i₁ x) → i₂ x; (i₂ x) → i₁ x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))
#⟦ assocl₊ ⟧₁ = (λ { (i₁ x) → i₁ (i₁ x); (i₂ (i₁ x)) → i₁ (i₂ x); (i₂ (i₂ x)) → i₂ x }) ,
  qinv-is-equiv ((λ { (i₁ (i₁ x)) → i₁ x; (i₁ (i₂ x)) → i₂ (i₁ x); (i₂ x) → i₂ (i₂ x) }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ (i₁ _)) → refl x; x@(i₂ (i₂ _)) → refl x }) ,
    (λ { x@(i₁ (i₁ _)) → refl x; x@(i₁ (i₂ _)) → refl x; x@(i₂ _) → refl x }))
#⟦ unite⋆l ⟧₁ = (λ { (_ , x) → x }) ,
  qinv-is-equiv ((λ x → (0₁ , x)) , (λ { x@(0₁ , _) → refl x }) , refl)
#⟦ swap⋆ ⟧₁ = (λ { (x , y) → (y , x) }) , qinv-is-equiv ((λ { (x , y) → (y , x) }) , refl , refl)
#⟦ assocl⋆ ⟧₁ = (λ { (x , y , z) → ((x , y) , z) }) ,
  qinv-is-equiv ((λ { ((x , y) , z) → x , y , z }) , refl , refl)
#⟦ absorbr ⟧₁ = (λ { (() , _) }) , qinv-is-equiv ((λ ()) , (λ { (() , _) }) , (λ ()))
#⟦ dist ⟧₁ = (λ { (i₁ x , y) → i₁ (x , y); (i₂ x , y) → i₂ (x , y) }) ,
  qinv-is-equiv ((λ { (i₁ (x , y)) → i₁ x , y; (i₂ (x , y)) → i₂ x , y }) ,
    (λ { x@(i₁ _ , _) → refl x; x@(i₂ _ , _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))
{- #⟦ distl ⟧₁ = (λ { (x , i₁ y) → i₁ (x , y); (x , i₂ y) → i₂ (x , y) }) ,
  qinv-is-equiv ((λ { (i₁ (x , y)) → x , i₁ y; (i₂ (x , y)) → x , i₂ y }) ,
    (λ { x@(_ , i₁ _) → refl x; x@(_ , i₂ _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))-}
#⟦ _⟷_.! f ⟧₁ = !e #⟦ f ⟧₁
#⟦ f ◎ g ⟧₁ = #⟦ g ⟧₁ ● #⟦ f ⟧₁
#⟦ f ⊕ g ⟧₁ =
  let (f , e) = #⟦ f ⟧₁ in
  let (f⁻¹ , εf , ηf) = hae-is-qinv e in
  let (g , e) = #⟦ g ⟧₁ in
  let (g⁻¹ , εg , ηg) = hae-is-qinv e in
  (λ { (i₁ x) → i₁ (f x); (i₂ x) → i₂ (g x) }) ,
    qinv-is-equiv ((λ { (i₁ y) → i₁ (f⁻¹ y); (i₂ y) → i₂ (g⁻¹ y) }) ,
      (λ { (i₁ x) → ap i₁ (εf x); (i₂ x) → ap i₂ (εg x) }) ,
      (λ { (i₁ y) → ap i₁ (ηf y); (i₂ y) → ap i₂ (ηg y) }))
#⟦ f ⊗ g ⟧₁ =
  let (f , e) = #⟦ f ⟧₁ in
  let (f⁻¹ , εf , ηf) = hae-is-qinv e in
  let (g , e) = #⟦ g ⟧₁ in
  let (g⁻¹ , εg , ηg) = hae-is-qinv e in
  (λ { (a , b) → (f a , g b) }) ,
    qinv-is-equiv ((λ { (c , d) → (f⁻¹ c , g⁻¹ d) }) ,
      (λ { (a , b) → pair= (εf a , εg b) }) ,
  (λ { (c , d) → pair= (ηf c , ηg d) }))

⟦_⟧₀ : U → M
⟦ T ⟧₀ = #⟦ T ⟧₀ , size T , ∣ ua #⟦ normalizeC T ⟧₁ ◾ size-el _ ∣

⟦_⟧₀⁻¹ : M → U
⟦ _ , n , _ ⟧₀⁻¹ = fromSize n

⟦⟦_⟧₀⟧₀⁻¹ : (T : U) → ⟦ ⟦ T ⟧₀ ⟧₀⁻¹ ⟷ T
⟦⟦ T ⟧₀⟧₀⁻¹ = _⟷_.! (normalizeC T)

module _ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ} {P : A → Type ℓ'} {Q : Σ A P → Type ℓ''} {x y : A} {uz : Σ (P x) (λ u → Q (x , u))} where
  tpt-dpair : (p : x == y) → tpt (λ x → Σ (P x) (λ u → Q (x , u))) p uz == (tpt P p (p₁ uz) , tpt Q (dpair= (p , refl (tpt P p (p₁ uz)))) (p₂ uz))
  tpt-dpair (refl _) = refl _


module _ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} {b : B} where
  tpt-const : (p : x == y) → tpt (λ _ → B) p b == b
  tpt-const (refl _) = refl _

postulate
  normalizeC-id : (n : ℕ) → tpt (λ m → #⟦ fromSize n ⟧₀ ≃ #⟦ fromSize m ⟧₀) (p₂ (p₂ ℕ-U-is-retract) n) #⟦ normalizeC (fromSize n) ⟧₁ == ide _

--need: ⟦ ⟦ El n , n , ∣ refl (El n) ∣ ⟧₀⁻¹ ⟧₀ == El n , n , ∣ refl (El n) ∣
--      #⟦ fromSize n ⟧₀ , size (fromSize n) , ∣ ua #⟦ normalizeC (fromSize n) ⟧₁ ◾ size-el (size (fromSize n)) ∣
⟦⟦_⟧₀⁻¹⟧₀ : (X : M) → ∥ ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ == X ∥
⟦⟦ T , n , p ⟧₀⁻¹⟧₀ = indTrunc (λ p → ∥ ⟦ ⟦ T , n , p ⟧₀⁻¹ ⟧₀ == T , n , p ∥) (λ { (refl _) → ∣
  dpair= (size-el n ,
  dpair= (ap p₁ (tpt-dpair (size-el n)) ◾ tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n ,
         (tpt (λ m → ∥ El n == El m ∥) (ap p₁ (tpt-dpair (size-el n)) ◾ tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n)
           (p₂
             (tpt is-finite (size-el n) (size (fromSize n) , ∣ ua #⟦ normalizeC (fromSize n) ⟧₁ ◾ size-el (size (fromSize n)) ∣)))
         
            ==⟨ tpt◾ (ap p₁ (tpt-dpair (size-el n))) (tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n) _ ⟩
         
          tpt _ (tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n) (tpt (λ m → ∥ El n == El m ∥) (ap p₁ (tpt-dpair (size-el n))) _)
         
             ==⟨ ap (tpt _ (tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n)) (happly (! (tpt∘ p₁ (tpt-dpair (size-el n)))) _) ⟩
         
          tpt _ (tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n) (tpt (λ z → ∥ El n == El (p₁ z) ∥) (tpt-dpair (size-el n))
            (p₂ (tpt is-finite (size-el n) (size (fromSize n) , ∣ ua #⟦ normalizeC (fromSize n) ⟧₁ ◾ size-el (size (fromSize n)) ∣))))
         
             ==⟨ ap (tpt _ (tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n)) (apd _ p₂ (tpt-dpair (size-el n))) ⟩
          
          tpt (λ m → ∥ El n == El m ∥) (tpt-const (size-el n) ◾ p₂ (p₂ ℕ-U-is-retract) n) (tpt (λ v → ∥ p₁ v == El (p₂ v) ∥)
            (dpair= (size-el n , refl (tpt (λ _ → ℕ) (size-el n) (size (fromSize n))))) ∣ ua #⟦ normalizeC (fromSize n) ⟧₁ ◾ size-el (size (fromSize n)) ∣)

             ==⟨ {!!} ⟩
         
         (∣ refl (El n) ∣ ∎))))
  ∣ }) (λ _ → identify) p

cmpl₀ : (X : M) → Σ U (λ T → ∥ ⟦ T ⟧₀ == X ∥)
cmpl₀ X = ⟦ X ⟧₀⁻¹ , ⟦⟦ X ⟧₀⁻¹⟧₀
