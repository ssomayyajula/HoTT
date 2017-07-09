{-# OPTIONS --without-K #-}

module Reversible.Pi.Semantics where

open import Type using (Type; _⊔_; Type₀; Type₁)
open import Zero using (𝟘)
open import One
open import Paths using (_==_; refl; !; _◾_; ap; tpt)
open import Coproduct
open import DependentSum using (Σ; _,_; _×_; p₁; p₂)
open import Functions using (id; _∘_)
open import Univalence using (ua)
open import Homotopies using (_∼_)
open import Equivalences using (_≃_; ide; !e; _●_; qinv-is-equiv; hae-is-qinv)
open import NaturalNumbers
open import PropositionalTruncation using (∣_∣; recTrunc; identify)

open import PathsInSigma using (dpair=; pair=)

open import Reversible.Pi.Syntax
--open import Reversible.Pi.FinUniverse using (all-1-paths)

open import Reversible.Utils

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes
open IsFiniteIsProp using (is-finite-is-prop)

M : Type₁
M = Σ Type₀ is-finite

fromSize : ℕ → U
fromSize 0        = ZERO
fromSize (succ n) = PLUS ONE (fromSize n)

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

#⟦_⟧₀ : U → Type₀
#⟦ ZERO ⟧₀        = 𝟘
#⟦ ONE  ⟧₀        = 𝟙
#⟦ PLUS  t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ + #⟦ t₂ ⟧₀
#⟦ TIMES t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ × #⟦ t₂ ⟧₀

#⟦_⟧₁ : {X Y : U} → X ⟷ Y → #⟦ X ⟧₀ ≃ #⟦ Y ⟧₀
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

size-el : (n : ℕ) → #⟦ fromSize n ⟧₀ == El n
size-el 0        = refl _
size-el (succ n) = ap (_+_ 𝟙) (size-el n)

⟦_⟧₀ : U → M
⟦ T ⟧₀ = #⟦ T ⟧₀ , size T , ∣ ua #⟦ normalizeC T ⟧₁ ◾ size-el (size T) ∣

⟦_⟧₀⁻¹ : M → U
⟦ _ , n , _ ⟧₀⁻¹ = fromSize n

⟦⟦_⟧₀⟧₀⁻¹ : (T : U) → ⟦ ⟦ T ⟧₀ ⟧₀⁻¹ ⟷ T
⟦⟦ T ⟧₀⟧₀⁻¹ = _⟷_.! (normalizeC T)

⟦⟦_⟧₀⁻¹⟧₀ : (X : M) → ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ == X
⟦⟦ X@(T , n , p) ⟧₀⁻¹⟧₀ = {-dpair= (recTrunc _ (λ p → size-el n ◾ Paths.! p) {!!} p , dpair= ({!!} , {!!}))-}
  recTrunc _ (λ p' → dpair= (size-el n ◾ Paths.! p' ,
  dpair= ({!!} ,
          {!!})))
          {!!}
          p where

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦_⟧₁ {X} {Y} c = dpair= (ua #⟦ c ⟧₁ , dpair= (lem c , identify _ _)) where
  lem : (c : X ⟷ Y) → p₁ (tpt is-finite (ua #⟦ c ⟧₁) (size X , ∣ ua #⟦ normalizeC X ⟧₁ ◾ size-el (size X) ∣)) == size Y
  lem unite₊l = {!!}
  lem = {!!}

⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹
⟦ refl _ ⟧₁⁻¹ = id⟷

cmpl₀ : (x : M) → Σ U (λ t → ⟦ t ⟧₀ == x)
cmpl₀ x = ⟦ x ⟧₀⁻¹ , ⟦⟦ x ⟧₀⁻¹⟧₀
