{-# OPTIONS --without-K #-}

module Reversible.Pi.Semantics where

open import Type using (Type; _⊔_; Type₀; Type₁)
open import Zero using (𝟘)
open import One
open import Paths using (_==_; refl; !; _◾_; ap; tpt; ind=)
open import Coproduct
open import DependentSum using (Σ; _,_; _×_; p₁)
open import Functions using (_∘_)
open import Univalence using (ua)
open import Equivalences using (_≃_; ide; !e; _●_; qinv-is-equiv; hae-is-qinv)
open import NaturalNumbers
open import PropositionalTruncation using (∣_∣; recTrunc; identify)

open import PathsInSigma using (dpair=; pair=; dpair=-e₁)

open import Reversible.Pi.Syntax
--open import Reversible.Pi.FinUniverse using (all-1-paths)

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes

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

toNames : ℕ → Names
toNames 0        = `0
toNames (succ n) = `1+ (toNames n)

toU : Names → U
toU `0      = ZERO
toU (`1+ n) = PLUS ONE (toU n)

⟦_⟧₀ : U → M
⟦ T ⟧₀ = #⟦ T ⟧₀ , fromU T , ∣ ua (lem (size T) ● #⟦ normalizeC T ⟧₁) ∣ where
  fromU : U → Names
  fromU = toNames ∘ size
  
  lem : (n : ℕ) → #⟦ fromSize n ⟧₀ ≃ El (toNames n)
  lem 0        = ide _
  lem (succ n) =
    let (f , e)     = lem n         in
    let (g , ε , η) = hae-is-qinv e in
    (λ { (i₁ 0₁) → i₁ 0₁; (i₂ x) → i₂ (f x) }) , qinv-is-equiv
      ((λ { (i₁ 0₁) → i₁ 0₁; (i₂ y) → i₂ (g y) }) ,
       (λ { (i₁ 0₁) → refl _; (i₂ x) → ap i₂ (ε x) }) ,
       (λ { (i₁ 0₁) → refl _; (i₂ y) → ap i₂ (η y) }))

⟦_⟧₀⁻¹ : M → U
⟦ _ , name , _ ⟧₀⁻¹ = toU name

⟦⟦_⟧₀⟧₀⁻¹ : (T : U) → ⟦ ⟦ T ⟧₀ ⟧₀⁻¹ ⟷ T
⟦⟦ T ⟧₀⟧₀⁻¹ = tpt (λ t → t ⟷ T) (lem (size T)) (_⟷_.! (normalizeC T)) where
  lem : (n : ℕ) → fromSize n == toU (toNames n)
  lem 0        = refl _
  lem (succ n) = ap (PLUS ONE) (lem n)

⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹
⟦ refl _ ⟧₁⁻¹ = id⟷

completeness₀ : {t s : U} → ⟦ t ⟧₀ == ⟦ s ⟧₀ → t ⟷ s
completeness₀ {t} {s} p = _⟷_.! ⟦⟦ t ⟧₀⟧₀⁻¹ ◎ (⟦ p ⟧₁⁻¹ ◎ ⟦⟦ s ⟧₀⟧₀⁻¹)

{-
⟦⟦_⟧₀⁻¹⟧₀ : (T : M) → ⟦ ⟦ T ⟧₀⁻¹ ⟧₀ == T
⟦⟦ T@(m , flat , p) ⟧₀⁻¹⟧₀ = dpair= (recTrunc _ (λ x → ! (x ◾ lem)) {!!} p , {!!}) --recTrunc (⟦ ⟦ T ⟧₀⁻¹ ⟧₀ == T) (λ x → ! (x ◾ lem)) ({!!}) p
 where
  lem : {flat : Names} → El flat == #⟦ ⟦ T ⟧₀⁻¹ ⟧₀
  lem {`0} = {!!}
  lem {`1+ n} = {!!}

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦_⟧₁ {X} {Y} c = dpair= (ua #⟦ c ⟧₁ , dpair= ({!!} , identify _ _)) where
  lem : (X Y : U) → p₁ (tpt is-finite (ua #⟦ c ⟧₁) (fromU X , ∣ ua (mlem (size X) ● #⟦ normalizeC X ⟧₁) ∣)) == fromU Y
  lem = {!!}
-}
