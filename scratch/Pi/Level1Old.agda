{-# OPTIONS --without-K #-}

module Reversible.Pi.Level1Old where

open import Type using (Type; _⊔_; Type₀; Type₁)
open import Zero using (𝟘)
open import One
open import Paths using (_==_; refl; !; _◾_; ap; tpt; ind=)
open import Coproduct
open import DependentSum using (Σ; _,_; _×_; p₁; p₂)
open import Functions using (_∘_; id; _$_)
open import Univalence using (ua)
open import Equivalences using (_≃_; ide; !e; _●_; qinv-is-equiv; hae-is-qinv)
open import NaturalNumbers
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; identify)

open import PathsInSigma using (dpair=; pair=)

open import Reversible.Pi.Syntax
open import Reversible.Pi.Level0Old

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El; finite-types-is-univ)

module _ {ℓ} {ℓ'} {ℓ''} {A : Type ℓ} {P : A → Type ℓ'} {Q : Σ A P → Type ℓ''} {x y : A} {uz : Σ (P x) (λ u → Q (x , u))} where
  tpt-dpair : (p : x == y) → tpt (λ x → Σ (P x) (λ u → Q (x , u))) p uz == (tpt P p (p₁ uz) , tpt Q (dpair= (p , refl (tpt P p (p₁ uz)))) (p₂ uz))
  tpt-dpair (refl _) = refl _

module _ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} {b : B} where
  tpt-const : (p : x == y) → tpt (λ _ → B) p b == b
  tpt-const (refl _) = refl _

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
size-el = indℕ _ (refl 𝟘) (λ _ → ap (_+_ 𝟙))

size= : {X Y : U} → X ⟷ Y → size X == size Y
size= = {!!}

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦_⟧₁ {X} {Y} c = {!!}
  --let p = ua (tpt (_≃_ #⟦ Y ⟧₀) (size-el _) #⟦ normalizeC _ ⟧₁ ● #⟦ c ⟧₁ ● !e (tpt (_≃_ #⟦ X ⟧₀) (size-el _) #⟦ normalizeC _ ⟧₁)) in
  --dpair= (p , dpair= (ap p₁ (tpt-dpair p) ◾ tpt-const p ◾ size= c , identify _ _))

{-
⟦_⟧₁⁻¹ : {X Y : M} → X == Y → ⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹
⟦_⟧₁⁻¹ {_ , _ , c₁} {_ , _ , c₂} p =
  recTrunc _ (λ c₁ →
  recTrunc _ (λ c₂ →
    ∣ ==-to-⟷ (! c₁ ◾ dpair=-e₁ p ◾ c₂) ∣
  ) identify c₂) identify c₁
-}

{-
⟦⟦_⟧₁⁻¹⟧₁ : {X Y : M} (p : X == Y) → recTrunc _ (λ p1 → recTrunc _  (λ p2 → ∥ tpt (_==_ X) p2 (tpt (λ x → x == ⟦ ⟦ Y ⟧₀⁻¹ ⟧₀) p1 ⟦ ⟦ p ⟧₁⁻¹ ⟧₁) == p ∥) {!!} ⟦⟦ Y ⟧₀⁻¹⟧₀) {!!} ⟦⟦ X ⟧₀⁻¹⟧₀
⟦⟦ p ⟧₁⁻¹⟧₁ = {!!}

-}

{-
cmpl₁ : {X Y : M} (p : X == Y) → Σ (⟦ X ⟧₀⁻¹ ⟷ ⟦ Y ⟧₀⁻¹) (λ c → ∥ ⟦ c ⟧₁ == {!!} ∥)
cmpl₁ p = ⟦ p ⟧₁⁻¹ , {!!} --⟦ p ⟧₁⁻¹ , ⟦⟦ p ⟧₁⁻¹⟧₁
-}
