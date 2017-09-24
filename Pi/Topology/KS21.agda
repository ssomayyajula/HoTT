{-# OPTIONS --without-K --rewriting #-}

module Pi.Topology.KS21 where

open import lib.Basics using (Type; Type₀; Type₁; cst; _==_; idp; !; Σ; _,_; pair=; _≃_; equiv; _⊔_; inl; inr; has-level; idf; ide; transport!; _∘_; _∼_; is-equiv; is-eq; λ=; equiv-is-inj; ⊥-elim; _∙_; ua; _∘e_)
open import lib.types.Truncation using (Trunc; [_]; Trunc-level; Trunc-rec; Trunc-elim)
open import lib.PathOver using (from-transp)
open import lib.types.Bool using (Bool; true; false; Bool-level; Bool-elim; Bool-true≠false)
open import lib.groups.Homomorphism using (group-hom)
open import lib.types.EilenbergMacLane1

open import lib.NType

open import Pi.Topology.SymmetricGroup

data Singleton {a} {A : Type a} (x : A) : Type a where
  _with=_ : (y : A) → x == y → Singleton x

inspect : ∀ {a} {A : Type a} (x : A) → Singleton x
inspect x = x with= idp

invol-is-equiv : ∀ {ℓ} {A : Type ℓ} {f : A → A} → f ∘ f ∼ idf A → is-equiv f
invol-is-equiv {f = f} h = is-eq f f h h

not : Bool ≃ Bool
not = f , invol-is-equiv (Bool-elim idp idp) where
  f : Bool → Bool
  f true  = false
  f false = true

not∘not=ide : not ∘e not == ide Bool
not∘not=ide = equiv= (λ= (Bool-elim idp idp))

all-bool-equiv : (p : Bool ≃ Bool) → (p == ide Bool) ⊔ (p == not)
all-bool-equiv (f , e) with inspect (f true) | inspect (f false)
... | true  with= p | false with= q = inl (equiv= (λ= (Bool-elim p q)))
... | false with= p | true  with= q = inr (equiv= (λ= (Bool-elim p q)))
... | true  with= p | true  with= q = ⊥-elim (Bool-true≠false (equiv-is-inj e _ _ (p ∙ ! q)))
... | false with= p | false with= q = ⊥-elim (Bool-true≠false (equiv-is-inj e _ _ (p ∙ ! q)))

bool-equiv-induction : ∀ {ℓ} {P : Bool ≃ Bool → Type ℓ} → P (ide Bool) → P not → (p : Bool ≃ Bool) → P p
bool-equiv-induction {P = P} pide pnot p with all-bool-equiv p
... | inl is-ide = transport! P is-ide pide
... | inr is-not = transport! P is-not pnot

U : Type₁
U = Σ Type₀ (λ X → Trunc -1 (X == Bool))

`𝟚 : U
`𝟚 = Bool , [ idp ]

`id : {A : U} → A == A
`id {A} = idp

`not : `𝟚 == `𝟚
`not = pair= (ua not) (from-transp _ _ (prop-has-all-paths Trunc-level _ _))

`not∙`not=`id : `not ∙ `not == `id
`not∙`not=`id = {!!} -- TODO: copy proof from TwoUniverse

K : Type₀
K = EM₁ (S Bool-level)

U-level : has-level 1 U
U-level = {!!} -- TODO: copy proof from TwoUniverse

model-is-em : U ≃ K
model-is-em = equiv f g {!!} {!!} where
  f : U → K
  -- TODO: EM₁-level not compatible with prop truncation
  f (_ , p) = Trunc-rec {!!} (cst embase) p
  
  g : K → U
  g = EM₁-rec U-level `𝟚 (group-hom
    (bool-equiv-induction `id `not)
    (bool-equiv-induction
      (bool-equiv-induction
        {!!}    -- h (id ∘ id)   == h id ∙ h id (easy)
        {!!})   -- h (id ∘ not)  == h not ∙ h id (easy)
      (bool-equiv-induction
        {!!}    -- h (not ∘ id)  == h id ∙ h not (easy)
        {!!}))) -- h (not ∘ not) == h not ∙ h not (use not ∘ not == id, `not ∙ `not == `id)
