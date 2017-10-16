module Pi.Topology.BoolUniverse where

open import lib.Basics
open import lib.types.Bool
open import lib.types.Sigma using (fst=)
open import lib.NType2 using (is-gpd)
open import lib.Equivalence2 using (ua-∘e)
open import lib.types.Truncation

open import Pi.Topology.Equivalence
open import Pi.Topology.Util
open import Pi.Topology.Universe

not : Bool ≃ Bool
not = f , invol-is-equiv (Bool-elim idp idp) where
  f : Bool → Bool
  f true  = false
  f false = true

all-Bool-equiv : (p : Bool ≃ Bool) → (p == ide Bool) ⊔ (p == not)
all-Bool-equiv (f , e) with inspect (f true) | inspect (f false)
... | true  with= p | false with= q = inl $ equiv= $ λ= $ Bool-elim p q
... | false with= p | true  with= q = inr $ equiv= $ λ= $ Bool-elim p q
... | true  with= p | true  with= q = ⊥-elim $ Bool-true≠false $ equiv-is-inj e _ _ $ p ∙ ! q
... | false with= p | false with= q = ⊥-elim $ Bool-true≠false $ equiv-is-inj e _ _ $ p ∙ ! q

Bool-equiv-induction : ∀ {ℓ} {P : Bool ≃ Bool → Type ℓ} → P (ide Bool) → P not → (p : Bool ≃ Bool) → P p
Bool-equiv-induction {P = P} pide pnot p with all-Bool-equiv p
... | inl is-ide = transport! P is-ide pide
... | inr is-not = transport! P is-not pnot

~not : (` Bool) == (` Bool)
~not = ~ not

not∘not=ide : not ∘e not == ide Bool
not∘not=ide = equiv= $ λ= $ Bool-elim idp idp

--~not∙~not=idp = pair=∙ (ua not) {!!} (ua not) {!!} ∙ ap (pair=) {!!} where
  --lem : ua not ∙ ua not == idp
  --lem = ! (ua-∘e not not) ∙ ap ua not∘not=ide ∙ ua-ide Bool

ide≠not : ide Bool ≠ not
ide≠not e = Bool-true≠false $ app= (fst= e) true

-- TODO: Port proofs from 2DTypes/Pi2.UniFibExamples, 2DTypes/Pi2.TwoUniverse
postulate
  U[Bool]-level : is-gpd U[ Bool ]
  ~not∙~not=idp : ~not ∙ ~not == idp
