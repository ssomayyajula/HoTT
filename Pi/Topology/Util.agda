module Pi.Topology.Util where

open import lib.Basics

data Singleton {a} {A : Type a} (x : A) : Type a where
  _with=_ : (y : A) → x == y → Singleton x

inspect : ∀ {a} {A : Type a} (x : A) → Singleton x
inspect x = x with= idp

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where
  pathover∙↓ : {x y z : X} {u : P x} {v : P y} {w : P z}
        → (p : x == y) (r : u == v [ P ↓ p ])
        → (q : y == z) (s : v == w [ P ↓ q ])
        → u == w [ P ↓ (p ∙ q) ]
  pathover∙↓ idp idp idp idp = idp

  pair=∙ : {x y z : X} {u : P x} {v : P y} {w : P z}
          → (p : x == y) (r : u == v [ P ↓ p ])
          → (q : y == z) (s : v == w [ P ↓ q ])
          → pair= p r ∙ pair= q s == pair= (p ∙ q) (pathover∙↓ p r q s)
  pair=∙ idp idp idp idp = idp
