module Pi.Topology.Util where

open import lib.Basics using (Type; _==_; idp)

data Singleton {a} {A : Type a} (x : A) : Type a where
  _with=_ : (y : A) → x == y → Singleton x

inspect : ∀ {a} {A : Type a} (x : A) → Singleton x
inspect x = x with= idp
