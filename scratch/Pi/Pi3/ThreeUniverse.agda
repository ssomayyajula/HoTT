module Reversible.Pi3.ThreeUniverse where

open import UnivalentTypeTheory
open import Homotopies
open import PropositionalTruncation
open import Reversible.UnivalentFibrations
open import TwoUniverse using (is-type)
open import TwoUniverse using (ap-dpair=-e-out)

𝟛 : Type₀
𝟛 = 𝟙 + (𝟙 + 𝟙)

pattern 0₃ = i₁ 0₁
pattern 1₃ = i₂ (i₁ 0₁)
pattern 2₃ = i₂ (i₂ 0₁)

ind𝟛 : ∀ {ℓ} {P : 𝟛 → Type ℓ} → P 0₃ → P 1₃ → P 2₃ → (x : 𝟛) → P x
ind𝟛 p0 p1 p2 = λ { 0₃ → p0; 1₃ → p1; 2₃ → p2 }

`𝟛 : U[ 𝟛 ]
`𝟛 = lift 𝟛

swap12 : 𝟛 → 𝟛
swap12 0₃ = 1₃
swap12 1₃ = 0₃
swap12 2₃ = 2₃

swap13 : 𝟛 → 𝟛
swap13 0₃ = 2₃
swap13 1₃ = 1₃
swap13 2₃ = 0₃

id-𝟛 : 𝟛 → 𝟛
id-𝟛 = swap12 ∘ swap12

left-shift : 𝟛 → 𝟛
left-shift = swap13 ∘ swap12

right-shift : 𝟛 → 𝟛
right-shift = swap12 ∘ swap13

swap23 : 𝟛 → 𝟛
swap23 = swap12 ∘ left-shift

{- Involutions are equivalences -}
inv-is-equiv : ∀ {ℓ} {A : Type ℓ} (f : A → A) → f ∘ f ∼ id → is-equiv f
inv-is-equiv f h = qinv-is-equiv (f , h , h)

private
  swap12-eqv : 𝟛 ≃ 𝟛
  swap12-eqv =
    swap12 , inv-is-equiv swap12 (ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃))

  swap13-eqv : 𝟛 ≃ 𝟛
  swap13-eqv =
    swap13 , inv-is-equiv swap13 (ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃))

  left-shift-eqv : 𝟛 ≃ 𝟛
  left-shift-eqv =
    left-shift , qinv-is-equiv (right-shift ,
      ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃) ,
      ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃))

  right-shift-eqv : 𝟛 ≃ 𝟛
  right-shift-eqv =
    right-shift , qinv-is-equiv (left-shift ,
      ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃) ,
      ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃))
  
  swap23-eqv : 𝟛 ≃ 𝟛
  swap23-eqv =
    swap23 , inv-is-equiv swap23 (ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃))

`swap12 : `𝟛 == `𝟛
`swap12 = dpair= (ua swap12-eqv , identify _ _)

`swap13 : `𝟛 == `𝟛
`swap13 = dpair= (ua swap13-eqv , identify _ _)

`swap23 : `𝟛 == `𝟛
`swap23 = dpair= (ua swap23-eqv , identify _ _)

`left-shift : `𝟛 == `𝟛
`left-shift = dpair= (ua left-shift-eqv , identify _ _)

`right-shift : `𝟛 == `𝟛
`right-shift = dpair= (ua right-shift-eqv , identify _ _)

id-𝟛-eq-id : id-𝟛 == id
id-𝟛-eq-id = funext (ind𝟛 (refl 0₃) (refl 1₃) (refl 2₃))

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with=_ : (y : A) → x == y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with= (refl x)

{- Non-bijective functions into 𝟛 are not equivalences -}

{-φ-𝟘 : (f : 𝟛 → 𝟛) → is-equiv f → ¬ (Σ 𝟛 (λ v → (f 0₃ == b) × (f 1₃ == b) + ))
φ
-}

{- Equivalences on 𝟛 are equivalent to 1 of 6 "canonical" equivalences -}
φ : (f : 𝟛 → 𝟛) → is-equiv f → (f == id) + (f == swap12) + (f == swap13) + (f == swap23) + (f == left-shift) + (f == right-shift)
φ f e with inspect (f 0₃) | inspect (f 1₃) | inspect (f 2₃) {- Observe the action of f on 𝟛 -}
{- Exclude the 21 impossible cases -}
{-φ f e      | 0₃ with= p   | 0₃ with= q     | 0₃ with= r = {!!}
φ f e      | 1₃ with= p   | 0₃ with= q     | 0₃ with= r = {!!}
φ f e      | 0₃ with= p   | 1₃ with= q     | 0₃ with= r = {!!}
φ f e      | 0₃ with= p   | 0₃ with= q     | 1₃ with= r = {!!}
φ f e      | 1₃ with= p   | 1₃ with= q     | 0₃ with= r = {!!}
φ f e      | 1₃ with= p   | 0₃ with= q     | 1₃ with= r = {!!}
φ f e      | 0₃ with= p   | 1₃ with= q     | 1₃ with= r = {!!}
φ f e      | 1₃ with= p   | 1₃ with= q     | 1₃ with= r = {!!}-}
{- Now consider the 6 actual cases -}
φ f e      | 0₃ with= p   | 1₃ with= q     | 2₃ with= r = i₁ (funext (ind𝟛 p q r))
φ f e      | 1₃ with= p   | 0₃ with= q     | 2₃ with= r = i₂ (i₁ (funext (ind𝟛 p q r)))
φ f e      | 2₃ with= p   | 1₃ with= q     | 0₃ with= r = i₂ (i₂ (i₁ (funext (ind𝟛 p q r))))
φ f e      | 0₃ with= p   | 2₃ with= q     | 1₃ with= r = i₂ (i₂ (i₂ (i₁ (funext (ind𝟛 p q r)))))
φ f e      | 1₃ with= p   | 2₃ with= q     | 0₃ with= r = i₂ (i₂ (i₂ (i₂ (i₁ (funext (ind𝟛 p q r))))))
φ f e      | 2₃ with= p   | 0₃ with= q     | 1₃ with= r = i₂ (i₂ (i₂ (i₂ (i₂ (funext (ind𝟛 p q r))))))
φ f e      | _            | _              | _ = {!!}


ψ : {f : 𝟛 → 𝟛} {e : is-equiv f} → (f == id) + (f == swap12) + (f == swap13) + (f == swap23) + (f == left-shift) + (f == right-shift) → ((f , e) == ide 𝟛) + ((f , e) == swap12-eqv) + ((f , e) == swap13-eqv) + ((f , e) == swap23-eqv) + ((f , e) == left-shift-eqv) + ((f , e) == right-shift-eqv)
ψ (i₁ p) = i₁ (eqv= p)
ψ (i₂ (i₁ p)) = i₂ (i₁ (eqv= p))
ψ (i₂ (i₂ (i₁ p))) = i₂ (i₂ (i₁ (eqv= p)))
ψ (i₂ (i₂ (i₂ (i₁ p)))) = i₂ (i₂ (i₂ (i₁ (eqv= p))))
ψ (i₂ (i₂ (i₂ (i₂ (i₁ p))))) = i₂ (i₂ (i₂ (i₂ (i₁ (eqv= p)))))
ψ (i₂ (i₂ (i₂ (i₂ (i₂ p))))) = i₂ (i₂ (i₂ (i₂ (i₂ (eqv= p)))))

all-eqvs-𝟛 : (e : 𝟛 ≃ 𝟛) → (e == ide 𝟛) + (e == swap12-eqv) + (e == swap13-eqv) + (e == swap23-eqv) + (e == left-shift-eqv) + (e == right-shift-eqv)
all-eqvs-𝟛 (f , e') = ψ (φ f e')

all-1-paths-𝟛 : (l : 𝟛 == 𝟛) → (l == refl 𝟛) + (l == ua swap12-eqv) + (l == ua swap13-eqv) + (l == ua swap23-eqv) + (l == ua left-shift-eqv) + (l == ua right-shift-eqv)
all-1-paths-𝟛 = φ' ∘ all-eqvs-𝟛 ∘ path-to-eqv
  where φ' : {l : 𝟛 == 𝟛} → (path-to-eqv l == ide 𝟛) + (path-to-eqv l == swap12-eqv) + (path-to-eqv l == swap13-eqv) + (path-to-eqv l == swap23-eqv) + (path-to-eqv l == left-shift-eqv) + (path-to-eqv l == right-shift-eqv)
          → (l == refl 𝟛) + (l == ua swap12-eqv) + (l == ua swap13-eqv) + (l == ua swap23-eqv) + (l == ua left-shift-eqv) + (l == ua right-shift-eqv)
        φ' (i₁ α) = {!!} {-i₁ (ap-dpair=-e-out (α ◾ ! (dpair=-β₁ {P = is-type 𝟛} {ux = ∣ refl 𝟛 ∣} _)) (prop-is-set identify _ _ _ _))-}
        φ' _ = {!!}

all-1-paths : (p : `𝟛 == `𝟛) → (p == `id) + (p == `swap12) + (p == `swap13) + (p == `swap23) + (p == `left-shift) + (p == `right-shift)
all-1-paths = {!!}
