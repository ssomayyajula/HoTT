
T⟦_⟧ : ℕ → U
T⟦   0   ⟧ = ZERO
T⟦ suc n ⟧ = PLUS ONE T⟦ n ⟧

{-
size-T : (n : ℕ) → size T⟦ n ⟧ == n
size-T 0       = refl 0
size-T (suc n) = ap suc (size-T n)

-- Quite a bit of induction
size-eq : {X Y : U} → X ⟷ Y → size X == size Y
size-eq = {!!}

⟦_⟧ₜ : (t : U) → U[ Fin (size t) ]
⟦ t ⟧ₜ = `Fin (size t)
-}


`⟦_⟧ₜ : (t : U) → U[ ⟦ t ⟧ₜ ]
`⟦ t ⟧ₜ = lift ⟦ t ⟧ₜ

⟦_⟧₁' : {X : U} → (t : X ⟷ X) → `⟦ X ⟧ₜ == `⟦ X ⟧ₜ
⟦ _ ⟧₁' = {!!}

tr : (n : ℕ) → ⟦ T⟦ n ⟧ ⟧ₜ == AFin n
tr 0       = refl (AFin 0)
tr (suc n) = ap ((_+_) 𝟙) (tr n)

cmpl1' : {n : ℕ} (p : `Fin n == `Fin n) → Σ (T⟦ n ⟧ ⟷ T⟦ n ⟧)
  (λ `p → tpt (λ m → lift m == lift m) (tr n ◾ ua afin-fin-equiv) ⟦ `p ⟧₁' == p)
cmpl1' = {!!}

cmpl1-lem : {X Y : U} → (p : CPerm (size X) (size Y)) → Σ (X ⟷ Y) (λ `p → ⟦ `p ⟧ₚ == p)
cmpl1-lem = {!!}

{-
norm : (X : U) → ⟦ X ⟧ₜ ≃ Fin (size X)
norm ZERO = {!!}
norm ONE = {!!} --(i₁ , qinv-is-equiv ((λ { (i₁ x) → x; (i₂ ()) }) , refl , (λ { (i₁ x) → refl (i₁ x); (i₂ ()) })))
norm (PLUS X Y) = let (fx , ex) = norm X in
                  let (fy , ey) = norm Y in
                  let (gx , εx , ηx) = hae-is-qinv ex in
                  let (gy , εy , ηy) = hae-is-qinv ey in
                  (λ { (i₁ x) → inject+ (size Y) (fx x);
                       (i₂ y) → let l = inject+ (size X) (fy y) in {!!} }) ,
                  qinv-is-equiv ({!!} , {!!} , {!!})
-}


