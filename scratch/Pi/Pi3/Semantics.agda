module Reversible.Pi3.Semantics where

open import UnivalentTypeTheory
open import Reversible.UnivalentFibrations as UF
open import Reversible.Pi3.ThreeUniverse as M
open import Reversible.Pi3.Syntax as S

------------------------------------------------------------------------------
-- Soundness: mapping syntax to the model

⟦_⟧ : U → U[ 𝟛 ]
⟦ `𝟛 ⟧ = M.`𝟛

⟦_⟧₁ : {A B : U} → A ⟷₁ B → ⟦ A ⟧ == ⟦ B ⟧
⟦_⟧₁ `swap12 = M.`swap12
⟦_⟧₁ `swap13 = M.`swap13
⟦_⟧₁ (!₁ p) = ! ⟦ p ⟧₁
⟦_⟧₁ (p ◾₁ q) = ⟦ p ⟧₁ ◾ ⟦ q ⟧₁

-- Completeness: mapping model to syntax
