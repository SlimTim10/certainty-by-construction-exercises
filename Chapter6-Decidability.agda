module Chapter6-Decidability where

open import Agda.Primitive renaming (Set to Type)

open import Chapter1-Agda
  using (Bool; true; false)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs
  using (_≡_; module PropEq; module ≡-Reasoning; suc-injective)
open PropEq

open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ; _,_)

-- 6.1 Negation

-- Valid, but not what we're going to use.
module Sandbox-Explosion where
  -- Using principle of explosion ("from false, anything is possible").
  _IsFalse : Type → Type₁
  P IsFalse = P → {A : Type} → A

  2≢3 : (2 ≡ 3) IsFalse
  2≢3 ()

-- 6.2 Bottom

-- Rather than showing all contradictions lead to explosion,
-- say that all contradictions lead to a specific type,
-- then show that all values of that type lead to explosion.
module Definition-Bottom where
  data ⊥ : Type where

  2≢3 : 2 ≡ 3 → ⊥
  2≢3 ()

  ⊥-elim : {A : Type} → ⊥ → A
  ⊥-elim ()

  ⊥-unique : {x y : ⊥} → x ≡ y
  ⊥-unique {x} = ⊥-elim x

  ¬_ : {ℓ : Level} → Type ℓ → Type ℓ
  ¬ P = P → ⊥
  infix 3 ¬_

-- 6.3 Inequality
