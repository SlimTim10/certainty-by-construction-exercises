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

  _≢_ : {A : Type} → A → A → Type
  x ≢ y = ¬ x ≡ y
  infix 4 _≢_

  ≢-sym : {A : Type} → {x y : A} → x ≢ y → y ≢ x
  ≢-sym x≢y y≡x = x≢y (sym y≡x)

  -- Helpful for proving that inequality is not reflexive.
  Reflexive
    : {c ℓ : Level} {A : Type c}
    → (A → A → Type ℓ)
    → Type (ℓ ⊔ c)
  Reflexive {A = A} _≈_ = {x : A} → x ≈ x

  -- Example showing equality is reflexive.
  ≡-refl : {A : Type} → Reflexive {A = A} _≡_
  ≡-refl = refl

  ¬≢-refl : ¬ ({A : Type} → Reflexive {A = A} _≢_)
  ¬≢-refl ¬≡-refl = ¬≡-refl {ℕ} {0} refl

-- 6.4 Negation Considered as a Callback
