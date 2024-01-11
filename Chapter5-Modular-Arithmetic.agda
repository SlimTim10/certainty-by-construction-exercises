module Chapter5-Modular-Arithmetic where

open import Agda.Primitive renaming (Set to Type)

open import Chapter1-Agda

open import Chapter2-Numbers

open import Chapter3-Proofs
open PropEq using (cong)

open import Chapter4-Relations

module Playground-Instances where
  open PropEq

  default : {ℓ : Level} {A : Type ℓ} → ⦃ a : A ⦄ → A
  default ⦃ val ⦄ = val

  private instance
    default-ℕ : ℕ
    default-ℕ = 0

    default-Bool : Bool
    default-Bool = false

  _ : default ≡ 0
  _ = refl

  _ : default ≡ false
  _ = refl

  private instance
    find-z≤n : {n : ℕ} → 0 ≤ n
    find-z≤n = z≤n

    find-s≤n
      : {m n : ℕ}
      → ⦃ m ≤ n ⦄
      → suc m ≤ suc n
    find-s≤n ⦃ m≤n ⦄ = s≤s m≤n

  _ : 10 ≤ 20
  _ = default

module Playground-Instances₂ where

  record HasDefault {ℓ : Level} (A : Type ℓ) : Type ℓ where
    constructor default-of
    field
      the-default : A

  default : {ℓ : Level} {A : Type ℓ} → ⦃ HasDefault A ⦄ → A
  default ⦃ default-of val ⦄ = val

  private instance
    _ = default-of 0
    _ = default-of false

  _ : default ≡ 0
  _ = PropEq.refl

-- No need to write default by hand. This does the same thing, with the-default:
  open HasDefault ⦃ ... ⦄

  _ : the-default ≡ 0
  _ = PropEq.refl

-- Solve our problem of having too many refls:
open IsEquivalence ⦃ ... ⦄ public

-- Turn an instance of IsEquivalence into an instance of IsPreorder.
instance
  equiv-to-preorder
    : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {_~_ : Rel A ℓ₂}
    → ⦃ IsEquivalence _~_ ⦄
    → IsPreorder _~_
  equiv-to-preorder = isPreorder

  -- For overloaded terms to find propositional equality immediately:
  ≡-is-equivalence = ≡-equiv

-- Modular arithmetic
-- The ring of natural numbers modulo N

module ℕ/nℕ (n : ℕ) where

  record _≈_ (a b : ℕ) : Type where
    constructor ≈-mod
    field
      x y : ℕ
      is-mod : a + x * n ≡ b + y * n

  infix 4 _≈_

  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 refl

  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y is-mod) = ≈-mod y x (sym is-mod)

  lemma₁ : (a x z : ℕ) → a + (x + z) * n ≡ (a + x * n) + z * n
  lemma₁ a x z = begin
    a + (x + z) * n ≡⟨ cong (a +_) (*-distribʳ-+ n x z) ⟩
    a + (x * n + z * n) ≡⟨ sym (+-assoc a _ _) ⟩
    (a + x * n) + z * n ∎
    where open ≡-Reasoning

  lemma₂ : (i j k : ℕ) → (i + j) + k ≡ (i + k) + j
  lemma₂ i j k = begin
    (i + j) + k ≡⟨ +-assoc i j k ⟩
    i + (j + k) ≡⟨ cong (i +_) (+-comm j k) ⟩
    i + (k + j) ≡⟨ sym (+-assoc i k j) ⟩
    (i + k) + j ∎
    where open ≡-Reasoning

  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y)
    ( begin
      a + (x + z) * n ≡⟨ lemma₁ a x z ⟩
      a + x * n + z * n ≡⟨ cong (_+ z * n) pxy ⟩
      b + y * n + z * n ≡⟨ lemma₂ b (y * n) (z * n) ⟩
      b + z * n + y * n ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n ≡⟨ sym (lemma₁ c w y) ⟩
      c + (w + y) * n ∎
    )
    where open ≡-Reasoning

  -- Having shown reflexivity, symmetry, and transitivity, it's clear _≈_ is an equivalence relation!
  ≈-preorder : IsPreorder _≈_
  ≈-preorder = record { refl = ≈-refl ; trans = ≈-trans }

  ≈-equiv : IsEquivalence _≈_
  ≈-equiv = record { isPreorder = ≈-preorder ; sym = ≈-sym }

  -- Drop the fact that _≈_ is an equivalence relation into the instance environment.
  instance
    _ = ≈-equiv

  -- Get reasoning syntax for our new preorder (Preorder-Reasoning module comes from previous chapter).
  module Mod-Reasoning where
    open Preorder-Reasoning ≈-preorder
      hiding (refl; trans)
      public

  -- 5.4

  -- Trivial proofs before interesting ones.
  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 refl

  suc-cong-mod : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  suc-cong-mod (≈-mod x y is-mod) = ≈-mod x y (cong suc is-mod)

  -- More interesting proofs.
  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
  +-zero-mod a zero a≈0 = begin
    a + zero ≡⟨ +-identityʳ a ⟩
    a ≈⟨ a≈0 ⟩
    zero ∎
    where open Mod-Reasoning
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b ≡⟨ +-suc a b ⟩
    suc a + b ≡⟨⟩
    suc (a + b) ≈⟨ suc-cong-mod (+-zero-mod a b a≈0) ⟩
    suc b ∎
    where open Mod-Reasoning

  suc-injective-mod : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  suc-injective-mod (≈-mod x y is-mod) = ≈-mod x y (suc-injective is-mod)

  +-cong₂-mod : {a b c d : ℕ}
    → a ≈ b → c ≈ d
    → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c ≈⟨ pcd ⟩
    d ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d ∎
    where open Mod-Reasoning
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc (a + c) ≈⟨ +-zero-mod (suc a) c pab ⟩
    c ≈⟨ pcd ⟩
    d ∎
    where open Mod-Reasoning
  +-cong₂-mod {suc a} {suc b} {c} {d} pab pcd = suc-cong-mod (+-cong₂-mod (suc-injective-mod pab) pcd)

  -- 5.5

  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero b b=0 = ≈-mod b b refl
  *-zero-mod (suc a) b b=0 = begin
    suc a * b ≡⟨⟩
    b + a * b ≈⟨ +-cong₂-mod b=0 (*-zero-mod a b b=0) ⟩
    0 ∎
    where open Mod-Reasoning

  *-cong₂-mod : {a b c d : ℕ}
    → a ≈ b
    → c ≈ d
    → a * c ≈ b * d
  *-cong₂-mod {zero} {b} {c} {d} a=b c=d = begin
    zero ≈⟨ sym (*-zero-mod d b (sym a=b)) ⟩
    d * b ≡⟨ *-comm d b ⟩
    b * d ∎
    where open Mod-Reasoning
  *-cong₂-mod {suc a} {zero} {c} {d} a=b c=d = begin
    c + a * c ≡⟨ *-comm (suc a) c ⟩
    c * suc a ≈⟨ *-zero-mod c (suc a) a=b ⟩
    zero ∎
    where open Mod-Reasoning
  *-cong₂-mod {suc a} {suc b} {c} {d} a=b c=d = begin
    c + a * c ≈⟨ +-cong₂-mod c=d (*-cong₂-mod (suc-injective-mod a=b) c=d) ⟩
    d + b * d ∎
    where open Mod-Reasoning
