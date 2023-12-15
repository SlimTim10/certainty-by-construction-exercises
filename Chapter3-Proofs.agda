module Chapter3-Proofs where

open import Chapter1-Agda
  using (Bool; true; false; _∨_; _∧_; not)

open import Chapter2-Numbers
  using (ℕ; zero; suc)

module Example-ProofsAsPrograms where
  open Chapter2-Numbers
    using (ℕ; IsEven)
  open ℕ
  open IsEven

  zero-is-even : IsEven zero
  zero-is-even = zero-even

  -- one-is-even : IsEven (suc zero)
  -- one-is-even = {!!}

module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A}
      → x ≡ x

  infix 4 _≡_

module Playground where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  open Chapter2-Numbers

  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl

  _ : three ≡ suc (suc (suc zero))
  _ = refl

  _ : three ≡ one + two
  _ = refl

  0+x≡x : (x : ℕ) → zero + x ≡ x
  0+x≡x _ = refl

  -- x+0̄≡x : (x : ℕ) → x + zero ≡ x
  -- x+0̄≡x zero = refl
  -- x+0̄≡x (suc x) = {!!}

  postulate
    _ : (x : ℕ)
      → x + zero ≡ x
      → suc (x + zero) ≡ suc x

    _ : {x y : ℕ}
      → x ≡ y
      → suc x ≡ suc y

  cong
    : {A B : Set}
    → {x y : A}
    → (f : A → B)
    → x ≡ y
    → f x ≡ f y
  cong f refl = refl

  x+0̄≡x : (x : ℕ) → x + zero ≡ x
  x+0̄≡x zero = refl
  x+0̄≡x (suc x) = cong suc (x+0̄≡x x)

  -- Left and right identities

  +-identityˡ : (x : ℕ) → zero + x ≡ x
  +-identityˡ = 0+x≡x

  +-identityʳ : (x : ℕ) → x + zero ≡ x
  +-identityʳ = x+0̄≡x

  *-identityˡ : (x : ℕ) → 1 * x ≡ x
  *-identityˡ zero = refl
  *-identityˡ (suc x) = cong suc (+-identityʳ x)

  *-identityʳ : (x : ℕ) → x * 1 ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  ∸-identityʳ : (x : ℕ) → x ∸ 0 ≡ x
  ∸-identityʳ x = refl

  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x
  ^-identityʳ zero = refl
  ^-identityʳ (suc x) = cong suc (*-identityʳ x)

  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ _ = refl

  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ false = refl
  ∨-identityʳ true = refl

  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  ∧-identityˡ x = refl

  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  ∧-identityʳ false = refl
  ∧-identityʳ true = refl

  -- zero elements
  
  *-zeroˡ : (x : ℕ) → zero * x ≡ zero
  *-zeroˡ _ = refl

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true
  ∨-zeroˡ _ = refl

  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true
  ∨-zeroʳ false = refl
  ∨-zeroʳ true = refl

  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false
  ∧-zeroˡ _ = refl

  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false
  ∧-zeroʳ false = refl
  ∧-zeroʳ true = refl

  -- Symmetry and Involutivity

  -- For some reason, the following isn't good enough.
  -- *-identityˡ′ : (x : ℕ) → x ≡ 1 * x
  -- *-identityˡ′ zero = refl
  -- *-identityˡ′ (suc x) = cong suc (*-identityˡ′ x)

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  *-identityˡ′ : (x : ℕ) → x ≡ 1 * x
  -- *-identityˡ′ x = sym (+-identityʳ x)
  *-identityˡ′ x = sym (*-identityˡ x)

  sym-involutive
    : {A : Set} {x y : A}
    → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl

  not-involutive : (x : Bool) → not (not x) ≡ x
  not-involutive false = refl
  not-involutive true = refl

  -- Transitivity
  
  trans
    : {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
  trans refl refl = refl

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + (b * zero)
  a^1≡a+b*0 a b
    = trans (^-identityʳ a)
      ( trans (sym (+-identityʳ a))
        (cong (a +_) (sym (*-zeroʳ b)))
      )

  -- Mixfix for multi-step proof DSL (equational reasoning)

  module ≡-Reasoning where

    _∎ : {A : Set} → (x : A) → x ≡ x
    x ∎ = refl

    infix 3 _∎

    _≡⟨⟩_
      : {A : Set} {y : A}
      → (x : A)
      → x ≡ y
      → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _≡⟨_⟩_
      : {A : Set}
      → (x : A)
      → {y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
    x ≡⟨ j ⟩ p = trans j p

    infixr 2 _≡⟨_⟩_

    begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
    begin_ x≡y = x≡y

    infix 1 begin_

  a^1≡a+b*0′ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0′ a b = begin
    a ^ 1 ≡⟨ ^-identityʳ a ⟩
    a ≡⟨ sym (+-identityʳ a) ⟩
    a + 0 ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
    a + b * 0 ∎
    where open ≡-Reasoning

  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl
  ∧-assoc true b c = refl

  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl
  -- +-assoc (suc x) y z = cong suc (+-assoc x y z)
  +-assoc (suc x) y z = begin
    suc x + y + z ≡⟨⟩
    suc (x + y + z) ≡⟨ cong suc (+-assoc x y z) ⟩
    suc (x + (y + z)) ≡⟨⟩
    suc x + (y + z) ∎
    where open ≡-Reasoning

  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y = begin
    suc x + y ≡⟨⟩
    suc (x + y) ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x) ≡⟨⟩
    suc y + x ≡⟨⟩
    suc (y + x) ≡⟨ sym (+-suc y x) ⟩
    y + suc x ∎
    where open ≡-Reasoning

  suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
  suc-injective refl = refl

  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero y = refl
  *-suc (suc x) y = begin
    suc (y + x * suc y) ≡⟨ cong suc (cong (y +_) (*-suc x y)) ⟩
    suc (y + (x + x * y)) ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
    suc (y + x + x * y) ≡⟨ cong suc (cong (_+ (x * y)) (sym (+-comm x y))) ⟩
    suc (x + y + x * y) ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
    suc (x + (y + x * y)) ∎
    where open ≡-Reasoning

  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero zero = refl
  *-comm zero (suc y) = *-comm zero y
  *-comm (suc x) y = begin
    suc x * y ≡⟨⟩
    y + x * y ≡⟨ cong (y +_) (*-comm x y) ⟩
    y + y * x ≡⟨ sym (*-suc y x) ⟩
    (y * suc x) ∎
    where open ≡-Reasoning

  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
  *-distribʳ-+ x zero z = refl
  *-distribʳ-+ x (suc y) z = begin
    (suc y + z) * x ≡⟨⟩
    x + (y + z) * x ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
    x + (y * x + z * x) ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
    (x + y * x) + z * x ≡⟨⟩
    suc y * x + z * x ∎
    where open ≡-Reasoning

  *-distribˡ-+ : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
  -- *-distribˡ-+ x zero z = sym (cong (_+ (x * z)) (*-zeroʳ x))
  -- *-distribˡ-+ x (suc y) z = begin
  --   x * (suc y + z) ≡⟨ *-comm x (suc (y + z)) ⟩
  --   (suc y + z) * x ≡⟨ *-distribʳ-+ x (suc y) z ⟩
  --   suc y * x + z * x ≡⟨ cong (_+ (z * x)) (*-comm (suc y) x) ⟩
  --   x * suc y + z * x ≡⟨ cong ((x * suc y) +_) (*-comm z x) ⟩
  --   x * suc y + x * z ∎
  --   where open ≡-Reasoning
  *-distribˡ-+ x y z = begin
    x * (y + z) ≡⟨ *-comm x (y + z) ⟩
    (y + z) * x ≡⟨ *-distribʳ-+ x y z ⟩
    y * x + z * x ≡⟨ cong (_+ (z * x)) (*-comm y x) ⟩
    x * y + z * x ≡⟨ cong ((x * y) +_) (*-comm z x) ⟩
    x * y + x * z ∎
    where open ≡-Reasoning

  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-assoc zero y z = refl
  *-assoc (suc x) y z = begin
    suc x * y * z ≡⟨⟩
    (y + x * y) * z ≡⟨ *-distribʳ-+ z y (x * y) ⟩
    y * z + (x * y) * z ≡⟨ cong ((y * z) +_) (*-assoc x y z) ⟩
    y * z + x * (y * z) ≡⟨⟩
    suc x * (y * z) ∎
    where open ≡-Reasoning

open import Relation.Binary.PropositionalEquality
  using (_≡_; module ≡-Reasoning)
  public

module PropEq where
  open Relation.Binary.PropositionalEquality
    using (refl; cong; sym; trans)
    public

open import Data.Bool
  using (if_then_else_)
  public

open import Function
  using (case_of_)
  public

open import Data.Bool.Properties
  using
    ( ∨-identityˡ ; ∨-identityʳ
    ; ∨-zeroˡ ; ∨-zeroʳ
    ; ∨-assoc ; ∧-assoc
    ; ∧-identityˡ ; ∧-identityʳ
    ; ∧-zeroˡ ; ∧-zeroʳ
    ; not-involutive
    )
  public

open import Data.Nat.Properties
  using
    ( +-identityˡ ; +-identityʳ
    ; *-identityˡ ; *-identityʳ
    ; *-zeroˡ ; *-zeroʳ
    ; +-assoc ; *-assoc
    ; +-comm ; *-comm
    ; ^-identityʳ
    ; +-suc ; suc-injective
    ; *-distribˡ-+ ; *-distribʳ-+
    )
  public
