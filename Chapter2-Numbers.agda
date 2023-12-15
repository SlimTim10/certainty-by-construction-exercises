module Chapter2-Numbers where

import Chapter1-Agda

module Definition-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three

  open Chapter1-Agda
    using (Bool; true; false)

  -- Don't use Bool in general. Just for now.
  
  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc _) = false

  n=2? : ℕ → Bool
  n=2? zero = false
  n=2? (suc zero) = false
  n=2? (suc (suc zero)) = true
  n=2? (suc (suc (suc _))) = false

  even? : ℕ → Bool
  even? zero = true
  even? (suc zero) = false
  even? (suc (suc x)) = even? x

  module Sandbox-Usable where
    postulate
      Usable : Set
      Unusable : Set

    IsEven : ℕ → Set
    IsEven zero = Usable
    IsEven (suc zero) = Unusable
    IsEven (suc (suc x)) = IsEven x

  -- Indexed type
  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)

  -- three-is-even : IsEven three
  -- three-is-even = suc-suc-even {!!}

  -- Exercise: Build an indexed type for IsOdd
  data IsOdd : ℕ → Set where
    one-odd : IsOdd one
    suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

  three-is-odd : IsOdd three
  three-is-odd = suc-suc-odd one-odd

  -- four-is-odd : IsOdd four
  -- four-is-odd = suc-suc-odd (suc-suc-odd {!!})

  -- Exercise: Write an inductive funciton which witnesses the fact that every even number is followed by an odd number.
  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd zero-even = one-odd
  evenOdd (suc-suc-even x) = suc-suc-odd (evenOdd x)

  data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x = just (suc-suc-even x)
  ... | nothing = nothing

  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)

  infixl 6 _+_

  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = b + (a * b)

  infixl 7 _*_

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = one
  a ^ suc b = a * (a ^ b)

  _∸_ : ℕ → ℕ → ℕ
  zero ∸ b = zero
  a ∸ zero = a
  suc a ∸ suc b = a ∸ b

  module Natural-Tests where
    open import Relation.Binary.PropositionalEquality

    _ : three ∸ one ≡ two
    _ = refl

module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]

  suc : ℤ → ℤ
  suc (+ x) = + ℕ.suc x
  suc -[1+ ℕ.zero ] = 0ℤ
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -1ℤ
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ] = -[1+ ℕ.suc x ]

  -- -_ : ℤ → ℤ
  -- - (+ ℕ.zero) = 0ℤ
  -- - (+ ℕ.suc x) = -[1+ x ]
  -- - -[1+ x ] = + ℕ.suc x

  pattern +[1+_] n = + ℕ.suc n
  pattern +0 = + ℕ.zero

  -_ : ℤ → ℤ
  - +0 = +0
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]

  -- _+_ : ℤ → ℤ → ℤ
  -- +0 + y = y
  -- +[1+ x ] + +0 = +[1+ x ]
  -- +[1+ x ] + +[1+ y ] = +[1+ 1 ℕ.+ x ℕ.+ y ]
  -- +[1+ x ] + -[1+ y ] = {!!}
  -- -[1+ x ] + +0 = -[1+ x ]
  -- -[1+ x ] + +[1+ y ] = {!!}
  -- -[1+ x ] + -[1+ y ] = -[1+ 1 ℕ.+ x ℕ.+ y ]

  _⊖_ : ℕ → ℕ → ℤ
  ℕ.zero ⊖ ℕ.zero = 0ℤ
  ℕ.zero ⊖ ℕ.suc y = -[1+ y ]
  ℕ.suc x ⊖ ℕ.zero = +[1+ x ]
  ℕ.suc x ⊖ ℕ.suc y = x ⊖ y

  module Integer-Tests where
    open import Relation.Binary.PropositionalEquality

    _ : 3 ⊖ 2 ≡ 1ℤ
    _ = refl

    _ : 2 ⊖ 3 ≡ -1ℤ
    _ = refl

  infixl 5 _+_
  _+_ : ℤ → ℤ → ℤ
  (+ x) + (+ y) = + (x ℕ.+ y)
  (+ x) + -[1+ y ] = x ⊖ ℕ.suc y
  -[1+ x ] + (+ y) = y ⊖ ℕ.suc x
  -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]

  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)

  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0 = +0
  x * +[1+ ℕ.zero ] = x
  x * +[1+ ℕ.suc y ] = (+[1+ y ] * x) + x
  x * -[1+ ℕ.zero ] = - x
  x * -[1+ ℕ.suc y ] = (-[1+ y ] * x) - x

  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : - (+ 2) * - (+ 6) ≡ + 12
    _ = refl

    _ : (+ 3) - (+ 10) ≡ - (+ 7)
    _ = refl

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public

open Sandbox-Naturals
  using (one; two; three; four)
  public

open Sandbox-Naturals
  using (IsEven)
  renaming (zero-even to z-even; suc-suc-even to ss-even)
  public

open import Data.Maybe
  using (Maybe; just; nothing)
  public
