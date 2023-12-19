module Chapter4-Relations where

open import Agda.Primitive renaming (Set to Type)

open import Chapter1-Agda
  using (Bool; false; true; not; _×_)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)

module Playground-Level where
  data Maybe₀ (A : Type): Type where
    just₀ : A → Maybe₀ A
    nothing₀ : Maybe₀ A

  -- Doesn't work
  -- _ = just₀ ℕ

  data Maybe₁ {ℓ : Level} (A : Type ℓ) : Type ℓ where
    just₁ : A → Maybe₁ A
    nothing₁ : Maybe₁ A

  _ = just₁ ℕ

  private variable
    ℓ : Level

  data Maybe₂ (A : Type ℓ) : Type ℓ where
    just₂ : A → Maybe₂ A
    nothing₂ : Maybe₂ A

private variable
  ℓ ℓ₁ ℓ₂ a b c : Level
  A : Type a
  B : Type b
  C : Type c

module Definition-DependentPair where
  record Σ (A : Type ℓ₁) (B : A → Type ℓ₂)
         : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  ∃n,n+1≡5 : Σ ℕ (λ n → n + 1 ≡ 5)
  ∃n,n+1≡5 = 4 , PropEq.refl

open import Data.Product
  using (Σ; _,_)

-- Defining heterogeneous relations in general

module Sandbox-Relations where
  REL
    : Type a → Type b → (ℓ : Level)
    → Type (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Type ℓ

  data Unrelated : REL A B lzero where

  data Related : REL A B lzero where
    related : {a : A} {b : B} → Related a b

  -- Transforming functions into relations
  
  data _maps_↦_ (f : A → B) : REL A B lzero where
    app : {x : A} → f maps x ↦ f x

  _ : not maps false ↦ true
  _ = app

  _ : not maps true ↦ false
  _ = app

  -- Doesn't typecheck
  -- _ : not maps false ↦ false
  -- _ = app

  -- Transforming relations into functions
  
  Functional : REL A B ℓ → Type _
  Functional {A = A} {B = B} _~_
    = {x : A} {y z : B}
    → x ~ y → x ~ z
    → y ≡ z

  Total : REL A B ℓ → Type _
  Total {A = A} {B = B} _~_
    = (x : A) → Σ B (λ y → x ~ y)

  relToFn : (_~_ : REL A B ℓ)
    → Functional _~_
    → Total _~_
    → A → B
  relToFn _~_ _ total x
    with total x
  ... | y , _ = y

  -- Homogeneous relations (relating two elements of the same type)

  Rel : Type a → (ℓ : Level) → Type (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ

  -- Standard properties of relations (reflexivity, symmetry, transitivity)
  -- Some relations may have these properties.

  Reflexive : Rel A ℓ → Type _
  Reflexive {A = A} _~_
    = {x : A} → x ~ x

  Symmetric : Rel A ℓ → Type _
  Symmetric {A = A} _~_
    = {x y : A} → x ~ y → y ~ x

  Transitive : Rel A ℓ → Type _
  Transitive {A = A} _~_
    = {x y z : A} → x ~ y → y ~ z → x ~ z

-- Attempting to order the naturals

-- Use what we built above, but from the standard library.
open import Relation.Binary
  using (Rel; Reflexive; Transitive; Symmetric)

-- A naive attempt.
module Naive-≤₁ where
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ a + b
  infix 4 _≤_

  _ : 2 ≤ 5
  _ = lte 2 3

  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono (lte x y) = lte (suc x) y

  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = lte zero zero
  ≤-refl {suc x} with ≤-refl {x}
  ... | x≤x = suc-mono x≤x

  open Chapter3-Proofs
    using (+-identityʳ)

  -- It's nice to know that subst exists, but as a good rule of thumb, it's usually the wrong tool for the job.
  subst
    : {x y : A}
    → (P : A → Type ℓ)
    → x ≡ y
    → P x → P y
  subst _ PropEq.refl px = px

  ≤-refl′ : Reflexive _≤_
  ≤-refl′ {x} = subst (λ φ → x ≤ φ) (+-identityʳ x) (lte x 0)

-- The real definition.
module Definition-LessThanOrEqualTo where
  data _≤_ : Rel ℕ lzero where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
  infix 4 _≤_

open import Data.Nat
  using (_≤_; z≤n; s≤s)

module Sandbox-≤ where
  _ : 2 ≤ 5
  _ = s≤s (s≤s z≤n)

  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono = s≤s

  ≤-refl : {x : ℕ} → x ≤ x
  ≤-refl {zero} = z≤n
  ≤-refl {suc x} = s≤s ≤-refl

  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n y≤z = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

-- Preorders
-- Can be thought of as directed graphs.

module Sandbox-Preorders where
  open Sandbox-≤

  record IsPreorder {A : Type a} (_~_ : Rel A ℓ) : Type (a ⊔ ℓ) where
    field
      refl : Reflexive _~_
      trans : Transitive _~_

  ≤-preorder : IsPreorder _≤_
  ≤-preorder = record { refl = ≤-refl ; trans = ≤-trans }

  ≡-preorder : IsPreorder (_≡_ {A = A})
  ≡-preorder = record { refl = PropEq.refl ; trans = PropEq.trans }

  -- Exercise: prove that Sandbox-Relations.Unrelated and Sandbox-Relations.Related are preorders.
  
  open Sandbox-Relations using (Unrelated; Related; related)
  
  Unrelated-preorder : IsPreorder (Unrelated {A = A})
  -- IsPreorder.refl Unrelated-preorder = {!!}
  Unrelated-preorder = record { refl = {!!} ; trans = {!!} }
  
  Related-preorder : IsPreorder (Related {A = A})
  Related-preorder = record { refl = related ; trans = λ _ _ → related }

  -- Syntactic sugar for preorder reasoning like for equational reasoning
  
  module Preorder-Reasoning
    {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where

    open IsPreorder ~-preorder public

    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y
    infix 1 begin_

    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎

    _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≡⟨⟩ p = p
    infixr 2 _≡⟨⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_

  -- Using preorder reasoning

  n≤1+n : (n : ℕ) → n ≤ 1 + n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  open Chapter3-Proofs using (+-comm)
  
  n≤n+1 : (n : ℕ) → n ≤ n + 1
  n≤n+1 n = begin
    n ≈⟨ n≤1+n n ⟩
    1 + n ≡⟨ +-comm 1 n ⟩
    n + 1 ∎
    where open Preorder-Reasoning ≤-preorder

  -- Offer better syntax for the this specific preorder
  module ≤-Reasoning where
    open Preorder-Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public

  n≤n+1′ : (n : ℕ) → n ≤ n + 1
  n≤n+1′ n = begin
    n ≤⟨ n≤1+n n ⟩
    1 + n ≡⟨ +-comm 1 n ⟩
    n + 1 ∎
    where open ≤-Reasoning

  -- Graphs reachability

  -- Define _⇒_ as an arbitrary relation.
  module Reachability {V : Type ℓ₁} (_⇒_ : Rel V ℓ₂) where
    private variable
      v v₁ v₂ v₃ : V

    -- Take the arbitrary relation _⇒_ and extend it into a preorder.
    -- Path is just _⇒_ but with "here" and "connect".
    data Path : Rel V (ℓ₁ ⊔ ℓ₂) where
      ↪_ : v₁ ⇒ v₂ → Path v₁ v₂
      here : Path v v
      connect : Path v₁ v₂ → Path v₂ v₃ → Path v₁ v₃

    -- Path is a "free preorder".
    Path-preorder : IsPreorder Path
    Path-preorder = record { refl = here ; trans = connect }

  -- Free preorder: About a Boy

  module Example-AboutABoy where
    data Person : Type where
      ellie fiona marcus rachel susie will : Person

    private variable
      p₁ p₂ : Person

    data _IsFriendsWith_ : Rel Person lzero where
      marcus-will : marcus IsFriendsWith will
      marcus-fiona : marcus IsFriendsWith fiona
      fiona-susie : fiona IsFriendsWith susie
      -- Friendship is symmetric
      sym : p₁ IsFriendsWith p₂ → p₂ IsFriendsWith p₁
    
    data _IsInterestedIn_ : Rel Person lzero where
      marcus-ellie : marcus IsInterestedIn ellie
      will-rachel : will IsInterestedIn rachel
      rachel-will : rachel IsInterestedIn will
      susie-will : susie IsInterestedIn will

    data SocialTie : Rel Person lzero where
      friendship : p₁ IsFriendsWith p₂ → SocialTie p₁ p₂
      interest : p₁ IsInterestedIn p₂ → SocialTie p₁ p₂

    open Reachability SocialTie

    will-fiona : Path will fiona
    will-fiona = begin
      will ≈⟨ ↪ friendship (sym marcus-will) ⟩
      marcus ≈⟨ ↪ friendship marcus-fiona ⟩
      fiona ∎
      where open Preorder-Reasoning Path-preorder

    rachel-ellie : Path rachel ellie
    rachel-ellie = begin
      rachel ≈⟨ ↪ interest rachel-will ⟩
      will ≈⟨ ↪ friendship (sym marcus-will) ⟩
      marcus ≈⟨ ↪ interest marcus-ellie ⟩
      ellie ∎
      where open Preorder-Reasoning Path-preorder

  -- Antisymmetry
  
  ≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl
  ≤-antisym (s≤s m≤n) (s≤s n) = PropEq.cong suc (≤-antisym m≤n n)

  Antisymmetric
    : Rel A ℓ₁
    → Rel A ℓ₂
    → Type _
  Antisymmetric _≈_ _≤_ =
    ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

  _ : Antisymmetric _≡_ _≤_
  _ = ≤-antisym


  record IsEquivalence {A : Type a} (_~_ : Rel A ℓ) : Type (a ⊔ ℓ) where
    field
      isPreorder : IsPreorder _~_
      sym : Symmetric _~_

    open IsPreorder isPreorder public

  -- Can be thought of as directed acyclic graphs.
  record IsPartialOrder {A : Type a} (_~_ : Rel A ℓ) : Type (a ⊔ ℓ) where
    field
      isPreorder : IsPreorder _~_
      antisym : Antisymmetric _≡_ _~_

  ≡-equiv : IsEquivalence (_≡_ {A = A})
  ≡-equiv = record { isPreorder = ≡-preorder ; sym = PropEq.sym }

  ≤-poset : IsPartialOrder _≤_
  ≤-poset = record { isPreorder = ≤-preorder ; antisym = ≤-antisym }

-- Exports

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
  public

open import Data.Product
  using (Σ; _,_)
  public

open import Relation.Binary
  using (Rel; REL; Transitive; Reflexive; Symmetric; Antisymmetric)
  public

open import Relation.Binary.PropositionalEquality
  using (subst)
  public

open import Data.Nat
  using (_≤_; z≤n; s≤s; _<_)
  public

open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; n≤1+n; module ≤-Reasoning)
  public

-- Standard library definitions can be found under Relation.Binary
open Sandbox-Preorders
  using
    ( IsPreorder; IsEquivalence; IsPartialOrder
    ; module Preorder-Reasoning
    ; ≡-preorder; ≡-equiv
    ; ≤-preorder; ≤-poset
    )
  public
