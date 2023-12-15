{-# OPTIONS --allow-unsolved-metas #-}

module Chapter1-Agda where

open import Data.Product using () renaming (_×_ to _,_)
open import Relation.Binary.PropositionalEquality

module Booleans where
  data Bool : Set where
    false : Bool
    true : Bool

  not : Bool → Bool
  not false = true
  not true = false

  _ : not (not false) ≡ false
  _ = refl

  _∨_ : Bool → Bool → Bool
  false ∨ other = other
  true ∨ other = true

  _∧_ : Bool → Bool → Bool
  true ∧ other = other
  false ∧ other = false

open import Data.Bool
  using (Bool; false; true; not; _∨_; _∧_)
  public

open import Data.Product
  using (_×_; _,_; proj₁; proj₂; curry; uncurry)
  public

open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public
