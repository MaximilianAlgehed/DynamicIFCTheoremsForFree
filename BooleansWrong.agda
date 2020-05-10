module BooleansWrong where

open import Data.Unit
open import Data.Empty

record Booleans : Set₁ where
  field
    Bool  : Set
    true  : Bool
    false : Bool
    neg : Bool -> Bool
    ∧ : Bool -> Bool -> Bool

module Impl where
  data Bool : Set where
    true  : Bool
    false : Bool
  ∧ : Bool -> Bool -> Bool
  ∧ false _ = false
  ∧ _ b = b
  neg : Bool -> Bool
  neg true = false
  neg false = true

module Extras where
  open Impl
  _⇒_ : Bool -> Bool -> Set
  _⇒_ false _ = ⊤
  _⇒_ _ true = ⊤
  _⇒_ _ _ = ⊥

booleans : Booleans
booleans = record {Impl}

open Booleans
record ⟦Booleans⟧ (m₀ : Booleans) (m₁ : Booleans) : Set₁ where
  field
    Boolᵣ : Bool m₀ -> Bool m₁ -> Set
    trueᵣ : Boolᵣ (true m₀) (true m₁)
    falseᵣ : Boolᵣ (false m₀) (false m₁)
    negᵣ : ∀ a₀ a₁ -> Boolᵣ a₀ a₁ -> Boolᵣ (neg m₀ a₀) (neg m₁ a₁)
    ∧ᵣ : ∀ a₀ a₁ -> Boolᵣ a₀ a₁ ->
             ∀ b₀ b₁ -> Boolᵣ b₀ b₁ ->
             Boolᵣ (∧ m₀ a₀ b₀) (∧ m₁ a₁ b₁)

open Extras

module Implᵣ where
    m₀ = booleans
    m₁ = booleans
    Boolᵣ : Bool m₀ -> Bool m₁ -> Set
    Boolᵣ = _⇒_
    trueᵣ : Boolᵣ (true m₀) (true m₁)
    trueᵣ = tt
    falseᵣ : Boolᵣ (false m₀) (false m₁)
    falseᵣ = tt
    ∧ᵣ : ∀ a₀ a₁ -> Boolᵣ a₀ a₁ ->
         ∀ b₀ b₁ -> Boolᵣ b₀ b₁ ->
           Boolᵣ (∧ m₀ a₀ b₀) (∧ m₁ a₁ b₁)
    ∧ᵣ Impl.true Impl.true aᵣ b₀ b₁ bᵣ = bᵣ
    ∧ᵣ Impl.false a₁ aᵣ b₀ b₁ bᵣ = tt
    negᵣ : ∀ a₀ a₁ -> Boolᵣ a₀ a₁ -> Boolᵣ (neg m₀ a₀) (neg m₁ a₁)
    negᵣ Impl.true Impl.true x = tt
    negᵣ Impl.false Impl.true tt = {!!} -- trying to prove true ==> false
    negᵣ Impl.false Impl.false x = tt
