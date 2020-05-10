module Booleans where

-- open import Data.Unit
-- open import Data.Empty

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record Booleans : Set₁ where
  field
    Bool  : Set
    true  : Bool
    false : Bool
    ∧ : Bool -> Bool -> Bool

module Impl where
  data Bool : Set where
    true  : Bool
    false : Bool
  ∧ : Bool -> Bool -> Bool
  ∧ false _ = false
  ∧ _ b = b

module Extras where
  open Impl
  _⇒_ : Bool -> Bool -> Set
  true ⇒ false = ⊥
  _    ⇒ _     = ⊤

booleans : Booleans
booleans = record {Impl}

open Booleans
record ⟦Booleans⟧ (m₀ : Booleans) (m₁ : Booleans) : Set₁ where
  field
    Boolᵣ : Bool m₀ -> Bool m₁ -> Set
    trueᵣ : Boolᵣ (true m₀) (true m₁)
    falseᵣ : Boolᵣ (false m₀) (false m₁)
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

booleansᵣ : ⟦Booleans⟧ booleans booleans
booleansᵣ = record {Implᵣ }

open ⟦Booleans⟧
open Extras
monotonicity : (o : (m : Booleans) -> Bool m -> Bool m) ->
               (oᵣ : (m₀ m₁ : Booleans) ->
                     (mᵣ : ⟦Booleans⟧ m₀ m₁) ->
                     ∀ x₀ x₁ -> Boolᵣ mᵣ x₀ x₁ -> Boolᵣ mᵣ (o m₀ x₀) (o m₁ x₁)) ->
               ∀ b₀ b₁ -> b₀ ⇒ b₁ -> (o booleans b₀) ⇒ (o booleans b₁)
monotonicity _ oᵣ = oᵣ booleans booleans booleansᵣ

