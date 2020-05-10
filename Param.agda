module Param where

open import Data.Maybe
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Agda.Primitive using (_⊔_)

⟦Set⟧ : Set → Set → Set₁
⟦Set⟧ A₀ A₁ = A₀ → A₁ → Set

-- ⟦Maybe⟧ : (A₀ : Set) (A₁ : Set) (Aᵣ : A₀ → A₁ → Set) → Maybe A₀ → Maybe A₁ → Set

data ⟦Maybe⟧ (A₀ : Set) (A₁ : Set) (Aᵣ : A₀ → A₁ → Set) : Maybe A₀ → Maybe A₁ → Set where
  ⟦just⟧    : ∀{a₀ : A₀}{a₁ : A₁}
            → (aᵣ : Aᵣ a₀ a₁)
            → ⟦Maybe⟧ A₀ A₁ Aᵣ (just a₀) (just a₁)
  ⟦nothing⟧ : ⟦Maybe⟧ A₀ A₁ Aᵣ nothing nothing

_⟦>>=⟧_ : {A₀ A₁ : Set} → {Aᵣ : A₀ → A₁ → Set}
      → {B₀ B₁ : Set} → {Bᵣ : B₀ → B₁ → Set}
      → {m₀ : Maybe A₀} → {m₁ : Maybe A₁}
      → (⟦m⟧ : ⟦Maybe⟧ A₀ A₁ Aᵣ m₀ m₁)
      → {c₀ : A₀ → Maybe B₀}
      → {c₁ : A₁ → Maybe B₁}
      → (cᵣ : {a₀ : A₀} → {a₁ : A₁} → (aᵣ : Aᵣ a₀ a₁)
             → ⟦Maybe⟧ B₀ B₁ Bᵣ (c₀ a₀) (c₁ a₁))
      → ⟦Maybe⟧ B₀ B₁ Bᵣ (m₀ >>= c₀) (m₁ >>= c₁)
_⟦>>=⟧_ (⟦just⟧ aᵣ) cᵣ = cᵣ aᵣ
_⟦>>=⟧_ ⟦nothing⟧ cᵣ = ⟦nothing⟧

{- Logical Relation for Co-Products -}
data _⟦⊎⟧_ {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set) {B₀ B₁ : Set} (Bᵣ : B₀ → B₁ → Set) : A₀ ⊎ B₀ → A₁ ⊎ B₁ → Set where
  ⟦inj₁⟧ : ∀{x₀ x₁} → Aᵣ x₀ x₁ → (Aᵣ ⟦⊎⟧ Bᵣ) (inj₁ x₀) (inj₁ x₁)
  ⟦inj₂⟧ : ∀{x₀ x₁} → Bᵣ x₀ x₁ → (Aᵣ ⟦⊎⟧ Bᵣ) (inj₂ x₀) (inj₂ x₁)

⟦Bool⟧ : Bool → Bool → Set
⟦Bool⟧ = _≡_

_⟦->⟧_ : {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set) ->
       {B₀ B₁ : Set} (Bᵣ : B₀ → B₁ → Set) ->
       ⟦Set⟧ (A₀ -> B₀) (A₁ -> B₁)
(Aᵣ ⟦->⟧ Bᵣ) f0 f1 = (x0 : _) → (x1 : _) → Aᵣ x0 x1 → Bᵣ (f0 x0) (f1 x1) 

_⟦→⟧_ : ∀{a} {A₀ A₁ : Set a} (Aᵣ : A₀ → A₁ → Set a) ->
         ∀{b} {B₀ B₁ : Set b} (Bᵣ : B₀ → B₁ → Set b) ->
       (A₀ -> B₀) -> (A₁ -> B₁) -> Set  (a ⊔ b)
(Aᵣ ⟦→⟧ Bᵣ) f0 f1 = (x0 : _) → (x1 : _) → Aᵣ x0 x1 → Bᵣ (f0 x0) (f1 x1) 

infixr 1 _⟦->⟧_

⟦⊤⟧ : ⊤ → ⊤ → Set
⟦⊤⟧ = _≡_


_⟦×⟧_ : {A₀ A₁ : Set} (Aᵣ : A₀ → A₁ → Set) ->
       {B₀ B₁ : Set} (Bᵣ : B₀ → B₁ → Set) ->
       ⟦Set⟧ (A₀ × B₀) (A₁ × B₁)
(Aᵣ ⟦×⟧ Bᵣ) (a0 , b0) (a1 , b1) = Aᵣ a0 a1 × Bᵣ b0 b1

×-id-l : ∀ {A B : Set} {a b : A × B} -> (_≡_ ⟦×⟧ _≡_) a b -> a ≡ b
×-id-l (refl , refl) = refl

×-id-r : ∀ {A B : Set} {a b : A × B} -> a ≡ b -> (_≡_ ⟦×⟧ _≡_) a b
×-id-r refl = (refl , refl)

