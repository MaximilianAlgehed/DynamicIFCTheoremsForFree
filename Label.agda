module Label where

open import Param

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Function
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

record Interface : Set1 where
  field
    L      : Set
    _⊑_    : L → L → Set
    _⊑d_   : (ℓ₀ ℓ₁ : L) → Dec (ℓ₀ ⊑ ℓ₁)
    ⊑-refl : ∀{ℓ} → ℓ ⊑ ℓ
    ⊑-trans : ∀{ℓ₀ ℓ₁ ℓ₂} → ℓ₀ ⊑ ℓ₁ → ℓ₁ ⊑ ℓ₂ → ℓ₀ ⊑ ℓ₂
    _⊔_ : L → L → L
    ⊔-mono : ∀{ℓ₀ ℓ₁} → ℓ₀ ⊑ (ℓ₀ ⊔ ℓ₁)
    ⊔-comm : ∀{ℓ₀ ℓ₁} → ℓ₀ ⊔ ℓ₁ ≡ ℓ₁ ⊔ ℓ₀
    ⊔-least-upper : ∀{ℓ₀ ℓ₁ ℓ₂} → ℓ₀ ⊑ ℓ₂ → ℓ₁ ⊑ ℓ₂ → (ℓ₀ ⊔ ℓ₁) ⊑ ℓ₂
    ℓ*     : L

  canFlowTo? = _⊑d_
  canFlowTo = _⊑_
  lub = _⊔_
  _̷⊑_ : L → L → Set
  ℓ₀ ̷⊑ ℓ₁ = ¬ (ℓ₀ ⊑ ℓ₁)

  _⋢_ = _̷⊑_

  ⟦L⟧ : ⟦Set⟧ L L
  ⟦L⟧ = _≡_

  ⊑-eql : ∀{ℓ₀ ℓ₁} → ℓ₀ ≡ ℓ₁ → ℓ₀ ⊑ ℓ₁
  ⊑-eql refl = ⊑-refl


module MkLH where
  data Label : Set where
    H L : Label

  _⊑_ : Label -> Label -> Set
  _⊑_ L H = ⊥
  _⊑_ _ _ = ⊤

  canFlowTo? : (ℓ₀ ℓ₁ : Label) → Dec (ℓ₀ ⊑ ℓ₁)
  canFlowTo? H H = yes tt
  canFlowTo? H L = yes tt
  canFlowTo? L H = no λ x → x
  canFlowTo? L L = yes tt

  _⊔_ : Label -> Label -> Label
  _⊔_ H H = H
  _⊔_ _ _ = L

  ⊔-comm : {ℓ₀ ℓ₁ : Label} -> (ℓ₀ ⊔ ℓ₁) ≡ (ℓ₁ ⊔ ℓ₀)
  ⊔-comm {H} {H} = refl
  ⊔-comm {H} {L} = refl
  ⊔-comm {L} {H} = refl
  ⊔-comm {L} {L} = refl

  ⊔-mono : {ℓ₀ ℓ₁ : Label} -> ℓ₀ ⊑ (ℓ₀ ⊔ ℓ₁) 
  ⊔-mono {H} {H} = tt
  ⊔-mono {H} {L} = tt
  ⊔-mono {L} {H} = tt
  ⊔-mono {L} {L} = tt

  ⊑-refl : ∀{ℓ} → ℓ ⊑ ℓ
  ⊑-refl {H} = tt
  ⊑-refl {L} = tt

  ⊑-trans : ∀{ℓ₀ ℓ₁ ℓ₂} → ℓ₀ ⊑ ℓ₁ → ℓ₁ ⊑ ℓ₂ → ℓ₀ ⊑ ℓ₂
  ⊑-trans {H} {H} {c} = λ _ _ → tt
  ⊑-trans {H} {L} {c} = λ _ _ → tt
  ⊑-trans {L} {H} {c} = λ ()
  ⊑-trans {L} {L} {c} = λ _ z → z

  ⊔-least-upper : ∀{ℓ₀ ℓ₁ ℓ₂} → ℓ₀ ⊑ ℓ₂ → ℓ₁ ⊑ ℓ₂ → (ℓ₀ ⊔ ℓ₁) ⊑ ℓ₂
  ⊔-least-upper {H} {H} {c} = λ _ _ → tt
  ⊔-least-upper {H} {L} {c} = λ _ z → z
  ⊔-least-upper {L} {b} {c} = λ z _ → z

  lowHigh : Interface
  lowHigh = record
              { L = Label ;
                _⊑_ = _⊑_ ;
                _⊑d_ = canFlowTo? ;
                ⊑-refl = ⊑-refl ;
                ⊑-trans = ⊑-trans ;
                _⊔_ = _⊔_;
                ⊔-mono = ⊔-mono;
                ⊔-least-upper = ⊔-least-upper;
                ⊔-comm = ⊔-comm;
                ℓ* = L }
