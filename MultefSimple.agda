import Label

module MultefSimple (LABEL : Label.Interface) where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Unary
open import Data.Maybe 
open import Data.Sum
open import Data.Empty
open import Data.Bool hiding (if_then_else_)

open import Param
open import Utils

open Label.Interface LABEL

record Multef  : Set1 where
  field
    Fac : Set -> Set
    facet : {a : Set} -> L -> Fac a -> Fac a -> Fac a
    return : {a : Set} -> a -> Fac a
    bind : {a b : Set} -> Fac a -> (a -> Fac b) -> Fac b

  fmap : {a b : Set} -> (a -> b) -> Fac a -> Fac b
  fmap f fa = bind fa (λ x → return (f x))

record ⟦Multef⟧ (m₀ m₁ : Multef) : Set₂ where
  open Multef
  field
    Facᵣ  : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁) → ⟦Set⟧ (Fac m₀ A₀) (Fac m₁ A₁)
    returnᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
           → (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
           → Facᵣ A₀ A₁ Aᵣ (return m₀ a₀) (return m₁ a₁)
    bindᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
           → (B₀ B₁ : Set) → (Bᵣ : ⟦Set⟧ B₀ B₁)
           → (f₀ : Fac m₀ A₀) → (f₁ : Fac m₁ A₁) → (fᵣ : Facᵣ A₀ A₁ Aᵣ f₀ f₁)
           → (c₀ : A₀ → Fac m₀ B₀) → (c₁ : A₁ → Fac m₁ B₁)
           → (cᵣ : (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
                  → Facᵣ B₀ B₁ Bᵣ (c₀ a₀) (c₁ a₁))
           → Facᵣ B₀ B₁ Bᵣ (bind m₀ f₀ c₀) (bind m₁ f₁ c₁)
    facetᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
            → (ℓ₀ ℓ₁ : L)   → (⟦ℓ⟧ : ⟦L⟧ ℓ₀ ℓ₁)
            → (f₀₀ : Fac m₀ A₀) → (f₀₁ : Fac m₁ A₁)
            → (f₀ᵣ : Facᵣ A₀ A₁ Aᵣ f₀₀ f₀₁)
            → (f₁₀ : Fac m₀ A₀) → (f₁₁ : Fac m₁ A₁)
            → (f₁ᵣ : Facᵣ A₀ A₁ Aᵣ f₁₀ f₁₁)
            → Facᵣ A₀ A₁ Aᵣ (facet m₀ ℓ₀ f₀₀ f₁₀) (facet m₁ ℓ₁ f₀₁ f₁₁)

module Sec where
  data Fac : Set -> Set where
    return : {a : Set} -> a -> Fac a
    facet : {a : Set} -> L -> Fac a -> Fac a -> Fac a

  bind : {a b : Set} -> Fac a -> (a -> Fac b) -> Fac b
  bind (return a) k = k a
  bind (facet l f0 f1) k = facet l (bind f0  k) (bind f1 k)

  project : {A : Set} -> Fac A -> L -> A
  project (facet l f0 f1) l' =
   if l ⊑d l'
     then project f0 l'
     else project f1 l'
  project (return a) _ = a

  _∼⟨_⟩_ : ∀{A : Set} → Fac A → L → Fac A → Set
  f₀ ∼⟨ ℓ ⟩ f₁ = project f₀ ℓ ≡ project f₁ ℓ

  lemma : ∀ {a b} l (f : Fac a) (c : a -> Fac b) -> project (bind f c) l ≡ project (c (project f l)) l
  lemma l (return x) c = refl
  lemma l (facet x f f₁) c with x ⊑d l
  lemma l (facet x f f₁) c | yes p = lemma l f c
  lemma l (facet x f f₁) c | no ¬p = lemma l f₁ c

sec : Multef
sec = record {Sec }

module Secᵣ where
  open Multef
  m₀ = sec
  m₁ = sec
  open Sec using (lemma; project)

  Facᵣ  : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁) → ⟦Set⟧ (Fac m₀ A₀) (Fac m₁ A₁)
  Facᵣ A₀ A₁ Aᵣ f₀ f₁ = Aᵣ (project f₀ ℓ*) (project f₁ ℓ*)

  facetᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
          → (ℓ₀ ℓ₁ : L)   → (⟦ℓ⟧ : ⟦L⟧ ℓ₀ ℓ₁)
          → (f₀₀ : Fac m₀ A₀) → (f₀₁ : Fac m₁ A₁)
          → (f₀ᵣ : Facᵣ A₀ A₁ Aᵣ f₀₀ f₀₁)
          → (f₁₀ : Fac m₀ A₀) → (f₁₁ : Fac m₁ A₁)
          → (f₁ᵣ : Facᵣ A₀ A₁ Aᵣ f₁₀ f₁₁)
          → Facᵣ A₀ A₁ Aᵣ (facet m₀ ℓ₀ f₀₀ f₁₀) (facet m₁ ℓ₁ f₀₁ f₁₁)
  facetᵣ A₀ A₁ Aᵣ ℓ₀ .ℓ₀ refl f₀₀ f₀₁ f₀ᵣ f₁₀ f₁₁ f₁ᵣ with ℓ₀ ⊑d ℓ*
  facetᵣ A₀ A₁ Aᵣ ℓ₀ .ℓ₀ refl f₀₀ f₀₁ f₀ᵣ f₁₀ f₁₁ f₁ᵣ | yes p = f₀ᵣ
  facetᵣ A₀ A₁ Aᵣ ℓ₀ .ℓ₀ refl f₀₀ f₀₁ f₀ᵣ f₁₀ f₁₁ f₁ᵣ | no ¬p = f₁ᵣ

  bindᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
         → (B₀ B₁ : Set) → (Bᵣ : ⟦Set⟧ B₀ B₁)
         → (f₀ : Fac m₀ A₀) → (f₁ : Fac m₁ A₁) → (fᵣ : Facᵣ A₀ A₁ Aᵣ f₀ f₁)
         → (c₀ : A₀ → Fac m₀ B₀) → (c₁ : A₁ → Fac m₁ B₁)
         → (cᵣ : (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
                → Facᵣ B₀ B₁ Bᵣ (c₀ a₀) (c₁ a₁))
         → Facᵣ B₀ B₁ Bᵣ (bind m₀ f₀ c₀) (bind m₁ f₁ c₁)
  bindᵣ  A₀ A₁ Aᵣ B₀ B₁ Bᵣ f₀ f₁ fᵣ c₀ c₁ cᵣ rewrite lemma ℓ* f₀ c₀ | lemma ℓ* f₁ c₁ = cᵣ _ _ fᵣ

  returnᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
         → (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
         → Facᵣ A₀ A₁ Aᵣ (return m₀ a₀) (return m₁ a₁)
  returnᵣ = λ A₀ A₁ Aᵣ a₀ a₁ aᵣ → aᵣ


⟦sec⟧ : ⟦Multef⟧ sec sec
⟦sec⟧ = record {Secᵣ}

module Std where
  Fac : Set -> Set
  facet : {a : Set} -> L -> Fac a -> Fac a -> Fac a
  return : {a : Set} -> a -> Fac a
  bind : {a b : Set} -> Fac a -> (a -> Fac b) -> Fac b

  Fac a = Maybe a
  return a =  just a
  bind f c = case f of \
    { (just a) -> c a
    ; nothing  -> nothing }
  facet ℓ f₀ f₁ = nothing

std : Multef
std = record {Std}

module Parametricity where
  open Multef
  open ⟦Multef⟧
  postulate parametricity : (o : (m : Multef) → Fac m Bool → Fac m Bool)
                          → (m₀ : Multef) → (m₁ : Multef) → (mᵣ : ⟦Multef⟧ m₀ m₁)
                          → (f₀ : Fac m₀ Bool) → (f₁ : Fac m₁ Bool)
                          → (fᵣ : Facᵣ mᵣ Bool Bool _≡_ f₀ f₁)
                          → Facᵣ mᵣ Bool Bool _≡_ (o m₀ f₀) (o m₁ f₁)

module Noninterference where
  open import Data.Bool
  open Multef
  open Sec using (project ; _∼⟨_⟩_ )
  open ⟦Multef⟧
  open Parametricity

  noninterference : (o : (m : Multef) → Fac m Bool → Fac m Bool)
                  → (f₀ f₁ : Fac sec Bool) → f₀ ∼⟨ ℓ* ⟩ f₁
                  → o sec f₀ ∼⟨ ℓ* ⟩ o sec f₁
  noninterference o f₀ f₁ x = parametricity o sec sec ⟦sec⟧ f₀ f₁ x

module ⟦Sec-std⟧ where
  open Multef
  open Sec using (project; lemma)
  m₀ = sec
  m₁ = std
  Facᵣ  : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁) → ⟦Set⟧ (Fac m₀ A₀) (Fac m₁ A₁)
  returnᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
         → (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
         → Facᵣ A₀ A₁ Aᵣ (return m₀ a₀) (return m₁ a₁)
  bindᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
         → (B₀ B₁ : Set) → (Bᵣ : ⟦Set⟧ B₀ B₁)
         → (f₀ : Fac m₀ A₀) → (f₁ : Fac m₁ A₁) → (fᵣ : Facᵣ A₀ A₁ Aᵣ f₀ f₁)
         → (c₀ : A₀ → Fac m₀ B₀) → (c₁ : A₁ → Fac m₁ B₁)
         → (cᵣ : (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
                → Facᵣ B₀ B₁ Bᵣ (c₀ a₀) (c₁ a₁))
         → Facᵣ B₀ B₁ Bᵣ (bind m₀ f₀ c₀) (bind m₁ f₁ c₁)
  facetᵣ : (A₀ A₁ : Set) → (Aᵣ : ⟦Set⟧ A₀ A₁)
          → (ℓ₀ ℓ₁ : L)   → (⟦ℓ⟧ : ⟦L⟧ ℓ₀ ℓ₁)
          → (f₀₀ : Fac m₀ A₀) → (f₀₁ : Fac m₁ A₁)
          → (f₀ᵣ : Facᵣ A₀ A₁ Aᵣ f₀₀ f₀₁)
          → (f₁₀ : Fac m₀ A₀) → (f₁₁ : Fac m₁ A₁)
          → (f₁ᵣ : Facᵣ A₀ A₁ Aᵣ f₁₀ f₁₁)
          → Facᵣ A₀ A₁ Aᵣ (facet m₀ ℓ₀ f₀₀ f₁₀) (facet m₁ ℓ₁ f₀₁ f₁₁)
  Facᵣ A₀ A₁ Aᵣ f₀ f₁ = f₁ ̸≡ nothing → ⟦Maybe⟧ A₀ A₁ Aᵣ (just (project f₀ ℓ*)) f₁ 
  returnᵣ A₀ A₁ Aᵣ a₀ a₁ aᵣ q = ⟦just⟧ aᵣ
  facetᵣ A₀ A₁ Aᵣ ℓ₀ ℓ₁ ℓᵣ f₀₀ f₀₁ f₀ᵣ f₁₀ f₁₁ f₁ᵣ q = ⊥-elim (q refl)
  
  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ f₀ f₁ fᵣ c₀ c₁ cᵣ with project (bind sec f₀ c₀) ℓ* | Sec.lemma ℓ* f₀ c₀
  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ f₀ (just x) fᵣ c₀ c₁ cᵣ | .(project (c₀ (project f₀ (Label.Interface.ℓ* LABEL))) (Label.Interface.ℓ* LABEL)) | refl with fᵣ (λ ())
  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ f₀ (just x) fᵣ c₀ c₁ cᵣ | ._ | refl | ⟦just⟧ aᵣ = λ x₁ → cᵣ _ _ aᵣ x₁
  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ f₀ nothing fᵣ c₀ c₁ cᵣ | .(project (c₀ (project f₀ (Label.Interface.ℓ* LABEL))) (Label.Interface.ℓ* LABEL)) | refl = λ x → ⊥-elim (x refl)


⟦sec-std⟧ : ⟦Multef⟧ sec std
⟦sec-std⟧ = record {⟦Sec-std⟧}

fᵣ : ∀ {b} -> ⟦Multef⟧.Facᵣ ⟦sec-std⟧ Bool Bool _≡_ (Sec.facet ℓ* (Sec.return b) (Sec.return false)) (just b)
fᵣ q with ℓ* ⊑d ℓ*
fᵣ q | yes p = ⟦just⟧ refl
fᵣ q | no ¬p = ⊥-elim (¬p ⊑-refl)

open Multef
open Sec using (project; lemma)
open ⟦Multef⟧
open Parametricity

transparency : (o : (m : Multef) → Fac m Bool → Fac m Bool)
             → (b : Bool)
             → let fb = (facet sec ℓ* (return sec b) (return sec false))
                in 
              ¬ (o std (just b) ≡ nothing)
             → just (project (o sec fb) ℓ*) ≡ (o std (return std b))
transparency o b q with parametricity o _ _ ⟦sec-std⟧ (facet sec ℓ* (return sec b) (return sec false)) (return std b) fᵣ q
... | d with o std (return std b)
transparency o b q | ⟦just⟧ aᵣ | .(just _) = cong just aᵣ

