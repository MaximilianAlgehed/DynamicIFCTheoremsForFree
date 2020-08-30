import Label

module LIO (LABEL : Label.Interface) where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Unary
open import Data.Maybe 
open import Data.Sum
open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Bool hiding (if_then_else_; _∧_)
open import Data.String
open import Data.List

open import Param
open import Utils

open Label.Interface LABEL

_∧_ = _×_
π₁ = proj₁
π₂ = proj₂

UserException : Set
UserException = String

data IfcException : Set where
  ToLabeledError : L → IfcException

data E : Set where
  EIFC  : IfcException  → List String → L → E
  EUser : UserException → List String → L → E

addCtx : E → String → E
addCtx (EIFC x x₁ ℓc) s = EIFC x (s ∷ x₁) ℓc
addCtx (EUser x x₁ ℓc) s = EUser x (s ∷ x₁) ℓc

record LIOInterface : Set₁ where
  field
    Labeled  : Set → Set
    label    : {A : Set} → L → A → Labeled A
    labelOf  : {A : Set} → Labeled A → L
    LIO      : Set → Set
    unlabel  : {A : Set} → Labeled A → LIO A
    toLabeled : {A : Set} → L → LIO A → LIO (Labeled A)
    return : {A : Set} → A → LIO A
    bind : {A B : Set} → LIO A → (A → LIO B) → LIO B
    throw : {A : Set} → UserException → LIO A
    catch : {A : Set} → LIO A → (E → LIO A) → LIO A
    withContext : {A : Set} → String → LIO A → LIO A

open ≡-Reasoning

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

module MkDIFC where
  -- The result of a computation is either a value of type A or a thrown
  -- exception of type E; in both cases the result is protected by a label
  Cfg : Set → Set
  Cfg A = (A ⊎ E) × L

  -- A labeled result is either a value of type A or a **delayed exception** of
  -- type E; again in both cases the result is protected by a label.
  -- The Labeled type might be equal to Cfg, but semantically the two are
  -- treated differently (see Cfgᵣ vs Labeledᵣ below)
  Labeled : Set -> Set
  Labeled A = (A ⊎ E) × L

  LIO : Set → Set
  LIO A = (ℓc : L) → Σ (Cfg A)
                        (λ { (r , ℓc') → ℓc ⊑ ℓc' }) -- added wrt. haskell

  label    : {A : Set} → L → A → Labeled A
  label ℓ a = inj₁ a , ℓ

  labelOf : {A : Set} → Labeled A → L
  labelOf (a , ℓ) = ℓ

  unlabel  : {A : Set} → Labeled A → LIO A
  unlabel (r , ℓ) ℓc = ((r , ℓ ⊔ ℓc) , ⊑-trans ⊔-mono (⊑-eql ⊔-comm))
           -- if r is a delayed exception then unlabel rethrows the exception

  return : {A : Set} → A → LIO A
  return a ℓc = (inj₁ a , ℓc) , ⊑-refl

  bind :  {A B : Set} → LIO A → (A → LIO B) → LIO B

  bind lio cont ℓc with inspect (lio ℓc)
  ... | ((inj₁ a , ℓc') , pr) with≡ _ = let r , pr' = cont a ℓc' in r , ⊑-trans pr pr'
  ... | ((inj₂ e , ℓc') , pr) with≡ _ = (inj₂ e , ℓc') , pr

  -- Unfortunately this equivalent but simpler definition breaks the proofs
  -- bind lio cont ℓc = case (lio ℓc) of \
  --  { ((inj₁ a , ℓc') , pr) -> let r , pr' = cont a ℓc' in r , ⊑-trans pr pr'
  --  ; ((inj₂ e , ℓc') , pr) -> (inj₂ e , ℓc') , pr }

  toLabeledHelp : {A : Set} → L → Cfg A → LIO (Labeled A)
  toLabeledHelp ℓ (r , ℓc') ℓc = 
      if  (ℓc' ⊑d ℓ)
      then  ((inj₁ (r , ℓ) , ℓc) , ⊑-refl)
      else  ((inj₁ (inj₂ (EIFC (ToLabeledError ℓ) [] ℓc) , ℓ) , ℓc) , ⊑-refl)

  toLabeled : {A : Set} → L → LIO A → LIO (Labeled A)
  toLabeled ℓ lio ℓc = toLabeledHelp ℓ (proj₁ (lio ℓc)) ℓc

  withContext : {A : Set} → String → LIO A → LIO A
  withContext s lio ℓc =
    ( helper
    , proj₂ (proj₁ (lio ℓc)) ) , proj₂ (lio ℓc)
    where
      helper : _
      helper with proj₁ (proj₁ (lio ℓc))
      helper | inj₁ x = inj₁ x
      helper | inj₂ y = inj₂ (addCtx y s)

  throw : {A : Set} → UserException → LIO A
  throw e ℓc = (inj₂ (EUser e [] ℓc) , ℓc), ⊑-refl

  catch : {A : Set} → LIO A → (E → LIO A) → LIO A
  catch lio hnd ℓc with lio ℓc
  catch lio hnd ℓc | (r , ℓc') , pr with r
  ... | inj₁ a = (inj₁ a , ℓc') , pr
  ... | inj₂ e = let c , pr' = hnd e ℓc' in (c , ⊑-trans pr pr')

  -- These throw and catch are modeled after λ[]_thrown+D (Hritcu et al, 2013)
  -- and the newest incarnation of LIO exceptions (Stefan et al, 2017).
  -- Previous versions of LIO (Stefan et al, 2012) were actually a bit more
  -- complex (the throw time lc was also stored inside the delayed exceptions
  -- and catching raised the lc by that); but that complexity is not needed.

DIFC : LIOInterface
DIFC = record {MkDIFC}

record ⟦LIOInterface⟧ (m₀ m₁ : LIOInterface) : Set₂ where
  open LIOInterface
  field
    Labeledᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
              → Labeled m₀ A₀ → Labeled m₁ A₁ → Set

    Labelᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
            → (ℓ₀ ℓ₁ : L) → (ℓᵣ : ⟦L⟧ ℓ₀ ℓ₁)
            → (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
            → Labeledᵣ A₀ A₁ Aᵣ (label m₀ ℓ₀ a₀) (label m₁ ℓ₁ a₁)

    labelOfᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
               → (la₀ : Labeled m₀ A₀) → (la₁ : Labeled m₁ A₁) → (⟦la⟧ : Labeledᵣ A₀ A₁ Aᵣ la₀ la₁)
               → ⟦L⟧ (labelOf m₀ la₀) (labelOf m₁ la₁)

    LIOᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
          → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → Set

    unlabelᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
              → (lab₀ : Labeled m₀ A₀) → (lab₁ : Labeled m₁ A₁) → (⟦lab⟧ : Labeledᵣ A₀ A₁ Aᵣ lab₀ lab₁)
              → LIOᵣ A₀ A₁ Aᵣ (unlabel m₀ lab₀) (unlabel m₁ lab₁)

    toLabeledᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
                → (ℓ₀ ℓ₁ : L)   → (ℓᵣ : ⟦L⟧ ℓ₀ ℓ₁)
                → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → (lioᵣ : LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁)
                → LIOᵣ (Labeled m₀ A₀) (Labeled m₁ A₁) (Labeledᵣ A₀ A₁ Aᵣ) (toLabeled m₀ ℓ₀ lio₀) (toLabeled m₁ ℓ₁ lio₁)

    returnᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
             → (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
             → LIOᵣ A₀ A₁ Aᵣ (return m₀ a₀) (return m₁ a₁)

    bindᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
           → (B₀ B₁ : Set) → (Bᵣ : B₀ → B₁ → Set)
           → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → (lioᵣ : LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁)
           → (cont₀ : A₀ → LIO m₀ B₀) → (cont₁ : A₁ → LIO m₁ B₁)
           → (contᵣ : (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁) → LIOᵣ B₀ B₁ Bᵣ (cont₀ a₀) (cont₁ a₁))
           → LIOᵣ B₀ B₁ Bᵣ (bind m₀ lio₀ cont₀) (bind m₁ lio₁ cont₁)

    Eᵣ : E → E → Set

    userExceptionᵣ : UserException → UserException → Set

    withContextᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
                  → (s₀ s₁ : String) → (sᵣ : s₀ ≡ s₁)
                  → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → (lioᵣ : LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁)
                  → LIOᵣ A₀ A₁ Aᵣ (withContext m₀ s₀ lio₀) (withContext m₁ s₁ lio₁)

    throwᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
            → (e₀ e₁ : UserException) → (eᵣ : userExceptionᵣ e₀ e₁)
            → LIOᵣ A₀ A₁ Aᵣ (throw m₀ e₀) (throw m₁ e₁)

    catchᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
            → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → (lioᵣ : LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁)
            → (cont₀ : E → LIO m₀ A₀) → (cont₁ : E → LIO m₁ A₁)
            → (contᵣ : (e₀ e₁ : E) → (eᵣ : Eᵣ e₀ e₁) → LIOᵣ A₀ A₁ Aᵣ (cont₀ e₀) (cont₁ e₁))
            → LIOᵣ A₀ A₁ Aᵣ (catch m₀ lio₀ cont₀) (catch m₁ lio₁ cont₁)
