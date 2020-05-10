import Label
import MultefSimple as Multef
module FIOSimple (LABEL : Label.Interface)
           where

module MultefL = Multef LABEL

open Label.Interface LABEL


open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Unary
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (if_then_else_)
open import Data.String
open import Param
open import Utils

record Interface (MULTEF : MultefL.Multef) : Set1 where
  open MultefL.Multef MULTEF public using (Fac)
  field
    FSt : Set -> Set

module MkFSt (MULTEF : MultefL.Multef) where
  module Multef' = MultefL.Multef MULTEF
  open Multef' using (Fac; fmap)

  _>>=_ = Multef'.bind

  State : Set
  State = String -> Bool
  
  FSt : Set -> Set
  get  : FSt State
  put  : State -> FSt ⊤
  return : {a : Set} -> a -> FSt a
  bind : {a b : Set} -> FSt a -> (a -> FSt b) -> FSt b

  FSt a = State -> Fac (State × a)
  get z = Multef'.return (z , z)
  put s s' = Multef'.return (s , tt)
  return a = λ s → Multef'.return (s , a)
  bind fio k s = do (s' , a ) <- fio s
                    k a s'

  read : String -> FSt Bool
  read var = bind get (λ s → return (s var))

  write : String -> Bool -> FSt ⊤
  write var val = bind get (λ s -> put (λ var' → if var ≈? var' then val else s var'))

  lift : {A : Set} -> Fac A -> FSt A
  lift f = λ s → do a <- f ; Multef'.return (s , a)

fioSec : (MULTEF : MultefL.Multef) -> Interface MULTEF
fioSec MULTEF = record {MkFSt MULTEF}


record ⟦Multef⟧ {n₀ n₁ : MultefL.Multef} (m₀ : Interface n₀) (m₁ : Interface n₁) : Set2 where
  open Interface
  field
    Facᵣ  : {A₀ A₁ : Set} → (Aᵣ : ⟦Set⟧ A₀ A₁) → ⟦Set⟧ (Fac m₀ A₀) (Fac m₁ A₁)

    FStᵣ :  {A₀ A₁ : Set} -> (Aᵣ : ⟦Set⟧ A₀ A₁)
            -> ⟦Set⟧  (FSt m₀ A₀) (FSt m₁ A₁)

    -- ⟦get⟧  : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) -> FStᵣ ⟦s⟧ ⟦s⟧ (get m₀) (get m₁)
    -- ⟦put⟧  : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->  (⟦s⟧ ⟦->⟧ (FStᵣ ⟦s⟧ ⟦⊤⟧)) (put m₀) (put m₁)

    -- ⟦run⟧ : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->
    --         {a₀ a₁ : Set} -> (⟦a⟧ : ⟦Set⟧ a₀ a₁) ->
    --         ((Facᵣ ⟦s⟧ ⟦->⟧ ⟦s⟧) ⟦->⟧ (Facᵣ (FStᵣ ⟦s⟧ ⟦a⟧)) ⟦->⟧ (FStᵣ ⟦s⟧ (Facᵣ ⟦a⟧))) (run m₀) (run m₁)

    -- returnᵣ : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->
    --          {a₀ a₁ : Set} -> (⟦a⟧ : ⟦Set⟧ a₀ a₁) ->
    --          (⟦a⟧ ⟦->⟧ (FStᵣ ⟦s⟧ ⟦a⟧)) (return m₀) (return m₁)

    -- bindᵣ : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->
    --          {a₀ a₁ : Set} -> (⟦a⟧ : ⟦Set⟧ a₀ a₁) ->
    --          {b₀ b₁ : Set} -> (⟦b⟧ : ⟦Set⟧ b₀ b₁) ->
    --          ((FStᵣ ⟦s⟧ ⟦a⟧) ⟦->⟧ (⟦a⟧ ⟦->⟧ (FStᵣ ⟦s⟧ ⟦b⟧)) ⟦->⟧ (FStᵣ ⟦s⟧ ⟦b⟧)) (bind m₀) (bind m₁)

-- Parametricity gives us the following record for every underlying Multef implementation.
-- (We only need to fill in manually only the fields which we actually use in the proof).

module MkFStᵣ
  (MULTEF : MultefL.Multef)
  (⟦MULTEF⟧ : MultefL.⟦Multef⟧ MULTEF MULTEF)
  where
  module Multefᵣ = MultefL.⟦Multef⟧ 
  open Multefᵣ ⟦MULTEF⟧ hiding (returnᵣ; bindᵣ) renaming (Facᵣ to PreFac)
  open Interface
  m₀ = fioSec MULTEF
  m₁ = fioSec MULTEF
  ⟦State⟧ : ⟦Set⟧ (MkFSt.State MULTEF) (MkFSt.State MULTEF)
  ⟦State⟧ = _≡_
  Facᵣ  : {A₀ A₁ : Set} → (Aᵣ : ⟦Set⟧ A₀ A₁) → ⟦Set⟧ (Fac m₀ A₀) (Fac m₁ A₁)
  Facᵣ Aᵣ = PreFac _ _ Aᵣ
  FStᵣ :  {A₀ A₁ : Set} -> (Aᵣ : ⟦Set⟧ A₀ A₁)
         -> ⟦Set⟧  (FSt m₀ A₀) (FSt m₁ A₁)
  FStᵣ Aᵣ = ⟦State⟧ ⟦->⟧ (Facᵣ (⟦State⟧ ⟦×⟧ Aᵣ))

  -- ⟦get⟧  : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) -> FStᵣ ⟦s⟧ ⟦s⟧ (get m₀) (get m₁)
  -- ⟦get⟧ _ _ _ ⟦s⟧ = Multefᵣ.returnᵣ ⟦MULTEF⟧ _ _ _ _ _ ( ⟦s⟧ , ⟦s⟧ )
  
  -- ⟦put⟧  : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->  (⟦s⟧ ⟦->⟧ (FStᵣ ⟦s⟧ ⟦⊤⟧)) (put m₀) (put m₁)
  -- ⟦put⟧ ⟦S⟧ _ _  ⟦s0⟧ _ _ ⟦s⟧ = Multefᵣ.returnᵣ ⟦MULTEF⟧ _ _ _ _ _ (⟦s0⟧ , refl)
  
  -- ⟦run⟧ : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->
  --         {a₀ a₁ : Set} -> (⟦a⟧ : ⟦Set⟧ a₀ a₁) ->
  --         ((Facᵣ ⟦s⟧ ⟦->⟧ ⟦s⟧) ⟦->⟧ (Facᵣ (FStᵣ ⟦s⟧ ⟦a⟧)) ⟦->⟧ (FStᵣ ⟦s⟧ (Facᵣ ⟦a⟧))) (run m₀) (run m₁)

  -- returnᵣ : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->
  --          {a₀ a₁ : Set} -> (⟦a⟧ : ⟦Set⟧ a₀ a₁) ->
  --          (⟦a⟧ ⟦->⟧ (FStᵣ ⟦s⟧ ⟦a⟧)) (return m₀) (return m₁)
  -- returnᵣ _ _ = λ _ _ ⟦x⟧ _ _ ⟦s⟧ -> Multefᵣ.returnᵣ ⟦MULTEF⟧ _ _ _ _ _ ( ⟦s⟧ , ⟦x⟧ )

  -- bindᵣ : {s₀ s₁ : Set} -> (⟦s⟧ : ⟦Set⟧ s₀ s₁) ->
  --          {a₀ a₁ : Set} -> (⟦a⟧ : ⟦Set⟧ a₀ a₁) ->
  --          {b₀ b₁ : Set} -> (⟦b⟧ : ⟦Set⟧ b₀ b₁) ->
  --          ((FStᵣ ⟦s⟧ ⟦a⟧) ⟦->⟧ (⟦a⟧ ⟦->⟧ (FStᵣ ⟦s⟧ ⟦b⟧)) ⟦->⟧ (FStᵣ ⟦s⟧ ⟦b⟧)) (bind m₀) (bind m₁)
  -- bindᵣ ⟦S⟧ Aᵣ ⟦B⟧ fio0 fio1 ⟦fio⟧ k0 k1 ⟦k⟧ s0 s1 ⟦s⟧ =
  --    Multefᵣ.bindᵣ ⟦MULTEF⟧ _ _ _ _ _ _ (fio0 s0) (fio1 s1) (⟦fio⟧ s0 s1 ⟦s⟧)
  --      _ _ (λ {(s'0 , a0) (s'1 , a1) (⟦s'⟧ , ⟦a⟧) → ⟦k⟧ a0 a1 ⟦a⟧ s'0 s'1 ⟦s'⟧})

sec : Interface MultefL.sec
sec = fioSec MultefL.sec

module MadeFStᵣ = MkFStᵣ MultefL.sec MultefL.⟦sec⟧

⟦sec⟧ : ⟦Multef⟧ sec sec
⟦sec⟧ = record {MadeFStᵣ }


open Interface
open ⟦Multef⟧

open MultefL.Sec using (project)
-- Max: The only thing I would fix here is that it should probably
-- be ∀ s₀ s₁ → (∀ v → project (s₀ v) ℓ* ≡ project (s₁ v) ℓ*) → ...


_∼⟨_⟩_ : ∀{A : Set} → FSt sec A → L → FSt sec A → Set
f0 ∼⟨ ℓ ⟩ f1 = ∀ v -> MultefL.Sec._∼⟨_⟩_ (f0 v) ℓ (f1 v)


noninterference : (o : (m : Interface MultefL.sec) → FSt m Bool → FSt m Bool)
                  → (oᵣ : (m₀ : Interface MultefL.sec) → (m₁ : Interface MultefL.sec) → (mᵣ : ⟦Multef⟧ m₀ m₁)
                         → (f₀ : FSt m₀ Bool) → (f₁ : FSt m₁ Bool) → (⟦f⟧ : FStᵣ mᵣ _≡_ f₀ f₁)
                         → FStᵣ mᵣ  _≡_ (o m₀ f₀) (o m₁ f₁))
                  → (f₀ f₁ : FSt sec Bool) → f₀ ∼⟨ ℓ* ⟩ f₁
                  → o sec f₀ ∼⟨ ℓ* ⟩ o sec f₁
noninterference o oᵣ f0 f1 p = h1 (oᵣ sec sec ⟦sec⟧ f0 f1 (h0 p))
 where
   h0 : ((s : MkFSt.State MultefL.sec) → project (f0 s) ℓ* ≡ project (f1 s) ℓ*) -> ((x0 x1 : MkFSt.State MultefL.sec) →
       x0 ≡ x1 → (_≡_ ⟦×⟧ _≡_) (project (f0 x0) ℓ*)  (project (f1 x1) ℓ*))
   h0 x x0 .x0 refl = ×-id-r (x x0)

   h1 : ((x0 x1 : MkFSt.State MultefL.sec) →
      x0 ≡ x1 →
      (_≡_ ⟦×⟧ _≡_)
      (project (o (fioSec MultefL.sec) f0 x0) ℓ*)
      (project (o (fioSec MultefL.sec) f1 x1) ℓ*)) ->
      ∀ s -> project (o (fioSec MultefL.sec) f0 s) ℓ* ≡ project (o (fioSec MultefL.sec) f1 s) ℓ*
   h1 x s = ×-id-l (x s s refl)

