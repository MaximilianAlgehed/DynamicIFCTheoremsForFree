module Utils where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

if_then_else_ : {P : Set} -> {A : Set} -> Dec P -> A -> A -> A
if_then_else_ (yes p) x _ = x
if_then_else_ (no ¬p) _ x = x

case_of_ : {a b : Set} -> a -> (a -> b) -> b
case_of_ a f = f a

_̸≡_ : ∀ {a} {A : Set a} (x : A) -> A → Set a
x ̸≡ y = ¬ (x ≡ y)
