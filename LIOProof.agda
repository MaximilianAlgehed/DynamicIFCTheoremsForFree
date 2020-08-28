import Label

module LIOProof  (LABEL : Label.Interface) where

open import LIO (LABEL)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Unary
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Data.Bool hiding (if_then_else_; _∧_)
open import Data.String
open import Param
open import Utils
open Label.Interface LABEL
open ≡-Reasoning

module Mk⟦DIFC⟧ where
  open LIOInterface

  toLabeledLemma : ∀{A : Set}
                 → (lio : LIO DIFC A)
                 → (ℓ ℓc : L)
                 → proj₂ (proj₁ (toLabeled DIFC ℓ lio ℓc)) ≡ ℓc
  toLabeledLemma lio ℓ ℓc with proj₂ (proj₁ (lio ℓc)) ⊑d ℓ
  ... | yes p = refl
  ... | no ¬p = refl

  helper₀ : ∀ {A₀} {A₁} {Aᵣ : A₀ → A₁ → Set}
          → {a₀ : A₀}
          → {a₁ : A₁}
          → {x₀ : A₀ ⊎ E}
          → {x₁ : A₁ ⊎ E}
          → (Aᵣ ⟦⊎⟧ _≡_) x₀ x₁
          → x₀ ≡ inj₁ a₀
          → x₁ ≡ inj₁ a₁
          → Aᵣ a₀ a₁
  helper₀ (⟦inj₁⟧ x) refl refl = x

  helper₁ : ∀ {A₀} {A₁} {Aᵣ : A₀ → A₁ → Set}
          → {a : A₀}
          → {e : E}
          → {x₀ : A₀ ⊎ E}
          → {x₁ : A₁ ⊎ E}
          → (Aᵣ ⟦⊎⟧ _≡_) x₀ x₁
          → x₀ ≡ inj₁ a
          → x₁ ≡ inj₂ e
          → ⊥
  helper₁ x refl refl with x
  ... | ()

  helper₂ : ∀ {A₀} {A₁} {Aᵣ : A₀ → A₁ → Set}
          → {e₀ e₁ : E}
          → {x₀ : A₀ ⊎ E}
          → {x₁ : A₁ ⊎ E}
          → (Aᵣ ⟦⊎⟧ _≡_) x₀ x₁
          → x₀ ≡ inj₂ e₀
          → x₁ ≡ inj₂ e₁
          → e₀ ≡ e₁
  helper₂ (⟦inj₂⟧ x) refl refl = x

  ⟦⊎⟧sym : ∀{A₀ A₁ : Set} {Aᵣ : A₀ → A₁ → Set}
         → (x₀ : A₀ ⊎ E)
         → (x₁ : A₁ ⊎ E)
         → (Aᵣ ⟦⊎⟧ _≡_) x₀ x₁
         → ((λ a₀ a₁ → Aᵣ a₁ a₀) ⟦⊎⟧ _≡_) x₁ x₀
  ⟦⊎⟧sym .(inj₁ _) .(inj₁ _) (⟦inj₁⟧ x) = ⟦inj₁⟧ x
  ⟦⊎⟧sym .(inj₂ _) .(inj₂ _) (⟦inj₂⟧ x) = ⟦inj₂⟧ (sym x)

  lemma₀ : ∀{ℓ A} → (lio : LIO DIFC A) → ℓ ⊑ proj₂ (proj₁ (lio ℓ))
  lemma₀ {ℓ} lio = proj₂ (lio ℓ)

  lemma₁ : ∀{ℓ A B} → (lio : LIO DIFC A) → (cont : A → LIO DIFC B) → ℓ ⊑ proj₂ (proj₁ (bind DIFC lio cont ℓ))
  lemma₁ {ℓ} lio cont with inspect (lio ℓ)
  lemma₁ {ℓ} lio cont | ((inj₁ x , snd) , pr₀) with≡ eq = 
     ⊑-trans (lemma₀ lio) (⊑-trans (⊑-eql (cong (λ x → proj₂ (proj₁ x)) eq)) (lemma₀ (cont x)))
  lemma₁ {ℓ} lio cont | ((inj₂ y , snd) , pr₀) with≡ eq =
     ⊑-trans (lemma₀ lio) (⊑-eql (cong (λ x → proj₂ (proj₁ x)) eq))

  lemma₂ : ∀{ℓ A B} → (lio : LIO DIFC A) → (cont : A → LIO DIFC B) → proj₂ (proj₁ (lio ℓ)) ⊑ proj₂ (proj₁ (bind DIFC lio cont ℓ))
  lemma₂ {ℓ} lio cont with inspect (lio ℓ)
  lemma₂ {ℓ} lio cont | ((inj₁ x , snd) , pr₀) with≡ eq = 
    ⊑-trans (⊑-eql (cong (λ x → proj₂ (proj₁ x)) eq)) (lemma₀ (cont x))
  lemma₂ {ℓ} lio cont | ((inj₂ y , snd) , pr₀) with≡ eq = ⊑-eql (cong (λ x → proj₂ (proj₁ x)) eq)

  m₀ = DIFC
  m₁ = DIFC

  Eᵣ : E → E → Set
  Eᵣ = _≡_   {- Logical Relation for Errors -}

  Cfgᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set) → (A₀ ⊎ E) × L → (A₁ ⊎ E) × L → Set
  Cfgᵣ A₀ A₁ Aᵣ (v₀ , ℓ₀) (v₁ , ℓ₁) = (⟦L⟧ ℓ₀ ℓ₁ × ℓ₀ ⊑ ℓ* × (Aᵣ ⟦⊎⟧ Eᵣ) v₀ v₁) ⊎ (ℓ₀ ̷⊑ ℓ* × ℓ₁ ̷⊑ ℓ*)

  LIOᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
        → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → Set
  LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁ =
    (ℓ₀ ℓ₁ : L) → (ℓ₀ ≡ ℓ₁ ⊎ (ℓ₀ ̷⊑ ℓ* × ℓ₁ ̷⊑ ℓ*)) → Cfgᵣ A₀ A₁ Aᵣ (proj₁ (lio₀ ℓ₀)) (proj₁ (lio₁ ℓ₁))

  Labeledᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set) → Labeled m₀ A₀ → Labeled m₁ A₁ → Set
  Labeledᵣ A₀ A₁ Aᵣ l₀ l₁ = (labelOf m₀ l₀ ≡ labelOf m₁ l₁) ∧
                           (labelOf m₀ l₀ ⊑ ℓ* → (Aᵣ ⟦⊎⟧ Eᵣ) (proj₁ l₀) (proj₁ l₁))

  Labelᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
          → (ℓ₀ ℓ₁ : L) → (ℓᵣ : ⟦L⟧ ℓ₀ ℓ₁)
          → (a₀ : A₀) → (a₁ : A₁) → (aᵣ : Aᵣ a₀ a₁)
          → Labeledᵣ A₀ A₁ Aᵣ (label m₀ ℓ₀ a₀) (label m₁ ℓ₁ a₁)

  labelOfᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
             → (la₀ : Labeled m₀ A₀) → (la₁ : Labeled m₁ A₁) → (⟦la⟧ : Labeledᵣ A₀ A₁ Aᵣ la₀ la₁)
             → ⟦L⟧ (labelOf m₀ la₀) (labelOf m₁ la₁)

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

  Labelᵣ A₀ A₁ Aᵣ ℓ₀ ℓ₁ ℓᵣ a₀ a₁ aᵣ = ℓᵣ , λ pr → ⟦inj₁⟧ aᵣ

  labelOfᵣ A₀ A₁ Aᵣ la₀ la₁ (ℓᵣ , ⟦v⟧) = ℓᵣ

  unlabelᵣ A₀ A₁ Aᵣ lab₀ lab₁ ⟦lab⟧ ℓ₀ .ℓ₀ (inj₁ refl) with ℓ₀ ⊑d ℓ*
  ... | no ¬p = inj₂ ((λ pr → ¬p (⊑-trans ⊔-mono (⊑-trans (⊑-eql ⊔-comm) pr))) , λ pr → ¬p (⊑-trans ⊔-mono (⊑-trans (⊑-eql ⊔-comm) pr)))
  ... | yes p with proj₂ lab₀ ⊑d ℓ*
  ... | yes q = inj₁ (cong _ (proj₁ ⟦lab⟧) , ⊔-least-upper q p , proj₂ ⟦lab⟧ q)
  ... | no ¬q = inj₂ ((λ pr → ¬q (⊑-trans ⊔-mono pr)) , λ pr → ¬q (⊑-trans (⊑-trans (⊑-eql (proj₁ ⟦lab⟧)) ⊔-mono) pr))
  unlabelᵣ A₀ A₁ Aᵣ lab₀ lab₁ ⟦lab⟧ ℓ₀ ℓ₁ (inj₂ (not₀ , not₁)) =
    inj₂ ((λ pr → not₀ (⊑-trans (⊑-trans ⊔-mono (⊑-eql ⊔-comm)) pr)) , λ pr → not₁ (⊑-trans (⊑-trans ⊔-mono (⊑-eql ⊔-comm)) pr))

  lemmaz : {A₀ A₁ : Set} → {Aᵣ : A₀ → A₁ → Set}
        → (ℓ₀ : L) -> {ℓ₂ : L} -> (ℓ₂ ⊑ ℓ*)
        → (c₀ : MkDIFC.Cfg A₀) → (c₁ : MkDIFC.Cfg A₁) → Cfgᵣ A₀ A₁ Aᵣ c₀ c₁
        → Cfgᵣ _ _ (Labeledᵣ _ _ Aᵣ) (proj₁ (MkDIFC.toLabeledHelp ℓ₀ c₀ ℓ₂)) (proj₁ (MkDIFC.toLabeledHelp ℓ₀ c₁ ℓ₂))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) cr with lc0 ⊑d ℓ₀ | lc1 ⊑d ℓ₀
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) (inj₂ (fst , snd)) | yes q | yes r = inj₁ (refl , p , ⟦inj₁⟧ (refl , (λ pr → (⊥-elim (fst (⊑-trans q pr))))))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) (inj₂ (fst , snd)) | yes q | no ¬r = inj₁ (refl , p , ⟦inj₁⟧ (refl , (λ pr → (⊥-elim (fst (⊑-trans q pr))))))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) (inj₂ (fst , snd)) | no ¬q | yes r = inj₁ (refl , p , ⟦inj₁⟧ (refl , (λ pr → (⊥-elim (snd (⊑-trans r pr))))))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) _                  | no ¬q | no ¬r = inj₁ (refl , p , ⟦inj₁⟧ (refl , (λ _ → ⟦inj₂⟧ refl)))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) (inj₁ (fst , snd)) | yes q | yes r = inj₁ (refl , p , ⟦inj₁⟧ (refl , (λ _ → proj₂ snd)))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) (inj₁ (fst , snd)) | yes q | no ¬r = ⊥-elim (¬r (⊑-trans (⊑-eql (sym fst)) q))
  lemmaz ℓ₀ p (_ , lc0) (_ , lc1) (inj₁ (fst , snd)) | no ¬q | yes r = ⊥-elim (¬q (⊑-trans (⊑-eql fst) r))

  toLabeledᵣ A₀ A₁ Aᵣ ℓ₀ .ℓ₀ refl lio₀ lio₁ lioᵣ ℓ₂ ℓ₃ (inj₂ (not₂ , not₃)) =
    inj₂ ((λ pr → not₂ (⊑-trans (⊑-eql (sym (toLabeledLemma lio₀ ℓ₀ ℓ₂))) pr))
         , λ pr → not₃ (⊑-trans (⊑-eql (sym (toLabeledLemma lio₁ ℓ₀ ℓ₃))) pr))
  toLabeledᵣ A₀ A₁ Aᵣ ℓ₀ .ℓ₀ refl lio₀ lio₁ lioᵣ ℓ₂ .ℓ₂ (inj₁ refl) with ℓ₂ ⊑d ℓ*
  ... | no ¬p = inj₂ ( (λ pr → ¬p (⊑-trans (⊑-eql (sym (toLabeledLemma lio₀ ℓ₀ ℓ₂))) pr))
                     , λ pr → ¬p (⊑-trans (⊑-eql (sym (toLabeledLemma lio₁ ℓ₀ ℓ₂))) pr))
  ... | yes p = lemmaz ℓ₀ p (proj₁ (lio₀ ℓ₂)) (proj₁ (lio₁ ℓ₂)) (lioᵣ ℓ₂ ℓ₂ (inj₁ refl))

  returnᵣ A₀ A₁ Aᵣ a₀ a₁ aᵣ ℓ₀ .ℓ₀ (inj₁ refl) with ℓ₀ ⊑d ℓ*
  ... | yes p = inj₁ (refl , p , ⟦inj₁⟧ aᵣ)
  ... | no ¬p = inj₂ (¬p , ¬p)
  returnᵣ A₀ A₁ Aᵣ a₀ a₁ aᵣ ℓ₀ ℓ₁ (inj₂ y) = inj₂ y

  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) with lioᵣ ℓ₀ ℓ₀ (inj₁ refl)
  ... | inj₂ (not₀ , not₁) = inj₂ ((λ pr → not₀ (⊑-trans (lemma₂ lio₀ cont₀) pr)) , λ pr → not₁ (⊑-trans (lemma₂ lio₁ cont₁) pr))
  ... | inj₁ x with inspect (lio₀ ℓ₀)
  ... | ((inj₁ x₂ , snd₁) , snd) with≡ x₁ with inspect (lio₁ ℓ₀)
  ... | ((inj₂ y , snd₃) , snd₂) with≡ x₃ = ⊥-elim (helper₁ (proj₂ (proj₂ x)) (cong (λ x → proj₁ (proj₁ x)) x₁) (cong (λ x → proj₁ (proj₁ x)) x₃))
  ... | ((inj₁ x₄ , snd₃) , snd₂) with≡ x₃ = contᵣ x₂ x₄ (helper₀ (proj₂ (proj₂ x)) (cong (λ x → proj₁ (proj₁ x)) x₁) (cong (λ x → proj₁ (proj₁ x)) x₃)) snd₁ snd₃ (inj₁ snd₁≡snd₃)
    where
      snd₁≡snd₃ : snd₁ ≡ snd₃
      snd₁≡snd₃ = begin
        snd₁ ≡⟨ sym (cong (λ x → proj₂ (proj₁ x)) x₁) ⟩
        proj₂ (proj₁ (lio₀ ℓ₀)) ≡⟨ proj₁ x ⟩
        proj₂ (proj₁ (lio₁ ℓ₀)) ≡⟨ cong (λ x → proj₂ (proj₁ x)) x₃ ⟩
        snd₃ ∎
  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl)
      | inj₁ x
      | ((inj₂ y , snd₁) , snd) with≡ x₁ with inspect (lio₁ ℓ₀)
  ... | ((inj₁ x₃ , snd₃) , snd₂) with≡ x₂ = ⊥-elim (helper₁ (⟦⊎⟧sym (proj₁ (proj₁ (lio₀ ℓ₀))) (proj₁ (proj₁ (lio₁ ℓ₀))) (proj₂ (proj₂ x))) (cong (λ x → proj₁ (proj₁ x)) x₂) (cong (λ x → proj₁ (proj₁ x)) x₁))
  ... | ((inj₂ y₁ , snd₃) , snd₂) with≡ x₂ = inj₁ (snd₁≡snd₃ , ⊑-trans (⊑-eql (cong (λ x → proj₂ (proj₁ x)) (sym x₁))) (proj₁ (proj₂ x)) , ⟦inj₂⟧ (helper₂ (proj₂ (proj₂ x)) (cong (λ x → proj₁ (proj₁ x)) x₁) (cong (λ x → proj₁ (proj₁ x)) x₂)))
    where
      snd₁≡snd₃ : snd₁ ≡ snd₃
      snd₁≡snd₃ = begin
        snd₁ ≡⟨ sym (cong (λ x → proj₂ (proj₁ x)) x₁) ⟩
        proj₂ (proj₁ (lio₀ ℓ₀)) ≡⟨ proj₁ x ⟩
        proj₂ (proj₁ (lio₁ ℓ₀)) ≡⟨ cong (λ x → proj₂ (proj₁ x)) x₂ ⟩
        snd₃ ∎
  bindᵣ A₀ A₁ Aᵣ B₀ B₁ Bᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ ℓ₁ (inj₂ (fst , snd)) =
    inj₂ ((λ pr → fst (⊑-trans (lemma₁ lio₀ cont₀) pr)) , λ pr → snd (⊑-trans (lemma₁ lio₁ cont₁) pr))

  userExceptionᵣ : UserException → UserException → Set
  userExceptionᵣ = _≡_

  withContextᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
                → (s₀ s₁ : String) → (sᵣ : s₀ ≡ s₁)
                → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → (lioᵣ : LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁)
                → LIOᵣ A₀ A₁ Aᵣ (withContext m₀ s₀ lio₀) (withContext m₁ s₁ lio₁)
  withContextᵣ A₀ A₁ Aᵣ s₀ s₁ sᵣ lio₀ lio₁ lioᵣ ℓ₀ .ℓ₀ (inj₁ refl) with lioᵣ ℓ₀ ℓ₀ (inj₁ refl)
  ... | inj₂ (fst , snd) = inj₂ (fst , snd)
  withContextᵣ A₀ A₁ Aᵣ s₀ s₁ sᵣ lio₀ lio₁ lioᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₁ (fst , fst₁ , snd) with proj₁ (proj₁ (lio₀ ℓ₀)) | proj₁ (proj₁ (lio₁ ℓ₀))
  withContextᵣ A₀ A₁ Aᵣ s₀ s₁ sᵣ lio₀ lio₁ lioᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₁ (fst , fst₁ , snd) | inj₁ x | inj₁ x₁ = inj₁ (fst , fst₁ , snd)
  withContextᵣ A₀ A₁ Aᵣ s₀ .s₀ refl lio₀ lio₁ lioᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₁ (fst , fst₁ , ⟦inj₂⟧ refl) | inj₂ y | inj₂ .y = inj₁ (fst , fst₁ , ⟦inj₂⟧ refl)
  withContextᵣ A₀ A₁ Aᵣ s₀ s₁ sᵣ lio₀ lio₁ lioᵣ ℓ₀ ℓ₁ (inj₂ (fst , snd)) =
    inj₂ ((λ pr → fst (⊑-trans (proj₂ (lio₀ ℓ₀)) pr)) , λ pr → snd (⊑-trans (proj₂ (lio₁ ℓ₁)) pr))

  throwᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
          → (e₀ e₁ : UserException) → (eᵣ : userExceptionᵣ e₀ e₁)
          → LIOᵣ A₀ A₁ Aᵣ (throw m₀ e₀) (throw m₁ e₁)
  -- same as for return
  throwᵣ A₀ A₁ Aᵣ e₀ .e₀ refl ℓ₀ .ℓ₀ (inj₁ refl) with ℓ₀ ⊑d ℓ*
  ... | yes p = inj₁ (refl , p , ⟦inj₂⟧ refl)
  ... | no ¬p = inj₂ (¬p , ¬p)
  throwᵣ A₀ A₁ Aᵣ e₀ e₁ eᵣ ℓ₀ ℓ₁ (inj₂ y) = inj₂ y

  -- This could be made much nicer by proving a lemma about monotonicity
  -- of the catching part in the output label of the first argument to
  -- catch
  catchᵣ : (A₀ A₁ : Set) → (Aᵣ : A₀ → A₁ → Set)
          → (lio₀ : LIO m₀ A₀) → (lio₁ : LIO m₁ A₁) → (lioᵣ : LIOᵣ A₀ A₁ Aᵣ lio₀ lio₁)
          → (cont₀ : E → LIO m₀ A₀) → (cont₁ : E → LIO m₁ A₁)
          → (contᵣ : (e₀ e₁ : E) → (eᵣ : Eᵣ e₀ e₁) → LIOᵣ A₀ A₁ Aᵣ (cont₀ e₀) (cont₁ e₁))
          → LIOᵣ A₀ A₁ Aᵣ (catch m₀ lio₀ cont₀) (catch m₁ lio₁ cont₁)
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) with lioᵣ ℓ₀ ℓ₀ (inj₁ refl)
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₁ (fst , fst₁ , snd) with proj₁ (proj₁ (lio₀ ℓ₀)) | proj₁ (proj₁ (lio₁ ℓ₀))
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₁ (fst , fst₁ , snd) | inj₁ x | inj₁ x₁ = inj₁ (fst , fst₁ , snd)
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₁ (fst , fst₁ , ⟦inj₂⟧ x) | inj₂ y | inj₂ y₁ = contᵣ y y₁ x (proj₂ (proj₁ (lio₀ ℓ₀))) (proj₂ (proj₁ (lio₁ ℓ₀))) (inj₁ fst)
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₂ (fst , snd) with proj₁ (proj₁ (lio₀ ℓ₀)) | proj₁ (proj₁ (lio₁ ℓ₀))
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₂ (fst , snd) | inj₁ x | inj₁ x₁ = inj₂ ((λ pr → fst pr) , λ pr → snd pr)
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₂ (fst , snd) | inj₁ x | inj₂ y = inj₂ ((λ pr → fst pr) , λ pr → snd (⊑-trans (proj₂ (cont₁ y (proj₂ (proj₁ (lio₁ ℓ₀))))) pr))
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₂ (fst , snd) | inj₂ y | inj₁ x = inj₂ ((λ pr → fst (⊑-trans (proj₂ (cont₀ y _)) pr)) , snd)
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ .ℓ₀ (inj₁ refl) | inj₂ (fst , snd) | inj₂ y | inj₂ y₁ = inj₂ ((λ pr → fst (⊑-trans (proj₂ (cont₀ y _)) pr)) , λ pr → snd (⊑-trans (proj₂ (cont₁ y₁ _)) pr))
  catchᵣ A₀ A₁ Aᵣ lio₀ lio₁ lioᵣ cont₀ cont₁ contᵣ ℓ₀ ℓ₁ (inj₂ (fst , snd)) =
    inj₂ ((λ pr → fst (⊑-trans (proj₂ (catch m₀ lio₀ cont₀ ℓ₀)) pr)) , λ pr → snd (⊑-trans (proj₂ (catch m₁ lio₁ cont₁ ℓ₁)) pr))

⟦DIFC⟧ : ⟦LIOInterface⟧ DIFC DIFC
⟦DIFC⟧ = record { Mk⟦DIFC⟧ }

open LIOInterface
open ⟦LIOInterface⟧

data Univ : Set where
  bool : Univ
  labeled : Univ → Univ
  lio : Univ → Univ

El : Univ → LIOInterface → Set
El bool m        = Bool
El (labeled u) m = Labeled m (El u m)
El (lio u) m     = LIO m (El u m)

Rel : (u : Univ)
    → (m₀ : LIOInterface) → (m₁ : LIOInterface)
    → (mᵣ : ⟦LIOInterface⟧ m₀ m₁)
    → El u m₀ → El u m₁ → Set
Rel bool m₀ m₁ mᵣ        = _≡_
Rel (labeled u) m₀ m₁ mᵣ = Labeledᵣ mᵣ (El u m₀) (El u m₁) (Rel u m₀ m₁ mᵣ)
Rel (lio u) m₀ m₁ mᵣ     = LIOᵣ mᵣ (El u m₀) (El u m₁) (Rel u m₀ m₁ mᵣ)

postulate parametricity : (u₀ u₁ : Univ)
                        → (o : (m : LIOInterface) → El u₀ m → El u₁ m)
                        → (m₀ m₁ : LIOInterface) → (mᵣ : ⟦LIOInterface⟧ m₀ m₁)
                        → (i₀ : El u₀ m₀) → (i₁ : El u₀ m₁)
                        → (iᵣ : Rel u₀ m₀ m₁ mᵣ i₀ i₁)
                        → Rel u₁ m₀ m₁ mᵣ (o m₀ i₀) (o m₁ i₁)

_~⟨_⟩L_ : L → L → L → Set
ℓc₀ ~⟨ ℓ ⟩L ℓc₁ = (ℓc₀ ⊑ ℓ) ⊎ (ℓc₁ ⊑ ℓ) → ℓc₀ ≡ ℓc₁

mutual
  data _⊢_~⟨_⟩_ : (u : Univ) → El u DIFC → L → El u DIFC → Set where
    ~bool     : ∀{ℓ : L}{b₀ b₁ : Bool} → b₀ ≡ b₁ → bool ⊢ b₀ ~⟨ ℓ ⟩ b₁
  
    ~labeled₀ : ∀{ℓ ℓ' : L}{u : Univ}{v₀ v₁ : El u DIFC}
              → u ⊢ v₀ ~⟨ ℓ ⟩ v₁
              → (labeled u) ⊢ (inj₁ v₀ , ℓ') ~⟨ ℓ ⟩ (inj₁ v₁ , ℓ')
  
    ~labeled₂ : ∀{ℓ ℓ' : L}{u : Univ}{e : E}
              → (labeled u) ⊢ (inj₂ e , ℓ') ~⟨ ℓ ⟩ (inj₂ e , ℓ')
  
    ~labeled₃ : ∀{ℓ ℓ' : L}{u : Univ}{v₀ v₁ : El u DIFC ⊎ E}
              → ¬ (ℓ' ⊑ ℓ)
              → (labeled u) ⊢ (v₀ , ℓ') ~⟨ ℓ ⟩ (v₁ , ℓ')

    ~lio      : ∀{ℓ : L}{u : Univ}{lio₀ lio₁ : LIO DIFC (El u DIFC)}
              → ((ℓc₀ ℓc₁ : L) → ℓc₀ ~⟨ ℓ ⟩L ℓc₁ → u ⊢ proj₁ (lio₀ ℓc₀) ~⟨ ℓ ⟩Cfg proj₁ (lio₁ ℓc₁))
              → (lio u) ⊢ lio₀ ~⟨ ℓ ⟩ lio₁
  
  data _⊢_~⟨_⟩Cfg_ : (u : Univ) → (El u DIFC ⊎ E) × L → L → (El u DIFC ⊎ E) × L → Set where
    ~cfg₀ : ∀{ℓ : L}{u : Univ}{v₀ v₁ : El u DIFC}{ℓc₀ ℓc₁ : L}
          → ℓc₀ ~⟨ ℓ ⟩L ℓc₁
          → ℓc₀ ⊑ ℓ
          → ℓc₁ ⊑ ℓ
          → u ⊢ v₀ ~⟨ ℓ ⟩ v₁
          → u ⊢ (inj₁ v₀ , ℓc₀) ~⟨ ℓ ⟩Cfg (inj₁ v₁ , ℓc₁)

    ~cfg₁ : ∀{ℓ : L}{u : Univ}{e : E}{ℓc₀ ℓc₁ : L}
          → ℓc₀ ~⟨ ℓ ⟩L ℓc₁
          → u ⊢ (inj₂ e , ℓc₀) ~⟨ ℓ ⟩Cfg (inj₂ e , ℓc₁)

    ~cfg₂ : ∀{ℓ : L}{u : Univ}{v₀ v₁ : El u DIFC ⊎ E}{ℓc₀ ℓc₁ : L}
          → (ℓc₀ ~⟨ ℓ ⟩L ℓc₁)
          → (¬ (ℓc₀ ⊑ ℓ)) ⊎ (¬ (ℓc₁ ⊑ ℓ))
          → u ⊢ (v₀ , ℓc₀) ~⟨ ℓ ⟩Cfg (v₁ , ℓc₁)

  ~ℓ*-to-param : (u : Univ) → (x₀ x₁ : El u DIFC) → u ⊢ x₀ ~⟨ ℓ* ⟩ x₁ → Rel u DIFC DIFC ⟦DIFC⟧ x₀ x₁
  ~ℓ*-to-param bool x₀ x₁ (~bool x) = x
  ~ℓ*-to-param (labeled u) (.(inj₁ _) , snd) (.(inj₁ _) , .snd) (~labeled₀ x) = refl , λ p → ⟦inj₁⟧ (~ℓ*-to-param u _ _ x)
  ~ℓ*-to-param (labeled u) (.(inj₂ _) , snd) (.(inj₂ _) , .snd) ~labeled₂ = refl , λ p → ⟦inj₂⟧ refl
  ~ℓ*-to-param (labeled u) (fst , snd) (fst₁ , .snd) (~labeled₃ x) = refl , λ p → ⊥-elim (x p)
  ~ℓ*-to-param (lio u) x₀ x₁ (~lio x) ℓ₀ ℓ₁ (inj₁ x₂) = ~ℓ*-cfg-to-param u x₀ x₁ ℓ₀ ℓ₁ (inj₁ x₂) (x ℓ₀ ℓ₁ λ p → x₂)
  ~ℓ*-to-param (lio u) x₀ x₁ (~lio x) ℓ₀ ℓ₁ (inj₂ y) = ~ℓ*-cfg-to-param u x₀ x₁ ℓ₀ ℓ₁ (inj₂ y) (x ℓ₀ ℓ₁ λ { (inj₁ p) → ⊥-elim (proj₁ y p) ; (inj₂ p) → ⊥-elim (proj₂ y p) })

  ~ℓ*-cfg-to-param : (u : Univ)
                   → (x₀ x₁ : LIO DIFC (El u DIFC)) 
                   → (ℓc₀ ℓc₁ : L)
                   → ℓc₀ ≡ ℓc₁ ⊎ ((ℓc₀ ̷⊑ ℓ*) × (ℓc₁ ̷⊑ ℓ*))
                   → u ⊢ proj₁ (x₀ ℓc₀) ~⟨ ℓ* ⟩Cfg proj₁ (x₁ ℓc₁)
                   → ( (proj₂ (proj₁ (x₀ ℓc₀)) ≡ proj₂ (proj₁ (x₁ ℓc₁)))
                     × ( (proj₂ (proj₁ (x₀ ℓc₀)) ⊑ ℓ*)
                       × ((Rel u DIFC DIFC ⟦DIFC⟧ ⟦⊎⟧ _≡_) (proj₁ (proj₁ (x₀ ℓc₀)))
                                                           (proj₁ (proj₁ (x₁ ℓc₁)))))
                     ) ⊎ ( (proj₂ (proj₁ (x₀ ℓc₀)) ̷⊑ ℓ*)
                         × (proj₂ (proj₁ (x₁ ℓc₁)) ̷⊑ ℓ*)
                         )
  ~ℓ*-cfg-to-param u x₀ x₁ ℓc₀ ℓc₁ x x₂ with proj₁ (x₀ ℓc₀) | proj₁ (x₁ ℓc₁)
  ~ℓ*-cfg-to-param u x₀ x₁ ℓc₀ ℓc₁ x (~cfg₀ x₂ x₃ x₄ x₅) | .(inj₁ _) , snd | .(inj₁ _) , snd₁ = inj₁ (x₂ (inj₁ x₃) , x₃ , ⟦inj₁⟧ (~ℓ*-to-param u _ _ x₅))
  ~ℓ*-cfg-to-param u x₀ x₁ ℓc₀ ℓc₁ x (~cfg₁ x₂) | .(inj₂ _) , snd | .(inj₂ _) , snd₁ with snd ⊑d ℓ* | snd₁ ⊑d ℓ*
  ... | yes p | r = inj₁ (x₂ (inj₁ p) , p , ⟦inj₂⟧ refl)
  ... | no ¬p | yes p' = inj₂ (¬p , λ pr → ¬p (⊑-trans (⊑-eql (x₂ (inj₂ pr))) pr))
  ... | no ¬p | no ¬p' = inj₂ (¬p , ¬p')
  ~ℓ*-cfg-to-param u x₀ x₁ ℓc₀ ℓc₁ x (~cfg₂ x₂ (inj₁ x₃)) | fst , snd | fst₁ , snd₁ with snd₁ ⊑d ℓ*
  ... | yes p = inj₂ (x₃ , λ pr → x₃ (⊑-trans (⊑-eql (x₂ (inj₂ pr))) pr))
  ... | no ¬p = inj₂ (x₃ , ¬p)
  ~ℓ*-cfg-to-param u x₀ x₁ ℓc₀ ℓc₁ x (~cfg₂ x₂ (inj₂ y)) | fst , snd | fst₁ , snd₁ with snd ⊑d ℓ*
  ... | yes p = inj₂ ((λ pr → y (⊑-trans (⊑-eql (sym (x₂ (inj₁ pr)))) pr)) , y)
  ... | no ¬p = inj₂ (¬p , y)
  
  param-to-~ℓ* : (u : Univ) → (x₀ x₁ : El u DIFC) → Rel u DIFC DIFC ⟦DIFC⟧ x₀ x₁ → u ⊢ x₀ ~⟨ ℓ* ⟩ x₁ 
  param-to-~ℓ* bool x₀ x₁ x = ~bool x
  param-to-~ℓ* (labeled u) (fst , .(proj₂ x₁)) x₁ (refl , snd) with proj₂ x₁ ⊑d ℓ*
  ... | no ¬p = ~labeled₃ ¬p
  ... | yes p with snd p
  ... | ⟦inj₁⟧ x = ~labeled₀ (param-to-~ℓ* u _ _ x)
  ... | ⟦inj₂⟧ refl = ~labeled₂
  param-to-~ℓ* (lio u) x₀ x₁ x = ~lio (λ ℓc₀ ℓc₁ p → param-cfg-to-~ℓ* u x₀ x₁ ℓc₀ ℓc₁ p (x ℓc₀ ℓc₁ (hlp ℓc₀ ℓc₁ p)))

  hlp : (ℓc₀ ℓc₁ : L)
      → ((ℓc₀ ⊑ ℓ*) ⊎ (ℓc₁ ⊑ ℓ*) → ℓc₀ ≡ ℓc₁)
      → ℓc₀ ≡ ℓc₁ ⊎ Σ (ℓc₀ ⊑ ℓ* → ⊥) (λ x₂ → ℓc₁ ⊑ ℓ* → ⊥)
  hlp ℓc₀ ℓc₁ pr with ℓc₀ ⊑d ℓ* | ℓc₁ ⊑d ℓ*
  ... | yes p | r     = inj₁ (pr (inj₁ p))
  ... | no ¬p | no ¬q = inj₂ (¬p , ¬q)
  ... | no ¬p | yes q = inj₁ (pr (inj₂ q))

  param-cfg-to-~ℓ* : (u : Univ)
                   → (x₀ x₁ : LIO DIFC (El u DIFC))
                   → (ℓc₀ ℓc₁ : L)
                   → (ℓc₀ ~⟨ ℓ* ⟩L ℓc₁)
                   → ( (proj₂ (proj₁ (x₀ ℓc₀)) ≡ proj₂ (proj₁ (x₁ ℓc₁)))
                     × ((proj₂ (proj₁ (x₀ ℓc₀)) ⊑ ℓ*)
                       × ((Rel u DIFC DIFC ⟦DIFC⟧ ⟦⊎⟧ _≡_) (proj₁ (proj₁ (x₀ ℓc₀))) (proj₁ (proj₁ (x₁ ℓc₁))))
                       )
                     )
                   ⊎
                     ( (proj₂ (proj₁ (x₀ ℓc₀)) ⊑ ℓ* → ⊥)
                     × (proj₂ (proj₁ (x₁ ℓc₁)) ⊑ ℓ* → ⊥)
                     )
                   → u ⊢ proj₁ (x₀ ℓc₀) ~⟨ ℓ* ⟩Cfg proj₁ (x₁ ℓc₁)
  param-cfg-to-~ℓ* u x₀ x₁ ℓc₀ ℓc₁ x (inj₁ (fst , fst₁ , snd)) with (proj₁ (x₀ ℓc₀)) | (proj₁ (x₁ ℓc₁))
  param-cfg-to-~ℓ* u x₀ x₁ ℓc₀ ℓc₁ x (inj₁ (refl , fst₁ , ⟦inj₁⟧ x₄)) | inj₁ x₂ , snd₁ | inj₁ x₃ , snd₂ = ~cfg₀ (λ p → refl) fst₁ fst₁ (param-to-~ℓ* u x₂ x₃ x₄)
  param-cfg-to-~ℓ* u x₀ x₁ ℓc₀ ℓc₁ x (inj₁ (refl , fst₁ , ⟦inj₂⟧ refl)) | inj₂ y , snd₁ | inj₂ y₁ , snd₂ = ~cfg₁ λ p → refl 
  param-cfg-to-~ℓ* u x₀ x₁ ℓc₀ ℓc₁ x (inj₂ (fst , snd)) = ~cfg₂ (λ { (inj₁ p) → ⊥-elim (fst p) ; (inj₂ p) → ⊥-elim (snd p) }) (inj₁ fst)

NI : (u₀ u₁ : Univ)
   → (o : (m : LIOInterface) → El u₀ m → El u₁ m)
   → (x₀ x₁ : El u₀ DIFC)
   → u₀ ⊢ x₀ ~⟨ ℓ* ⟩ x₁
   → u₁ ⊢ (o DIFC x₀) ~⟨ ℓ* ⟩ (o DIFC x₁)
NI u₀ u₁ o x₀ x₁ x = param-to-~ℓ* u₁ (o DIFC x₀) (o DIFC x₁)
                      (parametricity u₀ u₁ o DIFC DIFC ⟦DIFC⟧ x₀ x₁
                        (~ℓ*-to-param u₀ x₀ x₁ x))


