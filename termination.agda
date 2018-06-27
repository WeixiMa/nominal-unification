open import Data.Nat as Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

open import base

data Length : ∀ {A : Set} → ℕ → List A → Set where
  ε    : ∀ {A} → Length {A} zero []
  step : ∀ {l A} {hd : A} {tl : List A} → Length l tl
         → Length (suc l) (hd ∷ tl)

cut : ∀ {l} → (χ : pχ) → (x : Var) → Length l χ
      → ∃ λ l₁ → ∃ λ χ₁ → ∃ λ l₂ → ∃ λ χ₂
      → Cut χ x (χ₁ , χ₂) × Length l₁ χ₁ × Length l₂ χ₂ × l₁ + l₂ ≡ l
cut = {!!}

pull : (σ₀ : Subst') → (xs₀ : List Var) → (χ : pχ) 
       → Maybe (∃ λ σ₁ → ∃ λ xs₁ → (σ₀ , xs₀) ⊢ χ ⇒pull (σ₁ , xs₁))
pull = {!!}

runχ : (n l₁ l₂ : ℕ) → (σ₀ : Subst') → (χ₀ : pχ) → (xs : List Var)
       → Length l₁ χ₀ → Length l₂ xs → n ≡ l₁ + l₂
       → Maybe (∃ λ σ₁ → ∃ λ χ₁ → (σ₀ , χ₀) ⊢ xs ⇒χ (σ₁ , χ₁))
runχ n l₁ l­2
