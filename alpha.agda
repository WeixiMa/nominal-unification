open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import base

data _⊢_≡_ : pδ → (Var × Scope) → (Var × Scope) → Set where
  base : ∀ {δ x₁ Φ₁ x₂ Φ₂}
         → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ
         → δ ⊢ (x₁ , Φ₁) ≡ (x₂ , Φ₂)
  refl : ∀ {δ x₁ Φ₁ x₂ Φ₂}
         → x₁ ≡ x₂ → Φ₁ ≡ Φ₂
         → δ ⊢ (x₁ , Φ₁) ≡ (x₂ , Φ₂)
  symm : ∀ {δ x₁ Φ₁ x₂ Φ₂}
         → δ ⊢ (x₂ , Φ₂) ≡ (x₁ , Φ₁)
         → δ ⊢ (x₁ , Φ₁) ≡ (x₂ , Φ₂)
  tran : ∀ {δ x₁ Φ₁ x₂ Φ₂ x' Φ'}
         → δ ⊢ (x₁ , Φ₁) ≡ (x' , Φ')
         → δ ⊢ (x' , Φ') ≡ (x₂ , Φ₂)
         → δ ⊢ (x₁ , Φ₁) ≡ (x₂ , Φ₂)

data _⊢_≈_ : pδ → (Term × Scope) → (Term × Scope) → Set where
  NN : ∀ {δ a₁ Φ₁ a₂ Φ₂} 
       → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
       → δ ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂)
  AA : ∀ {δ a₁ t₁ Φ₁ a₂ t₂ Φ₂}
       → δ ⊢ (t₁ , a₁ ∷ Φ₁) ≈ (t₂ , a₂ ∷ Φ₂)
       → δ ⊢ (abs a₁ t₁ , Φ₁) ≈ (abs a₂ t₂ , Φ₂)
  CC : ∀ {δ l₁ r₁ Φ₁ l₂ r₂ Φ₂}
       → δ ⊢ (l₁ , Φ₁) ≈ (l₂ , Φ₂)
       → δ ⊢ (r₁ , Φ₁) ≈ (r₂ , Φ₂)
       → δ ⊢ (comb l₁ r₁ , Φ₁) ≈ (comb l₂ r₂ , Φ₂)
  VV : ∀ {δ x₁ Φ₁ x₂ Φ₂}
       → δ ⊢ (x₁ , Φ₁) ≡ (x₂ , Φ₂)
       → δ ⊢ (var x₁ , Φ₁) ≈ (var x₂ , Φ₂)
 
≈refl : ∀ {δ t Φ} → δ ⊢ (t , Φ) ≈ (t , Φ)
≈refl {t = name a} {Φ} with bind? Φ a
≈refl {δ = _} {name a} {Φ} | inj₁ fr       = NN (same-free refl fr fr)
≈refl {δ = _} {name a} {Φ} | inj₂ (i , bd) = NN (same-bound refl bd bd)
≈refl {t = abs a t} = AA ≈refl
≈refl {t = comb l r} = CC ≈refl ≈refl
≈refl {t = var x} = VV (refl refl refl)

≈symm : ∀ {δ t₁ Φ₁ t₂ Φ₂} → δ ⊢ (t₁ , Φ₁) ≈ (t₂ , Φ₂)
        → δ ⊢ (t₂ , Φ₂) ≈ (t₁ , Φ₁) 
≈symm (NN (same-bound eq bd₁ bd₂)) = NN (same-bound (sym eq) bd₂ bd₁)
≈symm (NN (same-free eq fr₁ fr₂)) = NN (same-free (sym eq) fr₂ fr₁)
≈symm (AA aeq) = AA (≈symm aeq)
≈symm (CC aeql aeqr) = CC (≈symm aeql) (≈symm aeqr)
≈symm (VV eq) = VV (symm eq)

≈tran : ∀ {δ t₁ Φ₁ t' Φ' t₂ Φ₂}
        → δ ⊢ (t₁ , Φ₁) ≈ (t' , Φ')
        → δ ⊢ (t' , Φ') ≈ (t₂ , Φ₂)
        → δ ⊢ (t₁ , Φ₁) ≈ (t₂ , Φ₂)
≈tran (NN (same-bound eq bd₁ bd₂)) (NN (same-bound eq' bd₂' bd₃)) with uniq-bound bd₂ bd₂'
≈tran (NN (same-bound eq bd₁ bd₂)) (NN (same-bound eq' bd₂' bd₃)) | ieq , bdeq
  = NN (same-bound (trans eq (trans ieq eq')) bd₁ bd₃)
≈tran (NN (same-bound _ _ bd)) (NN (same-free _ fr _)) with free-bound-dec bd fr
≈tran (NN (same-bound _ _ bd)) (NN (same-free _ fr _)) | ()
≈tran (NN (same-free _ _ fr)) (NN (same-bound _ bd _)) with free-bound-dec bd fr
≈tran (NN (same-free _ _ fr)) (NN (same-bound _ bd _)) | ()
≈tran (NN (same-free eq fr₁ fr₂)) (NN (same-free eq' fr₂' fr₃)) with uniq-free fr₂ fr₂'
≈tran (NN (same-free eq fr₁ fr₂)) (NN (same-free eq' .fr₂ fr₃)) | refl
  = NN (same-free (trans eq eq') fr₁ fr₃)
≈tran (AA aeq1) (AA aeq2) = AA (≈tran aeq1 aeq2)
≈tran (CC aeq1 aeq2) (CC aeq3 aeq4) = CC (≈tran aeq1 aeq3) (≈tran aeq2 aeq4)
≈tran (VV eq) (VV eq') = VV (tran eq eq')


