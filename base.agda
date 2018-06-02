open import Data.Nat as Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

Var = ℕ
Name = ℕ
Scope = List Name

data Fr : Scope → Name → Set where
  ε : ∀ {x} → Fr [] x
  s : ∀ {Φ x x'} → ¬ x ≡ x'
      → Fr Φ x → Fr (x' ∷ Φ) x 
data Bd : Scope → Name → ℕ → Set where
  b : ∀ {Φ x x'} → x ≡ x'
      → Bd (x' ∷ Φ) x zero
  s : ∀ {Φ x i x'} → ¬ x ≡ x'
      → Bd Φ x i → Bd (x' ∷ Φ) x (suc i)
bind? : (Φ : Scope) → (x : Name) → (Fr Φ x) ⊎ (∃ λ i → Bd Φ x i)
bind? [] x                              = inj₁ ε
bind? (y ∷ Φ) x with x Nat.≟ y
bind? (y ∷ Φ) x | yes p                 = inj₂ (zero , b p)
bind? (y ∷ Φ) x | no ¬p with bind? Φ x
bind? (y ∷ Φ) x | no ¬p | inj₁ fr       = inj₁ (s ¬p fr)
bind? (y ∷ Φ) x | no ¬p | inj₂ (i , bd) = inj₂ (suc i , s ¬p bd)

data Term : Set where
  name : Name → Term
  abs  : Name → Term → Term
  comb : Term → Term → Term
  var  : Var → Term

Sbst = List (Var × Name)
Subst  = List (Var × Term)
data Absent : Sbst → Var → Set where
  ε : ∀ {x} → Absent [] x
  s : ∀ {σ x a x'} → ¬ x ≡ x'
      → Absent σ x → Absent ((x' , a) ∷ σ) x
data Present : Sbst → Var → Name → Set where
  f : ∀ {σ x a x'} → x ≡ x'
      → Present ((x' , a) ∷ σ) x a
  s : ∀ {σ x a x' a'} → ¬ x ≡ x'
      → Present σ x a → Present ((x' , a') ∷ σ) x a
find? : (σ : Sbst) → (x : Var) → (Absent σ x) ⊎ (∃ λ a → Present σ x a)
find? [] x                                     = inj₁ ε
find? ((x' , _) ∷ σ) x with x Nat.≟ x'
find? ((x' , _) ∷ σ) x | yes p                 = inj₂ (_ , f p)
find? ((x' , _) ∷ σ) x | no ¬p with find? σ x
find? ((x' , _) ∷ σ) x | no ¬p | inj₁ x₁       = inj₁ (s ¬p x₁)
find? ((x' , _) ∷ σ) x | no ¬p | inj₂ (a , bd) = inj₂ (a , s ¬p bd)

pν = List ((Name × Scope × Name × Scope) ⊎ (Name × Scope × Var × Scope))
pδ = List (Var × Scope × Var × Scope)

data _∼_ : (Name × Scope) → (Name × Scope) → Set where
  same-bound : ∀ {a₁ Φ₁ i₁ a₂ Φ₂ i₂}
               → i₁ ≡ i₂
               → Bd Φ₁ a₁ i₁ → Bd Φ₂ a₂ i₂
               → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
  same-free  : ∀ {a₁ Φ₁ a₂ Φ₂}
               → a₁ ≡ a₂
               → Fr Φ₁ a₁ → Fr Φ₂ a₂
               → (a₁ , Φ₁) ∼ (a₂ , Φ₂)

data _⊢_⇒ν_ : Sbst → pν → Sbst → Set where
  ε   : ∀ {σ} → σ ⊢ [] ⇒ν σ
  NN  : ∀ {σ₀ a₁ Φ₁ a₂ Φ₂ p σ₁}
        → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
        → σ₀ ⊢ p ⇒ν σ₁
        → σ₀ ⊢ ((inj₁ (a₁ , Φ₁ , a₂ , Φ₂)) ∷ p) ⇒ν σ₁
  NV  : ∀ {σ₀ a₁ Φ₁ x₂ a₂ Φ₂ p σ₁}
        → Absent σ₀ x₂
        → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
        → σ₀ ⊢ p ⇒ν σ₁
        → ((x₂ , a₂) ∷ σ₀) ⊢ ((inj₂ (a₁ , Φ₁ , x₂ , Φ₂)) ∷ p) ⇒ν σ₁
  NV' : ∀ {σ₀ a₁ Φ₁ x₂ a₂ Φ₂ p σ₁}
        → Present σ₀ x₂ x₂
        → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
        → σ₀ ⊢ p ⇒ν σ₁
        → σ₀ ⊢ ((inj₂ (a₁ , Φ₁ , x₂ , Φ₂)) ∷ p) ⇒ν σ₁

data Cut : pδ → Var → (pδ × pδ) → Set where
  ε : ∀ {x} → Cut [] x ([] , [])
  this : ∀ {x x₁ Φ₁ x₂ Φ₂ δ δ-with-x δ-without-x}
         → x ≡ x₁
         → Cut δ x (δ-with-x , δ-without-x)
         → Cut ((x₁ , Φ₁ , x₂ , Φ₂) ∷ δ) x
               (δ-without-x , (x₁ , Φ₁ , x₂ , Φ₂) ∷ δ-without-x)
  next : ∀ {x x₁ Φ₁ x₂ Φ₂ δ δ-with-x δ-without-x}
         → ¬ x ≡ x₁
         → Cut δ x (δ-with-x , δ-without-x)
         → Cut ((x₁ , Φ₁ , x₂ , Φ₂) ∷ δ) x
               ((x₁ , Φ₁ , x₂ , Φ₂) ∷ δ-without-x , δ-without-x)
 
data _⊢_⇒pull_ : (Sbst × List Var) → pδ → (Sbst × List Var) → Set where
  ε : ∀ {σ xs} → (σ , xs) ⊢ [] ⇒pull (σ , xs)
  NN : ∀ {σ₀ xs₀ x₁ Φ₁ a₁ x₂ Φ₂ a₂ p σ₁ xs₁}
       → Present σ₀ x₁ a₁ → Present σ₀ x₂ a₂
       → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
       → (σ₀ , xs₀) ⊢ p ⇒pull (σ₁ , xs₁)
       → (σ₀ , xs₀) ⊢ ((x₁ , Φ₁ , x₂ , Φ₂) ∷ p) ⇒pull (σ₁ , xs₁)
  NV : ∀ {σ₀ xs₀ x₁ Φ₁ a₁ x₂ Φ₂ a₂ p σ₁ xs₁}
       → Present σ₀ x₁ a₁ → Absent σ₀ x₂
       → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
       → ((x₂ , a₁) ∷ σ₀ , x₂ ∷ xs₀) ⊢ p ⇒pull (σ₁ , xs₁)
       → (σ₀ , xs₀) ⊢ ((x₁ , Φ₁ , x₂ , Φ₂) ∷ p) ⇒pull (σ₁ , xs₁)

data _⊢_⇒δ_ : (Sbst × pδ) → List Var → (Sbst × pδ) → Set where
  εxs : ∀ {σ δ} → (σ , δ) ⊢ [] ⇒δ (σ , δ)
  εδ : ∀ {σ xs} → (σ , []) ⊢ xs ⇒δ (σ , [])
  pull : ∀ {σ₀ δ₀ x xs σ₀' δ₀' pδ-of-x xs' σ₁ δ₁}
         → Cut δ₀ x (δ₀' , pδ-of-x)
         → (σ₀ , xs) ⊢ pδ-of-x ⇒pull (σ₀' , xs')
         → (σ₀' , δ₀') ⊢ xs' ⇒δ (σ₁ , δ₁)
         → (σ₀ , δ₀) ⊢ (x ∷ xs) ⇒δ (σ₁ , δ₁)

data _⊢_⇒s_ : (pν × pδ × Subst) → (Term × Scope × Term × Scope)
              → (pν × pδ × Subst) → Set where

data _⊢_⇒ρ_ : (pν × pδ × Subst) → List (Term × Scope × Term × Scope)
              → (pν × pδ × Subst) → Set where
  ε : ∀ {p δ σ} → (p , δ , σ) ⊢ [] ⇒ρ (p , δ , σ)
  s : ∀ {p₀ δ₀ σ₀ e es p₀' δ₀' σ₀' p₁ δ₁ σ₁}
      → (p₀ , δ₀ , σ₀) ⊢ e ⇒s (p₀' , δ₀' , σ₀')
      → (p₀' , δ₀' , σ₀') ⊢ es ⇒ρ (p₁ , δ₁ , σ₁)
      → (p₀' , δ₀' , σ₀') ⊢ (e ∷ es) ⇒ρ (p₁ , δ₁ , σ₁)
