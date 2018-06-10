open import Data.Nat as Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import axioms

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
  name : Name → Term             -- names
  abs  : Name → Term → Term      -- abstractions
  comb : Term → Term → Term      -- combinations
  var  : Var → Term              -- logic variables

Subst' = List (Var × Name)
Subst  = List (Var × Term)
data Absent' : Subst' → Var → Set where
  ε : ∀ {x} → Absent' [] x
  s : ∀ {σ x a x'} → ¬ x ≡ x'
      → Absent' σ x → Absent' ((x' , a) ∷ σ) x
data Present' : Subst' → Var → Name → Set where
  f : ∀ {σ x a x'} → x ≡ x'
      → Present' ((x' , a) ∷ σ) x a
  s : ∀ {σ x a x' a'} → ¬ x ≡ x'
      → Present' σ x a → Present' ((x' , a') ∷ σ) x a
find?' : (σ : Subst') → (x : Var) → (Absent' σ x) ⊎ (∃ λ a → Present' σ x a)
find?' [] x                                     = inj₁ ε
find?' ((x' , _) ∷ σ) x with x Nat.≟ x'
find?' ((x' , _) ∷ σ) x | yes p                 = inj₂ (_ , f p)
find?' ((x' , _) ∷ σ) x | no ¬p with find?' σ x
find?' ((x' , _) ∷ σ) x | no ¬p | inj₁ x₁       = inj₁ (s ¬p x₁)
find?' ((x' , _) ∷ σ) x | no ¬p | inj₂ (a , bd) = inj₂ (a , s ¬p bd)
data Absent : Subst → Var → Set where
  ε : ∀ {x} → Absent [] x
  s : ∀ {σ x a x'} → ¬ x ≡ x'
      → Absent σ x → Absent ((x' , a) ∷ σ) x
data Present : Subst → Var → Term → Set where
  f : ∀ {σ x t x'} → x ≡ x'
      → Present ((x' , t) ∷ σ) x t
  s : ∀ {σ x t x' t'} → ¬ x ≡ x'
      → Present σ x t → Present ((x' , t') ∷ σ) x t
find? : (σ : Subst) → (x : Var) → (Absent σ x) ⊎ (∃ λ t → Present σ x t)
find? [] x                                     = inj₁ ε
find? ((x' , _) ∷ σ) x with x Nat.≟ x'
find? ((x' , _) ∷ σ) x | yes p                 = inj₂ (_ , f p)
find? ((x' , _) ∷ σ) x | no ¬p with find? σ x
find? ((x' , _) ∷ σ) x | no ¬p | inj₁ x₁       = inj₁ (s ¬p x₁)
find? ((x' , _) ∷ σ) x | no ¬p | inj₂ (t , bd) = inj₂ (t , s ¬p bd)

data Subst'2Subst : Subst' → Subst → Set where
  ε   : Subst'2Subst [] []
  ext : ∀ {σ' σ x a} → Subst'2Subst σ' σ
        → Subst'2Subst ((x , a) ∷ σ') ((x , name a) ∷ σ)

pν  = List (Name × Scope × Name × Scope)
pν' = List (Name × Scope × Var × Scope)
pδ  = List (Var × Scope × Var × Scope)

data _∈_ : ∀ {A} → A → List A → Set where
  this : ∀ {A} {hd hd' : A} {tl : List A}
         → hd ≡ hd' → hd ∈ (hd' ∷ tl)
  step : ∀ {A} {hd hd' : A} {tl : List A}
         → ¬ hd ≡ hd' → hd ∈ tl → hd ∈ (hd' ∷ tl)

data _∼_ : (Name × Scope) → (Name × Scope) → Set where
  same-bound : ∀ {a₁ Φ₁ i₁ a₂ Φ₂ i₂}
               → i₁ ≡ i₂
               → Bd Φ₁ a₁ i₁ → Bd Φ₂ a₂ i₂
               → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
  same-free  : ∀ {a₁ Φ₁ a₂ Φ₂}
               → a₁ ≡ a₂
               → Fr Φ₁ a₁ → Fr Φ₂ a₂
               → (a₁ , Φ₁) ∼ (a₂ , Φ₂)

data _⊢_⇒ν_ : Subst' → pν → Subst' → Set where
  ε   : ∀ {σ} → σ ⊢ [] ⇒ν σ
  NN  : ∀ {σ₀ a₁ Φ₁ a₂ Φ₂ p σ₁}
        → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
        → σ₀ ⊢ p ⇒ν σ₁
        → σ₀ ⊢ (a₁ , Φ₁ , a₂ , Φ₂) ∷ p ⇒ν σ₁
data _⊢_⇒ν'_ : Subst' → pν' → Subst' → Set where
  ε   : ∀ {σ} → σ ⊢ [] ⇒ν' σ
  NV  : ∀ {σ₀ a₁ Φ₁ x₂ a₂ Φ₂ p σ₁}
        → Absent' σ₀ x₂
        → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
        → ((x₂ , a₂) ∷ σ₀) ⊢ p ⇒ν' σ₁
        → σ₀ ⊢ (a₁ , Φ₁ , x₂ , Φ₂) ∷ p ⇒ν' σ₁
  NV' : ∀ {σ₀ a₁ Φ₁ x₂ a₂ Φ₂ p σ₁}
        → Present' σ₀ x₂ a₂
        → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
        → σ₀ ⊢ p ⇒ν' σ₁
        → σ₀ ⊢ (a₁ , Φ₁ , x₂ , Φ₂) ∷ p ⇒ν' σ₁

data Cut : pδ → Var → (pδ × pδ) → Set where
  ε    : ∀ {x} → Cut [] x ([] , [])
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
 
data _⊢_⇒pull_ : (Subst' × List Var) → pδ → (Subst' × List Var) → Set where
  ε  : ∀ {σ xs} → (σ , xs) ⊢ [] ⇒pull (σ , xs)
  NN : ∀ {σ₀ xs₀ x₁ Φ₁ a₁ x₂ Φ₂ a₂ p σ₁ xs₁}
       → Present' σ₀ x₁ a₁ → Present' σ₀ x₂ a₂
       → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
       → (σ₀ , xs₀) ⊢ p ⇒pull (σ₁ , xs₁)
       → (σ₀ , xs₀) ⊢ ((x₁ , Φ₁ , x₂ , Φ₂) ∷ p) ⇒pull (σ₁ , xs₁)
  NV : ∀ {σ₀ xs₀ x₁ Φ₁ a₁ x₂ Φ₂ a₂ p σ₁ xs₁}
       → Present' σ₀ x₁ a₁ → Absent' σ₀ x₂
       → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
       → ((x₂ , a₂) ∷ σ₀ , x₂ ∷ xs₀) ⊢ p ⇒pull (σ₁ , xs₁)
       → (σ₀ , xs₀) ⊢ ((x₁ , Φ₁ , x₂ , Φ₂) ∷ p) ⇒pull (σ₁ , xs₁)

data _⊢_⇒δ_ : (Subst' × pδ) → List Var → (Subst' × pδ) → Set where
  εxs  : ∀ {σ δ} → (σ , δ) ⊢ [] ⇒δ (σ , δ)
  εδ   : ∀ {σ xs} → (σ , []) ⊢ xs ⇒δ (σ , [])
  pull : ∀ {σ₀ δ₀ x xs σ₀' δ₀' pδ-of-x xs' σ₁ δ₁}
         → Cut δ₀ x (δ₀' , pδ-of-x)
         → (σ₀ , xs) ⊢ pδ-of-x ⇒pull (σ₀' , xs')
         → (σ₀' , δ₀') ⊢ xs' ⇒δ (σ₁ , δ₁)
         → (σ₀ , δ₀) ⊢ (x ∷ xs) ⇒δ (σ₁ , δ₁)

data _⊢_⇒s_ : (pν × pν' × pδ × Subst) → (Term × Scope × Term × Scope)
              → (pν × pν' × pδ × Subst) → Set where
  NN   : ∀ {p₀ p₀' δ₀ σ₀ a₁ Φ₁ a₂ Φ₂} 
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (name a₁ , Φ₁ , name a₂ , Φ₂) ⇒s
           ((a₁ , Φ₁ , a₂ , Φ₂) ∷ p₀ , p₀' , δ₀ , σ₀)
  NV   : ∀ {p₀ p₀' δ₀ σ₀ a₁ Φ₁ x₂ Φ₂} 
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (name a₁ , Φ₁ , var x₂ , Φ₂) ⇒s
           (p₀ , (a₁ , Φ₁ , x₂ , Φ₂) ∷ p₀' , δ₀ , σ₀)
  VV   : ∀ {p₀ p₀' δ₀ σ₀ x₁ Φ₁ x₂ Φ₂} 
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (var x₁ , Φ₁ , var x₂ , Φ₂) ⇒s
           (p₀ , p₀' , (x₁ , Φ₁ , x₂ , Φ₂) ∷ δ₀ , σ₀)
  CC   : ∀ {p₀ p₀' δ₀ σ₀ l₁ r₁ Φ₁ l₂ r₂ Φ₂ p p' δ σ p₁ p₁' δ₁ σ₁}
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (l₁ , Φ₁ , l₂ , Φ₂) ⇒s (p , p' , δ , σ)
         → (p , p' , δ , σ) ⊢ (r₁ , Φ₁ , r₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (comb l₁ r₁ , Φ₁ , comb l₂ r₂ , Φ₂) ⇒s
           (p₁ , p₁' , δ₁ , σ₁)
  AA   : ∀ {p₀ p₀' δ₀ σ₀ a₁ t₁ Φ₁ a₂ t₂ Φ₂ p₁ p₁' δ₁ σ₁}
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (t₁ , a₁ ∷ Φ₁ , t₂ , a₂ ∷ Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (abs a₁ t₁ , Φ₁ , abs a₂ t₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
  VC   : ∀ {p₀ p₀' δ₀ σ₀ x₁ xₗ xᵣ Φ₁ l₂ r₂ Φ₂ p p' δ σ p₁ p₁' δ₁ σ₁}
         → Absent σ₀ x₁
         → (p₀ , p₀' , δ₀ , (x₁ , (comb (var xₗ) (var xᵣ))) ∷ σ₀)
           ⊢ (var xₗ , Φ₁ , l₂ , Φ₂) ⇒s (p , p' , δ , σ)
         → (p , p' , δ , σ) ⊢ (var xᵣ , Φ₁ , r₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (var x₁ , Φ₁ , comb l₂ r₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
  VC'  : ∀ {p₀ p₀' δ₀ σ₀ x₁ tₗ tᵣ Φ₁ l₂ r₂ Φ₂ p p' δ σ p₁ p₁' δ₁ σ₁}
         → Present σ₀ x₁ (comb tₗ tᵣ)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (tₗ , Φ₁ , l₂ , Φ₂) ⇒s (p , p' , δ , σ)
         → (p , p' , δ , σ) ⊢ (tᵣ , Φ₁ , r₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (var x₁ , Φ₁ , comb l₂ r₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
  VA   : ∀ {p₀ p₀' δ₀ σ₀ x₁ a₁ xₜ Φ₁ a₂ i t₂ Φ₂ p₁ p₁' δ₁ σ₁}
         → Absent σ₀ x₁
         → Bd Φ₁ a₁ i → Bd Φ₂ a₂ i
         → (p₀ , p₀' , δ₀ , (x₁ , (abs a₁ (var xₜ))) ∷ σ₀)
           ⊢ (var xₜ , a₁ ∷ Φ₁ , t₂ , a₂ ∷ Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (var x₁ , Φ₁ , abs a₂ t₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
  VA'  : ∀ {p₀ p₀' δ₀ σ₀ x₁ a₁ xₜ Φ₁ a₂ t₂ Φ₂ p₁ p₁' δ₁ σ₁}
         → Absent σ₀ x₁
         → Fr Φ₁ a₁ → Fr Φ₂ a₂
         → (p₀ , p₀' , δ₀ , (x₁ , (abs a₁ (var xₜ))) ∷ σ₀)
           ⊢ (var xₜ , a₁ ∷ Φ₁ , t₂ , a₂ ∷ Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (var x₁ , Φ₁ , abs a₂ t₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
  VA'' : ∀ {p₀ p₀' δ₀ σ₀ x₁ a₁ t₁ Φ₁ a₂ t₂ Φ₂ p₁ p₁' δ₁ σ₁}
         → Present σ₀ x₁ (abs a₁ t₁)
         → (p₀ , p₀' , δ₀ , σ₀)
           ⊢ (t₁ , a₁ ∷ Φ₁ , t₂ , a₂ ∷ Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)
         → (p₀ , p₀' , δ₀ , σ₀) ⊢ (var x₁ , Φ₁ , abs a₂ t₂ , Φ₂) ⇒s (p₁ , p₁' , δ₁ , σ₁)

data _⊢_⇒ρ_ : (pν × pν' × pδ × Subst) → List (Term × Scope × Term × Scope)
              → (pν × pν' × pδ × Subst) → Set where
  ε : ∀ {p δ σ} → (p , δ , σ) ⊢ [] ⇒ρ (p , δ , σ)
  s : ∀ {p₀ p₀' δ₀ σ₀ e es p p' δ σ p₁ p₁' δ₁ σ₁}
      → (p₀ , p₀' , δ₀ , σ₀) ⊢ e ⇒s (p , p' , δ , σ)
      → (p , p' , δ , σ) ⊢ es ⇒ρ (p₁ , p₁' , δ₁ , σ₁)
      → (p₀ , p₀' , δ₀ , σ₀) ⊢ (e ∷ es) ⇒ρ (p₁ , p₁' , δ₁ , σ₁)

uniq-free : ∀ {Φ a} → (x : Fr Φ a) → (y : Fr Φ a) → x ≡ y
uniq-free ε ε                                 = refl
uniq-free (s x1 p1) (s x2 p2) with uniq-free p1 p2 | ⊥-funext x1 x2
uniq-free (s x1 p1) (s .x1 .p1) | refl | refl = refl

uniq-bound : ∀ {Φ a i i'} → (x : Bd Φ a i) → (y : Bd Φ a i')
             → Σ (i ≡ i') (λ ieq → (subst (λ k → Bd Φ a k) ieq) x ≡ y)
uniq-bound (b x) (b x') with x | x'
uniq-bound (b x) (b x') | refl | refl                   = refl , refl
uniq-bound (b x) (s nope y)                             = ⊥-elim (nope x)
uniq-bound (s nope x₁) (b x)                            = ⊥-elim (nope x)
uniq-bound (s nope x) (s nope' y) with ⊥-funext nope nope'
uniq-bound (s nope x) (s .nope y) | refl with uniq-bound x y
uniq-bound (s nope x) (s .nope .x) | refl | refl , refl = refl , refl

free-bound-dec : ∀ {Φ a i} → Bd Φ a i → Fr Φ a → ⊥
free-bound-dec {[]} {a} () fr
free-bound-dec {a' ∷ Φ} {a} bd fr with a Nat.≟ a'
free-bound-dec {a' ∷ Φ} {.a'} (b _) (s ¬eq _) | yes refl
  = ¬eq refl
free-bound-dec {a' ∷ Φ} {.a'} (s ¬eq _) (s _ _) | yes refl
  = ¬eq refl
free-bound-dec {a' ∷ Φ} {a} (b p) fr | no ¬p
  = ¬p p
free-bound-dec {a' ∷ Φ} {a} (s _ bd) (s _ fr) | no ¬p
  = free-bound-dec bd fr

