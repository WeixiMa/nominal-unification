open import Data.Nat as Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import base
open import alpha

data Sub : Term → Subst → Term → Set where
  name : ∀ {a σ} → Sub (name a) σ (name a)
  abs  : ∀ {a t t' σ} →  Sub t σ t' → Sub (abs a t) σ (abs a t')
  comb : ∀ {l r l' r' σ} → Sub l σ l' → Sub r σ r'
         → Sub (comb l r) σ (comb l r)
  var  : ∀ {x σ} → Absent σ x → Sub (var x) σ (var x)
  var' : ∀ {x t t' σ} → Present σ x t → Sub t σ t'
         → Sub (var x) σ t'

data Subst2Queue : Subst' → List Var → Set where

-- data _⊆_ : Subst' → Subst' → Set where
--   ε : ∀ {σ} → [] ⊆ σ
--   f : ∀ {pr σ' σ} → σ' ⊆ σ → pr ∈ σ → (pr ∷ σ') ⊆ σ

data _⊆_ : ∀ {A} → List A → List A → Set where
  ε : ∀ {A} {ls : List A} → [] ⊆ ls
  f : ∀ {A} {hd : A} {tl ls} → tl ⊆ ls → hd ∈ ls → (hd ∷ tl) ⊆ ls

postulate
  _ν≟_ : Decidable {A = (Name × Scope × Name × Scope)} _≡_
  diffHead : ∀ {x₁ x₂ x₁' x₂' : Name} {Φ₁ Φ₂ Φ₁' Φ₂' : Scope}
             → ¬ x₁ ≡ x₁'
             → ¬ (x₁ , Φ₁ , x₂ , Φ₂) ≡ (x₁' , Φ₁' , x₂' , Φ₂')
  diffHead' : ∀ {x₁ x₂ x₁' x₂' : Name} {Φ₁ Φ₂ Φ₁' Φ₂' : Scope}
              → ¬ (x₁ , Φ₁ , x₂ , Φ₂) ≡ (x₁' , Φ₁' , x₂' , Φ₂')
              → ¬ x₁ ≡ x₁'
  replace : ∀ {a₁ Φ₁ a₂ Φ₂ a₁' Φ₁' a₂' Φ₂'}
          → (a₁' , Φ₁' , a₂' , Φ₂') ≡ (a₁ , Φ₁ , a₂ , Φ₂)
          → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
          → (a₁' , Φ₁') ∼ (a₂' , Φ₂')
  ⊆refl : ∀ {A} {σ : List A} → σ ⊆ σ
  ⊆tran : ∀ {A} {σ₀ σ₁ σ₂ : List A} → σ₀ ⊆ σ₁ → σ₁ ⊆ σ₂ → σ₀ ⊆ σ₂
  ⊆ext : ∀ {A} {hd : A} {σ} → σ ⊆ (hd ∷ σ)
  ∈larger : ∀ {A} {x : A} {s s'} → x ∈ s → s ⊆ s' → x ∈ s'
  ν'≟ : ∀ (a₁ a₂ a₁' a₂' : Name) (Φ₁ Φ₂ Φ₁' Φ₂' : Scope)
       → ¬ (a₁ , Φ₁ , a₂ , Φ₂) ≡ (a₁' , Φ₁' , a₂' , Φ₂')
       ⊎ (a₁ , Φ₁ , a₂ , Φ₂) ≡ (a₁' , Φ₁' , a₂' , Φ₂')
         × a₁ ≡ a₁' × Φ₁ ≡ Φ₁' × a₂ ≡ a₂' × Φ₂ ≡ Φ₂'
  substIsFunction : ∀ {σ x a a'} → (p : Present' σ x a) → (p' : Present' σ x a')
                  → Σ (a ≡ a')
                    (λ aeq → (subst (λ name → Present' σ x name) aeq p) ≡ p')
  presentLarger : ∀ {x a σ σ'} → Present' σ x a → σ ⊆ σ'
                → Present' σ' x a
         
inRest : ∀ {A} {hd hd' : A} {tl : List A} → ¬ hd ≡ hd' → hd ∈ (hd' ∷ tl) → hd ∈ tl
inRest nope (this eq) = ⊥-elim (nope eq)
inRest _ (step _ i)   = i

inCut : ∀ {x₁ Φ₁ x₂ Φ₂ x δ δ-with-x δ-without-x}
        → Cut δ x (δ-without-x , δ-with-x)
        → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ → x₁ ≡ x
        → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ-with-x
inCut ε () eq
inCut {x₁} {Φ₁} {x₂} {Φ₂} {x} (this {.x} {x₁'} {Φ₁'} {x₂'} {Φ₂'} refl c) i refl
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
inCut {x₁'} {Φ₁} {x₂} {Φ₂} {x₁'} (this {.x₁'} {x₁'} {Φ₁'} {x₂'} {Φ₂'} refl c) i refl
   | inj₁ neq = step neq (inCut c (inRest neq i) refl)
inCut {x₁'} {Φ₁} {x₂} {Φ₂} {x₁'} (this {.x₁'} {x₁'} {Φ₁'} {x₂'} {Φ₂'} refl c) i refl
   | inj₂ (_ , refl , refl , refl , refl) = this refl
inCut {.x} {Φ₁} {x₂} {Φ₂} {x} (next {.x} {x₁'} {Φ₁'} {x₂'} {Φ₂'} neq c) i refl = inCut c (inRest (diffHead neq) i) refl

outCut : ∀ {x₁ Φ₁ x₂ Φ₂ x δ δ-with-x δ-without-x}
         → Cut δ x (δ-without-x , δ-with-x)
         → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ → ¬ x₁ ≡ x
         → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ-without-x
outCut ε () neq
outCut {x₁} {Φ₁} {x₂} {Φ₂} {x} (this {.x} {.x} {Φ₁'} {x₂'} {Φ₂'} refl c) i nope
  = outCut c (inRest (diffHead nope) i) nope
outCut {x₁} {Φ₁} {x₂} {Φ₂} {x} (next {.x} {x₁'} {Φ₁'} {x₂'} {Φ₂'} neq' c) i nope
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
outCut {x₁} {Φ₁} {x₂} {Φ₂} {x} (next {.x} {x₁'} {Φ₁'} {x₂'} {Φ₂'} neq' c) i nope
    | inj₁ neq = step neq (outCut c (inRest neq i) nope)
outCut {x₁} {Φ₁} {x₂} {Φ₂} {x} (next {.x} {x₁'} {Φ₁'} {x₂'} {Φ₂'} neq' c) i nope
    | inj₂ (eq , refl , refl , refl , refl) = this refl

ν'extσ : ∀ {σ' σ p} → σ' ⊢ p ⇒ν' σ → σ' ⊆ σ
ν'extσ ε = ⊆refl
ν'extσ (NV _ _ d) = ⊆tran ⊆ext (ν'extσ d)
ν'extσ (NV' _ _  d) = ν'extσ d

pullextσ : ∀ {σ₀ xs₀ δ σ₁ xs₁} → (σ₀ , xs₀) ⊢ δ ⇒pull (σ₁ , xs₁) → σ₀ ⊆ σ₁
pullextσ ε = ⊆refl
pullextσ (NN _ _ _ d) = pullextσ d
pullextσ (NV x x₃ x₄ d) = ⊆tran ⊆ext (pullextσ d)

δextσ : ∀ {σ₀ δ₀ xs σ₁ δ₁} → (σ₀ , δ₀) ⊢ xs ⇒δ (σ₁ , δ₁) → σ₀ ⊆ σ₁
δextσ εxs = ⊆refl
δextσ εδ = ⊆refl
δextσ (pull _ p d) = ⊆tran (pullextσ p) (δextσ d)

ν✓ : ∀ {σ₀ pν σ₁ a₁ Φ₁ a₂ Φ₂}
     → σ₀ ⊢ pν ⇒ν σ₁ → (a₁ , Φ₁ , a₂ , Φ₂) ∈ pν
     → [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂)
ν✓ ε ()
ν✓ {a₁ = a₁} {Φ₁} {a₂} {Φ₂} (NN {a₁ = a₁'} {Φ₁'} {a₂'} {Φ₂'} _ _) i
  with (a₁ , Φ₁ , a₂ , Φ₂) ν≟ (a₁' , Φ₁' , a₂' , Φ₂')
ν✓ {a₁ = a₁} {Φ₁} {a₂} {Φ₂} (NN {a₁ = a₁'} {Φ₁'} {a₂'} {Φ₂'} eq d) i
   | yes p = NN (replace p eq)
ν✓ {a₁ = a₁} {Φ₁} {a₂} {Φ₂} (NN {a₁ = a₁'} {Φ₁'} {a₂'} {Φ₂'} _ d) i
   | no ¬p = ν✓ d (inRest ¬p i)

ν'✓ : ∀ {σ₀ pν σ₁ a₁ Φ₁ x₂ Φ₂}
      → σ₀ ⊢ pν ⇒ν' σ₁ → (a₁ , Φ₁ , x₂ , Φ₂) ∈ pν
      → Σ Name λ a₂ → (Present' σ₁ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
ν'✓ ε ()
ν'✓ {a₁ = a₁} {Φ₁} {x₂} {Φ₂} (NV {a₁ = a₁'} {Φ₁'} {x₂'} {a₂'} {Φ₂'} _ _ _) i
  with ν'≟ a₁ x₂ a₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
ν'✓ {a₁ = a₁} {Φ₁} {x₂} {Φ₂} (NV {a₁ = a₁'} {Φ₁'} {x₂'} {a₂'} {Φ₂'} _ _ d) i
   | inj₁ neq = ν'✓ d (inRest neq i)
ν'✓ {a₁ = a₁} {Φ₁} {x₂} {Φ₂} (NV {a₁ = a₁'} {Φ₁'} {x₂'} {a₂'} {Φ₂'} _ eq d) i
   | inj₂ (_ , refl , refl , refl , refl)
   = a₂' , presentLarger (f refl) (ν'extσ d) , NN eq 
ν'✓ {a₁ = a₁} {Φ₁} {x₂} {Φ₂} (NV' {a₁ = a₁'} {Φ₁'} {x₂'} {a₂'} {Φ₂'} _ _ _) i
  with ν'≟ a₁ x₂ a₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
ν'✓ {a₁ = a₁} {Φ₁} {x₂} {Φ₂} (NV' {a₁ = a₁'} {Φ₁'} {x₂'} {a₂'} {Φ₂'} _ _ d) i
   | inj₁ neq = ν'✓ d (inRest neq i)
ν'✓ {a₁ = a₁} {Φ₁} {x₂} {Φ₂} (NV' {a₁ = a₁'} {Φ₁'} {x₂'} {a₂'} {Φ₂'} fd eq d) i
   | inj₂ (_ , refl , refl , refl , refl)
   = a₂' , presentLarger fd (ν'extσ d) , NN eq

δ✓' : ∀ {x₁ Φ₁ x₂ Φ₂ σ₀ σ₁ δ xs₀ xs₁}
      → (σ₀ , xs₀) ⊢ δ ⇒pull (σ₁ , xs₁)
      → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ
      → ∃ λ a₁ → ∃ λ a₂ → Present' σ₁ x₁ a₁ × Present' σ₁ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂)
δ✓' ε ()
δ✓' {x₁ = x₁} {Φ₁} {x₂} {Φ₂} (NN {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
δ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NN {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
   | inj₁ neq = δ✓' d (inRest neq i)
δ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NN {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
   | inj₂ (_ , refl , refl , refl , refl)
   = a₁' , a₂' , presentLarger fd₁ (pullextσ d) , presentLarger fd₂ (pullextσ d) , NN eq
δ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NV {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} x x₅ x₆ d) i
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
δ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NV {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} x x₅ x₆ d) i
   | inj₁ neq = δ✓' d (inRest neq i)
δ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NV {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
   | inj₂ (_ , refl , refl , refl , refl)
   = a₁' , a₂' , presentLarger fd₁ (⊆tran ⊆ext (pullextσ d)) , presentLarger (f refl) (pullextσ d) , NN eq

cutSmaller : ∀ {δ δ₀ δ₁ x} → Cut δ x (δ₀ , δ₁) → δ₀ ⊆ δ × δ₁ ⊆ δ
cutSmaller = {!!}

cutLemma : ∀ {δ x δ₀ δ₁ eqn} → Cut δ x (δ₀ , δ₁) → eqn ∈ δ₀ → eqn ∉ δ₁
cutLemma = {!!}

notin : ∀ {σ₀ xs₀ δ σ₁ xs₁ x₁ x₂ Φ₁ Φ₂}
        → (σ₀ , xs₀) ⊢ δ ⇒pull (σ₁ , xs₁)
        → (x₁ , Φ₁ , x₂ , Φ₂) ∉ δ → Absent' σ₀ x₁ → Absent' σ₀ x₂
        → Absent' σ₁ x₁ × Absent' σ₁ x₂
notin = {!!}

disjoint : ∀ {σ₀ δ₀ x xs xs' σ₁ δ₁ δ₀-with-x}
           → Cut δ₀ x (δ₁ , δ₀-with-x)
           → (σ₀ , xs) ⊢ δ₀-with-x ⇒pull (σ₁ , xs')
           → ((x₁ x₂ : Name) → (Φ₁ Φ₂ : Scope) → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ₀ → Absent' σ₀ x₁ × Absent' σ₀ x₂)
           → ((x₁ x₂ : Name) → (Φ₁ Φ₂ : Scope) → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ₁ → Absent' σ₁ x₁ × Absent' σ₁ x₂)
disjoint c p g x₁ x₂ Φ₁ Φ₂ i
  with cutSmaller c
disjoint c p g x₁ x₂ Φ₁ Φ₂ i
  | sub , _
  with g x₁ x₂ Φ₁ Φ₂ (∈larger i sub)
disjoint c p g x₁ x₂ Φ₁ Φ₂ i
  | _ , _ | nfd₁ , nfd₂ = notin p (cutLemma c i) nfd₁ nfd₂ 

δ✓ : ∀ {σ₀ δ₀ xs σ₁ δ₁ x₁ Φ₁ x₂ Φ₂}
     → (σ₀ , δ₀) ⊢ xs ⇒δ (σ₁ , δ₁) → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ₀
     → ((x₁ x₂ : Name) → (Φ₁ Φ₂ : Scope) → (x₁ , Φ₁ , x₂ , Φ₂) ∈ δ₀ → Absent' σ₀ x₁ × Absent' σ₀ x₂)
     → (∃ λ a₁ → ∃ λ a₂ → Present' σ₁ x₁ a₁ × Present' σ₁ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
     ⊎ (Absent' σ₁ x₁ × Absent' σ₁ x₂ × δ₁ ⊢ (var x₁ , Φ₁) ≈ (var x₂ , Φ₂))
δ✓ εxs i g with g _ _ _ _ i
δ✓ εxs i g | abs₁ , abs₂ = inj₂ (abs₁ , abs₂ , VV (base i))
δ✓ εδ () _
δ✓ {x₁ = x} (pull {x = x'} {xs} c p d) i g
  with x Nat.≟ x'
δ✓ {x₁ = x} (pull {x = x'} {xs} c p d) i g
   | yes eq
  with inCut c i eq
... | x∈δ
  with δ✓' p x∈δ
... | a₁ , a₂ , fd₁ , fd₂ , aeq
  = inj₁ (a₁ , a₂ , presentLarger fd₁ (δextσ d) , presentLarger fd₂ (δextσ d) , aeq)
δ✓ {x₁ = x} (pull {x = x'} {xs} c p d) i g
   | no neq = δ✓ d (outCut c i neq) (disjoint c p g)
