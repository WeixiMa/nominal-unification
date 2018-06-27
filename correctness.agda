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

data _⊆_ : ∀ {A} → List A → List A → Set where
  ε    : ∀ {A} {ls : List A} → [] ⊆ ls
  here : ∀ {A} {hd : A} {tl ls} → tl ⊆ ls → hd ∈ ls → (hd ∷ tl) ⊆ ls

postulate
  eqnDec : Decidable {A = (ℕ × Scope × ℕ × Scope)} _≡_
  ν'≟ : ∀ (a₁ a₂ a₁' a₂' : Name) (Φ₁ Φ₂ Φ₁' Φ₂' : Scope)
        → ¬ (a₁ , Φ₁ , a₂ , Φ₂) ≡ (a₁' , Φ₁' , a₂' , Φ₂')
        ⊎ (a₁ , Φ₁ , a₂ , Φ₂) ≡ (a₁' , Φ₁' , a₂' , Φ₂')
          × a₁ ≡ a₁' × Φ₁ ≡ Φ₁' × a₂ ≡ a₂' × Φ₂ ≡ Φ₂'
  diffHead : ∀ {x₁ x₂ x₁' x₂' : Name} {Φ₁ Φ₂ Φ₁' Φ₂' : Scope}
             → ¬ x₁ ≡ x₁'
             → ¬ (x₁ , Φ₁ , x₂ , Φ₂) ≡ (x₁' , Φ₁' , x₂' , Φ₂')
  replace : ∀ {a₁ Φ₁ a₂ Φ₂ a₁' Φ₁' a₂' Φ₂'}
            → (a₁' , Φ₁' , a₂' , Φ₂') ≡ (a₁ , Φ₁ , a₂ , Φ₂)
            → (a₁ , Φ₁) ∼ (a₂ , Φ₂)
            → (a₁' , Φ₁') ∼ (a₂' , Φ₂')
  ⊆refl : ∀ {A} {σ : List A} → σ ⊆ σ
  ⊆tran : ∀ {A} {σ₀ σ₁ σ₂ : List A} → σ₀ ⊆ σ₁ → σ₁ ⊆ σ₂ → σ₀ ⊆ σ₂
  ⊆ext : ∀ {A} {x : A} {σ} → σ ⊆ (x ∷ σ)
  ⊆still : ∀ {A} {hd : A} {σ σ'} → σ ⊆ σ' → hd ∈ σ' → (hd ∷ σ) ⊆ σ'
  ∉smaller : ∀ {A} {x : A} {s s'} → x ∉ s → s' ⊆ s → x ∉ s'
  presentLarger : ∀ {x a σ σ'} → Present' σ x a → σ ⊆ σ'
                  → Present' σ' x a
  uniq-present' : ∀ {σ σ' x a a'} → σ ⊆ σ' → Present' σ x a → Present' σ' x a'
                  → a ≡ a'
  present2∈ : ∀ {σ x a} → Present' σ x a → (x , a) ∈ σ

inRest : ∀ {A} {hd hd' : A} {tl : List A} → ¬ hd ≡ hd' → hd ∈ (hd' ∷ tl) → hd ∈ tl
inRest nope (this eq) = ⊥-elim (nope eq)
inRest _ (step _ i)   = i

inCut : ∀ {x₁ Φ₁ x₂ Φ₂ x χ χ-with-x χ-without-x}
        → Cut χ x (χ-without-x , χ-with-x)
        → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ → x₁ ≡ x
        → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ-with-x
inCut ε () eq
inCut {x₁} {Φ₁} {x₂} {Φ₂} {x} (this {.x} {x₁'} {Φ₁'} {x₂'} {Φ₂'} refl c) i refl
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
inCut (this refl c) i refl
   | inj₁ neq = step neq (inCut c (inRest neq i) refl)
inCut (this refl c) i refl
   | inj₂ (_ , refl , refl , refl , refl) = this refl
inCut (next neq c) i refl = inCut c (inRest (diffHead neq) i) refl

outCut : ∀ {x₁ Φ₁ x₂ Φ₂ x χ χ-with-x χ-without-x}
         → Cut χ x (χ-without-x , χ-with-x)
         → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ → ¬ x₁ ≡ x
         → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ-without-x
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

pullextσ : ∀ {σ₀ xs₀ χ σ₁ xs₁} → (σ₀ , xs₀) ⊢ χ ⇒pull (σ₁ , xs₁) → σ₀ ⊆ σ₁
pullextσ ε = ⊆refl
pullextσ (NN _ _ _ d) = pullextσ d
pullextσ (NV x x₃ x₄ d) = ⊆tran ⊆ext (pullextσ d)

χextσ : ∀ {σ₀ χ₀ xs σ₁ χ₁} → (σ₀ , χ₀) ⊢ xs ⇒χ (σ₁ , χ₁) → σ₀ ⊆ σ₁
χextσ εxs = ⊆refl
χextσ εχ = ⊆refl
χextσ (step _ p d) = ⊆tran (pullextσ p) (χextσ d)

ν✓ : ∀ {σ₀ pν σ₁ a₁ Φ₁ a₂ Φ₂}
     → σ₀ ⊢ pν ⇒ν σ₁ → (a₁ , Φ₁ , a₂ , Φ₂) ∈ pν
     → [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂)
ν✓ ε ()
ν✓ {a₁ = a₁} {Φ₁} {a₂} {Φ₂} (NN {a₁ = a₁'} {Φ₁'} {a₂'} {Φ₂'} _ _) i
  with ν'≟ a₁ a₂ a₁' a₂' Φ₁ Φ₂ Φ₁' Φ₂'
ν✓ {a₁ = a₁} {Φ₁} {a₂} {Φ₂} (NN {a₁ = a₁'} {Φ₁'} {a₂'} {Φ₂'} _ d) i
   | inj₁ neq = ν✓ d (inRest neq i)
ν✓ {a₁ = a₁} {Φ₁} {a₂} {Φ₂} (NN {a₁ = a₁'} {Φ₁'} {a₂'} {Φ₂'} eq d) i
   | inj₂ (eq' , _ , _ , _ , _) = NN (replace eq' eq)

∈larger : ∀ {A} {dec : Decidable {A = A} _≡_} {ls ls'} {x : A} → ls' ⊆ ls → x ∈ ls' → x ∈ ls
∈larger ε ()
∈larger {dec = dec}{x = x} (here {hd = x'} sub x₁) xinls'
  with dec x x'
∈larger {dec = dec} {x = x} (here {hd = x'} sub p) xinls'
    | yes refl = p
∈larger {dec = dec} {x = x} (here {hd = x'} sub x₁) xinls'
    | no ¬p = ∈larger {dec = dec} sub (inRest ¬p xinls')

smaller : ∀ {ls ls'}
          → ls' ⊆ ls
          → (g : ℕ → Scope → ℕ → Scope → Set)
          → (∀ {a b c d} → (a , b , c , d) ∈ ls → g a b c d)
          → (∀ {a b c d} → (a , b , c , d) ∈ ls' → g a b c d)
smaller sub g h fd = h (∈larger {dec = eqnDec} sub fd)

✓ν : ∀ {σ₀ pν}
     → (∀ {a₁ Φ₁ a₂ Φ₂} → (a₁ , Φ₁ , a₂ , Φ₂) ∈ pν → [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
     → ∃ λ σ₁ → σ₀ ⊢ pν ⇒ν σ₁
✓ν {pν = []} g = _ , ε
✓ν {σ₀} {pν = x ∷ pν} g
  with g (this refl)
✓ν {σ₀} {x ∷ pν'} g
   | NN eq
 with ✓ν {σ₀} (smaller ⊆ext (λ a₁ → λ Φ₁ → λ a₂ → λ Φ₂ → [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂)) g)
... | σ₁ , d = σ₁ , NN eq d

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

✓ν' : ∀ {σ₀ σ pν}
      → (∀ {a₁ Φ₁ x₂ Φ₂} → (a₁ , Φ₁ , x₂ , Φ₂) ∈ pν
         → ∃ λ a₂ → Present' σ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
      → σ₀ ⊆ σ
      → ∃ λ σ₁ → σ₀ ⊢ pν ⇒ν' σ₁
✓ν' {pν = []} g sub = _ , ε
✓ν' {σ₀} {pν = (_ , _ , x₂ , _) ∷ pν} g sub
 with find?' σ₀ x₂
✓ν' {σ₀} {_} {(_ , _ , x₂ , _) ∷ pν} g sub
    | inj₁ nfd
 with g (this refl)
... | a₂ , fd , NN eq
 with ✓ν' {(x₂ , a₂) ∷ σ₀} {_} {pν} (smaller ⊆ext _ g) (⊆still sub (present2∈ fd))
... | σ₁ , d = σ₁ , NV nfd eq d
✓ν' {σ₀} {_} {(_ , _ , x₂ , _) ∷ pν} g sub
    | inj₂ (a₂ , fd)
 with g (this refl)
... | a₂' , fd' , NN eq
 with ✓ν' {σ₀} {pν = pν} (smaller ⊆ext _ g) sub
... | σ₁ , d
 with uniq-present' sub fd fd'
✓ν' {σ₀} {_} {(_ , _ , x₂ , _) ∷ pν} g sub
    | inj₂ (.a₂' , fd) | a₂' , fd' , NN eq | σ₁ , d | refl
    = σ₁ , NV' fd eq d
  
χ✓' : ∀ {x₁ Φ₁ x₂ Φ₂ σ₀ σ₁ χ xs₀ xs₁}
      → (σ₀ , xs₀) ⊢ χ ⇒pull (σ₁ , xs₁)
      → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ
      → ∃ λ a₁ → ∃ λ a₂ → Present' σ₁ x₁ a₁ × Present' σ₁ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂)
χ✓' ε ()
χ✓' {x₁ = x₁} {Φ₁} {x₂} {Φ₂} (NN {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
χ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NN {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
   | inj₁ neq = χ✓' d (inRest neq i)
χ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NN {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
   | inj₂ (_ , refl , refl , refl , refl)
   = a₁' , a₂' , presentLarger fd₁ (pullextσ d) , presentLarger fd₂ (pullextσ d) , NN eq
χ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NV {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} x x₅ x₆ d) i
  with ν'≟ x₁ x₂ x₁' x₂' Φ₁ Φ₂ Φ₁' Φ₂'
χ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NV {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} x x₅ x₆ d) i
   | inj₁ neq = χ✓' d (inRest neq i)
χ✓' {x₁} {Φ₁} {x₂} {Φ₂} (NV {x₁ = x₁'} {Φ₁'} {a₁'} {x₂'} {Φ₂'} {a₂'} fd₁ fd₂ eq d) i
   | inj₂ (_ , refl , refl , refl , refl)
   = a₁' , a₂' , presentLarger fd₁ (⊆tran ⊆ext (pullextσ d)) , presentLarger (f refl) (pullextσ d) , NN eq

✓χ' : ∀ {σ₀ σ xs₀ χ}
      → (∀ {x₁ Φ₁ x₂ Φ₂} → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ
         → ∃ λ a₁ → ∃ λ a₂ → Present' σ₀ x₁ a₁ × Present' σ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
      → σ₀ ⊆ σ
      → ∃ λ σ₁ → ∃ λ xs₁ → (σ₀ , xs₀) ⊢ χ ⇒pull (σ₁ , xs₁)
✓χ' {χ = []} g sub = _ , _ , ε
✓χ' {σ₀} {σ} {χ = (_ , _ , x₂ , _) ∷ χ} g sub
  with find?' σ₀ x₂ 
✓χ' {σ₀} {σ} {xs₀ = _} {(_ , _ , x₂ , _) ∷ χ} g sub
    | inj₁ nfd
  with g (this refl)
... | a₁ , a₂ , fd₁ , fd₂ , NN eq
  with ✓χ' {σ₀ = (x₂ , a₂) ∷ σ₀} {σ} {χ = χ} {!!} (⊆still sub (present2∈ fd₂))
... | σ₁ , xs₁ , p = σ₁ , xs₁ , NV fd₁ nfd eq p
✓χ' {σ₀} {σ} {xs₀ = _} {(_ , _ , x₂ , _) ∷ χ} g sub
    | inj₂ (a₂' , fd₂')
  with g (this refl)
... | a₁ , a₂ , fd₁ , fd₂ , NN eq
  with ✓χ' {σ₀ = σ₀} {σ} {χ = χ} (smaller ⊆ext _ g) sub
... | σ₁ , xs₁ , p
  with uniq-present' sub fd₂' fd₂
... | refl = σ₁ , xs₁ , NN fd₁ fd₂' eq p

χ✓ : ∀ {σ₀ χ₀ xs σ₁ χ₁ x₁ Φ₁ x₂ Φ₂}
     → (σ₀ , χ₀) ⊢ xs ⇒χ (σ₁ , χ₁) → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ₀
     → (∃ λ a₁ → ∃ λ a₂ → Present' σ₁ x₁ a₁ × Present' σ₁ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
     ⊎ (χ₁ ⊢ (var x₁ , Φ₁) ≈ (var x₂ , Φ₂))
χ✓ εxs i = inj₂ (VV (base i))
χ✓ εχ ()
χ✓ {x₁ = x} (step {x = x'} c p d) i
  with x Nat.≟ x'
χ✓ {x₁ = x} (step {x = x'} c p d) i
    | yes eq
  with inCut c i eq
... | x∈χ
  with χ✓' p x∈χ
... | a₁ , a₂ , fd₁ , fd₂ , aeq
  = inj₁ (a₁ , a₂ , presentLarger fd₁ (χextσ d) , presentLarger fd₂ (χextσ d) , aeq)
χ✓ {x₁ = x} (step {x = x'} c p d) i
   | no neq = χ✓ d (outCut c i neq)

✓χ : ∀ {σ₀ χ₀ xs σ}
     → (∀ {x₁ Φ₁ x₂ Φ₂}
       → (x₁ , Φ₁ , x₂ , Φ₂) ∈ χ₀
       → (∃ λ a₁ → ∃ λ a₂ → Present' σ x₁ a₁ × Present' σ x₂ a₂ × [] ⊢ (name a₁ , Φ₁) ≈ (name a₂ , Φ₂))
          ⊎ (χ₀ ⊢ (var x₁ , Φ₁) ≈ (var x₂ , Φ₂)))
     → σ₀ ⊆ σ
     → ∃ λ σ₁ → ∃ λ χ₁ → (σ₀ , χ₀) ⊢ xs ⇒χ (σ₁ , χ₁)
✓χ g sub = {!!}

