open import Data.Empty
open import Relation.Binary.PropositionalEquality

postulate
  -- This special case of funext is provable if there's η-rules for ⊥
  -- and Π. But Agda doesn't seem to have definitional η for ⊥ -
  -- otherwise, λ f g → refl would be a proof, but it fails,
  -- complaining that f x is not convertible with g x.
  ⊥-funext : ∀{α} {A : Set α} → (f g : (x : A) → ⊥) → f ≡ g
