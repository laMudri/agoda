module Data.List.Extras where

  open import Data.Fin
  open import Data.List
  open import Data.List.Any
  open import Data.List.Membership.Propositional
  open import Data.Nat

  open import Relation.Binary.PropositionalEquality

  module _ {a} {A : Set a} where
    lookup-by-Fin : (xs : List A) → Fin (length xs) → A
    lookup-by-Fin [] ()
    lookup-by-Fin (x ∷ xs) zero = x
    lookup-by-Fin (x ∷ xs) (suc i) = lookup-by-Fin xs i

    lookup-by-Fin-∈ : ∀ xs i → lookup-by-Fin xs i ∈ xs
    lookup-by-Fin-∈ [] ()
    lookup-by-Fin-∈ (x ∷ xs) zero = here refl
    lookup-by-Fin-∈ (x ∷ xs) (suc i) = there (lookup-by-Fin-∈ xs i)

    index-lookup-by-Fin-∈ : ∀ xs i → index (lookup-by-Fin-∈ xs i) ≡ i
    index-lookup-by-Fin-∈ [] ()
    index-lookup-by-Fin-∈ (x ∷ xs) zero = refl
    index-lookup-by-Fin-∈ (x ∷ xs) (suc i) =
      cong suc (index-lookup-by-Fin-∈ xs i)

    lookup-by-Fin-index : ∀ {x xs} (x∈xs : x ∈ xs) →
                          lookup-by-Fin xs (index x∈xs) ≡ x
    lookup-by-Fin-index (here px) = sym px
    lookup-by-Fin-index (there x∈xs) = lookup-by-Fin-index x∈xs
