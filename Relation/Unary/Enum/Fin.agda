module Relation.Unary.Enum.Fin where
  open import Data.Fin
  open import Data.List
  open import Data.List.Distinct
  open import Data.List.Sorted
  open import Data.Nat
  open import Data.Product

  open import Function
  open import Function.Inverse hiding (id; _∘_)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Minimal
  open import Relation.Unary.Enum.Type
  open import Relation.Unary.Enum.Type.Minimal
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  Enum-type↔Fin : ∀ {a A} → ((x y : A) → Dec (x ≡ y)) → Enum-type {a} A →
                  ∃ λ n → A ↔ Fin n
  Enum-type↔Fin _≟_ e =
    _ , MinimalEnum-type↔Fin (minimise U _≟_ e) (minimise-minimal U _≟_ e)
