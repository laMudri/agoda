module Data.Fin.Encode2 where
  open import Data.Fin
  open import Data.Fin.Enum
  open import Data.Nat
  open import Data.Product

  open import Function
  open import Function.Inverse
  open import Function.Inverse.PropositionalEquality

  open import Relation.Unary.Enum

  ×↔ : ∀ {m n} → (Fin m × Fin n) ↔ Fin (m * n)
  ×↔ {m} {n} = {!Fin-enum m ×-enum Fin-enum n!}
