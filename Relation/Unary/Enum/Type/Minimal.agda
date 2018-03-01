module Relation.Unary.Enum.Type.Minimal {a} {A : Set a} where

  open import Data.Fin
  open import Data.List

  --open import Function
  open import Function.Inverse
  open import Function.Inverse.PropositionalEquality

  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Binary.Subsetoid (≡.setoid A)
  open import Relation.Unary
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Type
  open import Relation.Unary.Enum.Minimal (U {A = A})

  MinimalEnum-type↔Fin :
    ∀ (e : Enum-type {a} A) → Minimal e → A ↔ Fin (length (Enum-type.list e))
  MinimalEnum-type↔Fin e min = MinimalEnum↔Fin e min ∘ ↔∣U
    where
    open Enum-type e
