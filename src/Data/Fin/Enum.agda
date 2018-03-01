module Data.Fin.Enum where

  open import Data.Fin
  open import Data.List as List
  open import Data.List.Any
  open import Data.List.Any.Membership.Map
  open import Data.Nat

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Type

  Fin-enum : ∀ n → Enum-type (Fin n)
  Fin-enum zero = enum-type [] (λ ())
  Fin-enum (suc n) = enum-type
    (zero ∷ List.map suc list)
    (λ { zero → here refl
       ; (suc a) → there (∈-map suc (complete a)) })
    where
    open Enum-type (Fin-enum n)
