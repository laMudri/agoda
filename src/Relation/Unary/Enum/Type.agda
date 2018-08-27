module Relation.Unary.Enum.Type where

  open import Data.List as List
  open import Data.List.Any as Any
  open import Data.List.Membership.Propositional
  open import Data.Unit

  open import Relation.Unary as U hiding (_∈_)
  open import Relation.Unary.Enum

  Enum-type : ∀ {a} → Set a → Set _
  Enum-type A = Enum (U.U {A = A})

  module Enum-type {a} {A : Set a} (e : Enum-type A) where
    open Enum e public using (list)
    open Enum e using () renaming (complete to complete′)

    complete : ∀ a → a ∈ list
    complete a = complete′ {a} tt

  enum-type : ∀ {a} {A : Set a}
              (list : List A) → (∀ a → a ∈ list) → Enum-type A
  enum-type list complete = record
    { list = list
    ; consistent = λ _ → tt
    ; complete = λ {a} _ → complete a
    }
