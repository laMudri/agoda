module Relation.Unary.Enum.Fix where

  open import Data.List as List
  open import Data.Product as Σ

  open import Relation.Unary hiding (_∈_)
  open import Relation.Unary.Enum

  fix-enum : ∀ {a b p} {A : Set a} {B : Set b} (P : Pred A p) → Enum-type A →
             ((acc : List A) (s : B) → ∃₂ λ acc′ s′ → acc ⊂ acc′) →
