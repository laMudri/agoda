module Data.List.NonEmpty.Any where

  open import Data.List.Any
  open import Data.List.NonEmpty

  open import Level

  open import Relation.Binary hiding (Decidable)
  open import Relation.Nullary
  open import Relation.Unary as U hiding (_∈_)

  data Any⁺ {a p} {A : Set a} (P : Pred A p) : List⁺ A → Set (a ⊔ p) where
    here : ∀ {x xs} (px : P x) → Any⁺ P (x ∷ xs)
    there : ∀ {x xs} (pxs : Any P xs) → Any⁺ P (x ∷ xs)

  any⁺ : ∀ {a p} {A : Set a} {P : Pred A p} → Decidable P → Decidable (Any⁺ P)
  any⁺ P? (x ∷ xs) with P? x
  any⁺ P? (x ∷ xs) | yes px = yes (here px)
  any⁺ P? (x ∷ xs) | no ¬px with any P? xs
  any⁺ P? (x ∷ xs) | no ¬px | yes pxs = yes (there pxs)
  any⁺ P? (x ∷ xs) | no ¬px | no ¬pxs =
    no (λ { (here px) → ¬px px ; (there pxs) → ¬pxs pxs })

  module Membership⁺ {c ℓ} (S : Setoid c ℓ) where
    open Setoid S renaming (Carrier to C)
    open Membership S

    _∈⁺_ : C → List⁺ C → Set _
    x ∈⁺ xs = Any⁺ (x ≈_) xs
