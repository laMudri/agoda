module Data.List.Any.Membership.Map {a b} {A : Set a} {B : Set b} where
  open import Data.List as List
  open import Data.List.Any as Any
  open Membership-≡
  open import Data.Product as Σ

  open import Function

  open import Relation.Binary.PropositionalEquality as PEq

  ∈-map : ∀ (f : A → B) {x xs} → x ∈ xs → f x ∈ List.map f xs
  ∈-map f (here px) = here (cong f px)
  ∈-map f (there x∈xs) = there (∈-map f x∈xs)

  ∈-unmap : ∀ (f : A → B) {xs y} → y ∈ List.map f xs → (∃ λ x → y ≡ f x × x ∈ xs)
  ∈-unmap f {[]} ()
  ∈-unmap f {x ∷ xs} (here px) = x , px , here refl
  ∈-unmap f {x ∷ xs} (there fx∈fxs) =
    Σ.map id (Σ.map id there) (∈-unmap f fx∈fxs)
