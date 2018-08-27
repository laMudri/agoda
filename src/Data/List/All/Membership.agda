open import Relation.Unary using (Pred)

module Data.List.All.Membership {a p} {A : Set a} {P : Pred A p} where

  open import Data.List
  open import Data.List.All
  open import Data.List.Any
  open import Data.List.Membership.Propositional

  open import Function
  open import Function.Equivalence.PropositionalEquality

  open import Relation.Binary.PropositionalEquality

  All-∈→ : ∀ {xs} → All P xs → ∀ {x} → x ∈ xs → P x
  All-∈→ (px ∷ pxs) (here refl) = px
  All-∈→ (px ∷ pxs) (there x∈xs) = All-∈→ pxs x∈xs

  ∈→-All : ∀ {xs} → (∀ {x} → x ∈ xs → P x) → All P xs
  ∈→-All {[]} f = []
  ∈→-All {x ∷ xs} f = f (here refl) ∷ ∈→-All (f ∘ there)

  All⇔∈→ : ∀ {xs} → All P xs ⇔ (∀ {x} → x ∈ xs → P x)
  All⇔∈→ = mk-⇔ All-∈→ ∈→-All
