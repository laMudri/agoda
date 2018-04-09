open import Relation.Binary

module Data.List.Distinct {c ℓ} (S : Setoid c ℓ) where
  open Setoid S renaming (Carrier to C)

  open import Data.Bool
  open import Data.List hiding (any)
  open import Data.List.All as All
  open import Data.List.All.Properties as AllP using (anti-mono)
  open import Data.List.Any as Any
  open import Data.List.Any.Membership S
  open import Data.List.Any.Properties
  open import Data.List.Properties
  open import Data.List.Sorted {A = C}
  open import Data.Product
  open import Data.Sum as ⊎

  open import Function
  --open import Function.Equality using (_⟨$⟩_; cong)
  open import Function.Equivalence using (Equivalence; _⇔_)
  open import Function.Equivalence.PropositionalEquality
  open import Function.Inverse using (Inverse; _↔_)
  open import Function.Inverse.PropositionalEquality

  open import Level

  open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary as U hiding (_∈_; _∉_; Decidable)

  _≉_ = λ x y → ¬ x ≈ y

  Distinct = SortedBy _≉_

  head-distinct : ∀ {x xs} → Distinct (x ∷ xs) → All (x ≉_) xs
  head-distinct (dx ∷ _) = dx

  tail-distinct : ∀ {x xs} → Distinct (x ∷ xs) → Distinct xs
  tail-distinct (_ ∷ dxs) = dxs

  insert-∈ : ∀ {x y ys} xs → x ∈ xs ++ ys → x ∈ xs ++ y ∷ ys
  insert-∈ [] elem = there elem
  insert-∈ (x ∷ xs) (here px) = here px
  insert-∈ (x ∷ xs) (there elem) = there (insert-∈ xs elem)

  remove-distinct : ∀ {y ys} xs → Distinct (xs ++ y ∷ ys) → Distinct (xs ++ ys)
  remove-distinct [] dxs = tail-distinct dxs
  remove-distinct {y} {ys} (x ∷ xs) (dx ∷ dxs) =
    anti-mono (λ {z} z∈xsys → to {z} {xs} {y ∷ ys} (⊎.map id (there {x = y}) (from z∈xsys))) dx SortedBy.∷ remove-distinct xs dxs
    where
    open module Dummy {z : C} {as bs} = ↔ (++↔ {P = z ≡_} {xs = as} {bs})

  {-+}
  pull-distinct : ∀ {y ys} xs →
                     Distinct (xs ++ y ∷ ys) → Distinct (y ∷ xs ++ ys)
  pull-distinct [] dxs = dxs
  pull-distinct {y} {ys} (x ∷ xs) (dx ∷ dxs) with pull-distinct xs dxs
  ... | dy ∷ dys = {!!} --dy′ ∷ (λ z∈ → dx (insert-∈ xs z∈)) ∷ dys
    where
    open ↔ (++↔ {xs = xs} {y ∷ ys})

    dy′ : ∀ {z} → z ∈ x ∷ xs ++ ys → ¬ y ≈ z
    dy′ (here z≈x) y≈z = {!!} --dx (to (inj₂ (here refl))) (sym (trans y≈z z≈x))
    dy′ (there z∈) = {!!} --dy z∈
  {+-}

  ++-distinct : ∀ {xs ys} → (∀ {x} → x ∈ xs → x ∉ ys) →
                Distinct xs → Distinct ys → Distinct (xs ++ ys)
  ++-distinct {.[]} {ys} apart [] dys = dys
  ++-distinct {.(_ ∷ _)} {ys} apart (dx ∷ dxs) dys =
    to (dx , All.tabulate
               λ {x} x∈ys xq →
                 apart (here refl) (Any.map (λ { PEq.refl → xq }) x∈ys))
    ∷ ++-distinct (apart ∘ there) dxs dys
    where
    open ↔ AllP.++↔

  module Decidable (_≟_ : Decidable _≈_) where

    infixr 5 _∷∉_ --_++∉_

    _∷∉_ : C → List C → List C
    x ∷∉ xs with any (x ≟_) xs
    ... | yes p = xs
    ... | no ¬p = x ∷ xs

    nub-by-distinct : ∀ xs → Distinct (nub-by (λ x y → ⌊ ¬? (x ≟ y) ⌋) xs)
    nub-by-distinct [] = []
    nub-by-distinct (x ∷ xs) =
      filter-filters (x ≉_) (¬? ∘ x ≟_) (nub-by (λ x y → ⌊ ¬? (x ≟ y) ⌋) xs)
      ∷ filter-Sorted (⌊_⌋ ∘ ¬? ∘ x ≟_) (nub-by-distinct xs)

    {-+}
    ∷∉-distinct : ∀ x {xs} → Distinct xs → Distinct (x ∷∉ xs)
    ∷∉-distinct x {xs} dxs with any (x ≟_) xs
    ... | yes p = dxs
    ... | no ¬p = {!!} --(λ y∈xs x≈y → ¬p (Any.map (trans x≈y) y∈xs)) ∷ dxs

    _++∉_ : List C → List C → List C
    [] ++∉ ys = ys
    (x ∷ xs) ++∉ ys = x ∷∉ xs ++∉ ys

    ++∉-distinct : ∀ xs {ys} → Distinct ys → Distinct (xs ++∉ ys)
    ++∉-distinct [] dys = dys
    ++∉-distinct (x ∷ xs) {ys} dys with any (x ≟_) (xs ++∉ ys)
    ... | yes p = ++∉-distinct xs dys
    ... | no ¬p =
      {!!} --(λ y∈ x≈y → ¬p (Any.map (trans x≈y) y∈)) ∷ ++∉-distinct xs dys
    {+-}
