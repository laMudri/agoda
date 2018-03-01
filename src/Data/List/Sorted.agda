module Data.List.Sorted {a} {A : Set a} where

  open import Data.Bool
  open import Data.List
  open import Data.List.All as All renaming (all to All?)
  open import Data.List.All.Properties
  open import Data.List.Any as Any
  --open import Data.List.Any.Membership
  open import Data.List.Any.Membership.Propositional
  open import Data.List.Any.Membership.Propositional.Properties
  open import Data.List.Properties

  open import Function
  open import Function.Equality hiding (id; _∘_)
  open import Function.Equivalence hiding (id; _∘_)
  open import Function.Equivalence.PropositionalEquality

  open import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary as U using (Pred)

  data SortedBy {ℓ} (_∼_ : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
    [] : SortedBy _∼_ []
    _∷_ : ∀ {x xs} (sx : All (x ∼_) xs) (sxs : SortedBy _∼_ xs) →
          SortedBy _∼_ (x ∷ xs)

  filter-Sorted : ∀ {ℓ} {_∼_ : Rel A ℓ} → ∀ p {xs} →
                  SortedBy _∼_ xs → SortedBy _∼_ (filter p xs)
  filter-Sorted {ℓ} {_∼_} p {[]} [] = []
  filter-Sorted {ℓ} {_∼_} p {x ∷ xs} (sx ∷ sxs) with p x
  ... | false = filter-Sorted p sxs
  ... | true = anti-mono (filter-⊆ p xs) sx ∷ filter-Sorted p sxs

  nub-by : (A → A → Bool) → List A → List A
  nub-by p [] = []
  nub-by p (x ∷ xs) = x ∷ filter (p x) (nub-by p xs)

  nub-Sorted :
    ∀ {ℓ} {_∼_ : Rel A ℓ} (_∼?_ : Decidable _∼_) →
    ∀ xs → SortedBy _∼_ (nub-by (λ x y → ⌊ x ∼? y ⌋) xs)
  nub-Sorted _∼?_ [] = []
  nub-Sorted {_∼_ = _∼_} _∼?_ (x ∷ xs) =
    filter-filters (x ∼_) (x ∼?_) (nub-by (λ y z → ⌊ y ∼? z ⌋) xs)
    ∷ filter-Sorted (⌊_⌋ ∘ (x ∼?_)) (nub-Sorted _∼?_ xs)

  SortedBy? :
    ∀ {ℓ} {_∼_ : Rel A ℓ} (_∼?_ : Decidable _∼_) → U.Decidable (SortedBy _∼_)
  SortedBy? _∼?_ [] = yes []
  SortedBy? _∼?_ (x ∷ xs) with All? (x ∼?_) xs
  ... | yes sx with SortedBy? _∼?_ xs
  ... | yes sxs = yes (sx ∷ sxs)
  ... | no ¬sxs = no (λ { (sx ∷ sxs) → ¬sxs sxs })
  SortedBy? _∼?_ (x ∷ xs)
      | no ¬sx = no (λ { (sx ∷ sxs) → ¬sx sx })

  nub-by-∈⇔ :
    ∀ {x xs} (_≟_ : Decidable _≡_) →
    x ∈ xs ⇔ x ∈ nub-by (λ x y → ⌊ ¬? (x ≟ y) ⌋) xs
  nub-by-∈⇔ {x} _≟_ = mk-⇔ (to _) (from _)
    where
    p = λ x y → ⌊ ¬? (x ≟ y) ⌋

    to : ∀ ys → x ∈ ys → x ∈ nub-by p ys
    to (y ∷ ys) (here px) = here px
    to (y ∷ ys) (there x∈ys)
      with y ≟ x
         | filter-∈ (λ z → ⌊ ¬? (y ≟ z) ⌋) (nub-by p ys) {x} (to ys x∈ys)
    ... | yes refl | _ = here refl
    ... | no np | r = there (r refl)

    from : ∀ ys → x ∈ nub-by p ys → x ∈ ys
    from [] ()
    from (y ∷ ys) (here px) = here px
    from (y ∷ ys) (there x∈nub) =
      there (from ys (filter-⊆ (p y) (nub-by p ys) x∈nub))
