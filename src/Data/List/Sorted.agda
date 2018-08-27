module Data.List.Sorted where

  open import Data.List
  open import Data.List.All as All renaming (all to All?)
  open import Data.List.All.Properties
  open import Data.List.Any as Any
  --open import Data.List.Any.Membership
  import Data.List.Membership.Setoid as MemS
  open import Data.List.Membership.Setoid.Properties
  open import Data.List.Properties
  open import Data.List.Relation.Sublist.Propositional.Properties
  open import Data.Product

  open import Function
  open import Function.Equality hiding (id; _∘_)
  open import Function.Equivalence hiding (id; _∘_; sym)
  open import Function.Equivalence.PropositionalEquality

  open import Level

  open import Relation.Binary
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary as U using (Pred)

  module _ {a} {A : Set a} where

    data SortedBy {ℓ} (_∼_ : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
      [] : SortedBy _∼_ []
      _∷_ : ∀ {x xs} (sx : All (x ∼_) xs) (sxs : SortedBy _∼_ xs) →
            SortedBy _∼_ (x ∷ xs)

    nub-by : ∀ {r} {R : Rel A r} (R? : Decidable R) → List A → List A
    nub-by R? [] = []
    nub-by R? (x ∷ xs) = x ∷ filter (R? x) (nub-by R? xs)

    module _ {ℓ} {_∼_ : Rel A ℓ} where

      module _ {p} {P : Pred A p} (P? : U.Decidable P) where

        filter-Sorted : ∀ {xs} → SortedBy _∼_ xs → SortedBy _∼_ (filter P? xs)
        filter-Sorted {[]} [] = []
        filter-Sorted {x ∷ xs} (sx ∷ sxs) with P? x
        ... | no _ = filter-Sorted sxs
        ... | yes _ = anti-mono (filter⁺ P? xs) sx ∷ filter-Sorted sxs

      nub-Sorted : (_∼?_ : Decidable _∼_) → ∀ xs → SortedBy _∼_ (nub-by _∼?_ xs)
      nub-Sorted _∼?_ [] = []
      nub-Sorted _∼?_ (x ∷ xs) =
        filter⁺₁ (x ∼?_) (nub-by _∼?_ xs)
        ∷ filter-Sorted (x ∼?_) (nub-Sorted _∼?_ xs)

      SortedBy? : (_∼?_ : Decidable _∼_) → U.Decidable (SortedBy _∼_)
      SortedBy? _∼?_ [] = yes []
      SortedBy? _∼?_ (x ∷ xs) with All? (x ∼?_) xs
      ... | yes sx with SortedBy? _∼?_ xs
      ... | yes sxs = yes (sx ∷ sxs)
      ... | no ¬sxs = no (λ { (sx ∷ sxs) → ¬sxs sxs })
      SortedBy? _∼?_ (x ∷ xs)
          | no ¬sx = no (λ { (sx ∷ sxs) → ¬sx sx })

  module _ {c ℓ} (DS : DecSetoid c ℓ) where
    private
      open module DS = DecSetoid DS
    open MemS DS.setoid

    private
      _≠?_ = λ x y → ¬? (x ≟ y)

    nub-by-∈⇔ : ∀ {x xs} → x ∈ xs ⇔ x ∈ nub-by _≠?_ xs
    nub-by-∈⇔ {x} = mk-⇔ (to _) (from _)
      where
      resp : ∀ {y} → (¬_ ∘ (y ≈_)) Respects _≈_
      resp ij ¬yi yj = ¬yi (trans yj (sym ij))

      to : ∀ ys → x ∈ ys → x ∈ nub-by _≠?_ ys
      to (y ∷ ys) (here xy) = here xy
      to (y ∷ ys) (there x∈ys) with x ≟ y
      ... | yes xy = here xy
      ... | no ¬xy =
        there (∈-filter⁺ DS.setoid (y ≠?_) resp (to ys x∈ys) (¬xy ∘ sym))

      from : ∀ ys → x ∈ nub-by _≠?_ ys → x ∈ ys
      from [] ()
      from (y ∷ ys) (here xy) = here xy
      from (y ∷ ys) (there x∈nub) =
        there (from ys (proj₁ (∈-filter⁻ DS.setoid (y ≠?_) resp x∈nub)))
