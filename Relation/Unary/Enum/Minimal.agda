open import Function.Equivalence hiding (id; _∘_)
open import Function.Equivalence.PropositionalEquality
open import Relation.Binary as B
open import Relation.Unary as U using (Pred)

module Relation.Unary.Enum.Minimal {a p A} (P : Pred {a} A p) where
  open import Data.Bool
  open import Data.Fin
  open import Data.List
  open import Data.List.Any
  open import Data.List.Any.Membership.Propositional
  open import Data.List.Extras
  open import Data.List.Sorted
  open import Data.Nat
  open import Data.Product

  open import Function
  open import Function.Inverse hiding (id; _∘_)
  open import Function.Inverse.PropositionalEquality

  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Binary.Subsetoid (≡.setoid A)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary.Enum

  open import Data.List.Distinct (≡.setoid A)
  open import Data.List.Distinct.PropositionalEquality using (∈≡)

  Minimal : Enum P → Set _
  Minimal e = Distinct (Enum.list e)

  module _ e (min : Minimal e) where
    open Enum e
    open ≡-Reasoning

    complete-consistent : ∀ {x} (x∈ : x ∈ list) → complete (consistent x∈) ≡ x∈
    complete-consistent x∈ = ∈≡ min (complete (consistent x∈)) x∈

    complete-≡ : ∀ {x} (px px′ : P x) → complete px ≡ complete px′
    complete-≡ px px′ = ∈≡ min (complete px) (complete px′)

    MinimalEnum↔Fin :
      Subsetoid P ⟨ Inverse ⟩ ≡.setoid (Fin (length (Enum.list e)))
    MinimalEnum↔Fin = record
      { to = outofSub (λ _ → index ∘ complete)
                      (λ { refl px py → cong index (complete-≡ px py) })
      ; from = intoSub (→-to-⟶ (lookup-by-Fin list))
                       (consistent ∘ lookup-by-Fin-∈ list)
      ; inverse-of = record
        { left-inverse-of = λ { (a , p) → lookup-by-Fin-index (complete p) }
        ; right-inverse-of = λ i → begin
          index (complete (consistent (lookup-by-Fin-∈ list i)))
            ≡⟨ cong index (complete-consistent (lookup-by-Fin-∈ list i)) ⟩
          index (lookup-by-Fin-∈ list i)
            ≡⟨ index-lookup-by-Fin-∈ list i ⟩
          i
            ∎
        }
      }

  module _ (_≟_ : B.Decidable (_≡_ {A = A})) where
    minimise : Enum P → Enum P
    minimise e = record
      { list = list′
      ; consistent = consistent ∘ from
      ; complete = to ∘ complete
      }
      where
      open Enum e
      open module Dummy {x} = ⇔ (nub-by-∈⇔ {x = x} {list} _≟_)
      list′ = nub-by (λ x y → ⌊ ¬? (x ≟ y) ⌋) list

    minimise-minimal : ∀ e → Minimal (minimise e)
    minimise-minimal e = nub-by-distinct (Enum.list e)
      where
      open Decidable _≟_
