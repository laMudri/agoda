module Function.Inverse.PropositionalEquality where
  import Function.Inverse as I
  open I public using (_↔_)
  open I hiding (_↔_)

  open import Function.Equality

  open import Relation.Binary.PropositionalEquality

  module _ {f t} {From : Set f} {To : Set t} where

    module ↔ (inv : From ↔ To) where
      open Inverse inv using () renaming (to to to′; from to from′)
      open Inverse inv public using (right-inverse-of; left-inverse-of)
      to = to′ ⟨$⟩_
      from = from′ ⟨$⟩_

    mk-↔ : (to : From → To) (from : To → From) →
           (∀ x → from (to x) ≡ x) → (∀ y → to (from y) ≡ y) → From ↔ To
    mk-↔ to from left-inverse-of right-inverse-of = record
      { to = →-to-⟶ to
      ; from = →-to-⟶ from
      ; inverse-of = record
        { left-inverse-of = left-inverse-of
        ; right-inverse-of = right-inverse-of
        }
      }
