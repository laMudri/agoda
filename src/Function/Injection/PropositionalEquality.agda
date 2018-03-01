module Function.Injection.PropositionalEquality where
  import Function.Injection as I
  open I public using (_↣_)
  open I hiding (_↣_)

  open import Function.Equality

  open import Relation.Binary.PropositionalEquality

  module _ {f t} {From : Set f} {To : Set t} where

    module ↣ (inv : From ↣ To) where
      open Injection inv using () renaming (to to to′)
      open Injection inv public using (injective)
      to = to′ ⟨$⟩_

    mk-↣ : (f : From → To) → (∀ {x y} → f x ≡ f y → x ≡ y) → From ↣ To
    mk-↣ to injective = record
      { to = →-to-⟶ to
      ; injective = injective
      }
