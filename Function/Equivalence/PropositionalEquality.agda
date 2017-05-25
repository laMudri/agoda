module Function.Equivalence.PropositionalEquality where
  import Function.Equivalence as E
  open E public using (_⇔_)
  open E hiding (_⇔_)

  open import Function.Equality

  open import Relation.Binary.PropositionalEquality

  module _ {f t} {From : Set f} {To : Set t} where
    module ⇔ (equiv : From ⇔ To) where
      open Equivalence equiv renaming (to to to′; from to from′)
      to = to′ ⟨$⟩_
      from = from′ ⟨$⟩_

    mk-⇔ : (From → To) → (To → From) → From ⇔ To
    mk-⇔ to from = record { to = →-to-⟶ to ; from = →-to-⟶ from }
