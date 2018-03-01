open import Relation.Binary

module Function.Update {c ℓ} (DS : DecSetoid c ℓ) where

  open DecSetoid DS renaming (Carrier to C)

  open import Function

  open import Relation.Nullary

  _⟨_⟩≔_ : ∀ {a} {A : Set a} → (C → A) → C → A → (C → A)
  (f ⟨ c ⟩≔ a) c′ with c ≟ c′
  ... | yes p = a
  ... | no ¬p = f c′
