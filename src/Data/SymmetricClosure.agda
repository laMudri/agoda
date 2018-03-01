module Data.SymmetricClosure where

  open import Data.Sum

  open import Relation.Binary hiding (Sym)

  Sym : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Rel A ℓ
  Sym _∼_ x y = (x ∼ y) ⊎ (y ∼ x)
