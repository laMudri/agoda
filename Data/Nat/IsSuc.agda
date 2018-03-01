module Data.Nat.IsSuc where

  open import Data.Nat

  data Is-suc : ℕ → Set where
    is-suc : ∀ n → Is-suc (suc n)
