open import Relation.Binary

module Data.PriorityQueue
       {k ℓ₁ ℓ₂ v} (DTO : DecTotalOrder k ℓ₁ ℓ₂) (V : Set v) where

  open DecTotalOrder DTO renaming (Carrier to K)

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Nat.IsSuc
  open import Data.Product

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  record PriorityQueue {q} i (Q : Set q)
                       : Set (k ⊔ ℓ₁ ⊔ ℓ₂ ⊔ v ⊔ q ⊔ lsuc i) where
    field
      size : Q → ℕ
      insert : K → V → Q → Q
      extract : ∀ q → Is-suc (size q) → (K × V) × Q
      _K∈_ : K → Q → Set i
      _V∈_ : V → Q → Set i

      K∈-insert : ∀ k v q → k K∈ insert k v q
      K∈-extract : ∀ q s → let (k , v) , q′ = extract q s in k K∈ q
      K∉-extract : ∀ q s → let (k , v) , q′ = extract q s in ¬ k K∈ q′

      V∈-insert : ∀ k v q → v V∈ insert k v q
      V∈-extract : ∀ q s → let (k , v) , q′ = extract q s in v V∈ q
      V∉-extract : ∀ q s → let (k , v) , q′ = extract q s in ¬ v V∈ q′

      insert-resp-K∈ : ∀ k v q {k′} → k′ K∈ q → k′ K∈ insert k v q
      extract-resp-K∈ : ∀ q s → let (k , v) , q′ = extract q s in
                        ∀ k′ → ¬ k ≈ k′ → k′ K∈ q → k′ K∈ q′

      size-insert : ∀ k v q → ¬ k K∈ q → size (insert k v q) ≡ suc (size q)
      size-extract : ∀ q s → let _ , q′ = extract q s in suc (size q′) ≡ size q

      ≤-extract : ∀ q s → let (k , v) , q′ = extract q s in
                  ∀ {k′} → k′ K∈ q′ → k ≤ k′
