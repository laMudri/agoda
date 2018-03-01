module Igo.Board where
  open import Data.Bool using (Bool; true; false; _∧_; _∨_)
  open import Data.Fin as F using (Fin; zero; suc; toℕ; fromℕ≤; inject≤; inject+)
  open import Data.Fin.Enum
  open import Data.Fin.Properties as FP using (bounded)
  open import Data.Graph
  open import Data.Integer as ℤ using (ℤ; _⊖_; ∣_∣)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_; _≤_; _<_)
  open import Data.Nat.Properties
    using (module ≤-Reasoning; +-suc; +-mono-≤; ≤-refl; pred-mono)
  open ≤-Reasoning
  open import Data.Product

  open import Function

  open import Igo.Core

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  infixl 6 _+′_
  _+′_ : ∀ {m n} → Fin (suc m) → Fin n → Fin (m + n)
  i +′ j = inject≤ (i F.+ j) (pred-mono (bounded i) ⟨ +-mono-≤ ⟩ ≤-refl)

  infixl 7 _ℕ*F_
  _ℕ*F_ : ∀ {m} n → Fin (suc m) → Fin (suc (n * m))
  zero ℕ*F i = zero
  _ℕ*F_ {m} (suc n) i = subst Fin (+-suc m (n * m)) (i +′ n ℕ*F i)
  --_ℕ*F_ {m} (suc n) i = inject≤ (i F.+ n ℕ*F i) (begin
  --  toℕ i + suc (n * m)  ≡⟨ +-suc (toℕ i) (n * m) ⟩
  --  suc (toℕ i) + n * m  ≤⟨ bounded i ⟨ +-mono-≤ ⟩ ≤-refl ⟩
  --  suc m + (n * m)      ∎)

  encodePosition : ∀ {n} → Position (suc n) → Fin (n + suc (n * n))
  encodePosition {n} (x , y) = x +′ (n ℕ*F y)

  decodePosition : ∀ {n} → Fin (n + suc (n * n)) → Position (suc n)
  decodePosition i = {!!}

  touching : ∀ {n} → (p q : Position n) → Bool
  touching (px , py) (qx , qy) =
    (⌊ x ≟ 1 ⌋ ∧ ⌊ y ≟ 0 ⌋) ∨ (⌊ x ≟ 0 ⌋ ∧ ⌊ y ≟ 1 ⌋)
    where
    x = ∣ toℕ px ⊖ toℕ qx ∣
    y = ∣ toℕ py ⊖ toℕ qy ∣

  --graph : ∀ {n} → Graph (n + suc (n * n))
  --graph {n} u v = touching {n} (decodePosition u) (decodePosition v)
