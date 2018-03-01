module Data.Fin.Encode where
  open import Data.Fin as F using (Fin; zero; suc; toℕ; fromℕ≤)
  open import Data.Fin.Properties as FP using (_+′_; bounded; toℕ-injective)
  open import Data.Nat as N
  open import Data.Nat.DivMod
  open import Data.Nat.Properties as NP
  open import Data.Product

  open import Function
  open import Function.Inverse
  open import Function.Inverse.PropositionalEquality

  open import Relation.Binary.PropositionalEquality as ≡

  infixl 7 _ℕ*F_ _F*ℕ_
  _ℕ*F_ : ∀ {m} n → Fin (suc m) → Fin (suc (n * m))
  zero ℕ*F i = zero
  _ℕ*F_ {m} (suc n) i = subst Fin (+-suc m (n * m)) (i +′ n ℕ*F i)

  *-cancelˡ-≤ : ∀ {i j} k → suc k * i ≤ suc k * j → i ≤ j
  *-cancelˡ-≤ {i} {j} k le = *-cancelʳ-≤ i j k (begin
    i * suc k  ≡⟨ *-comm i (suc k) ⟩
    suc k * i  ≤⟨ le ⟩
    suc k * j  ≡⟨ *-comm (suc k) j ⟩
    j * suc k  ∎)
    where
    open ≤-Reasoning

  *-cancelʳ-< : ∀ i j k → i * suc k < j * suc k → i < j
  *-cancelʳ-< zero zero k ()
  *-cancelʳ-< zero (suc j) k lt = s≤s z≤n
  *-cancelʳ-< (suc i) zero k ()
  *-cancelʳ-< (suc i) (suc j) k (s≤s lt) =
    s≤s (*-cancelʳ-< i j k (+-cancelˡ-≤ k (begin
      k + suc (i * suc k)  ≡⟨ +-suc k (i * suc k) ⟩
      suc (k + i * suc k)  ≤⟨ lt ⟩
      k + j * suc k        ∎)))
    where
    open ≤-Reasoning

  toℕ-subst : ∀ {m n} (eq : m ≡ n) i → toℕ (subst Fin eq i) ≡ toℕ i
  toℕ-subst refl i = refl

  ×↔ : ∀ {m n} → (Fin m × Fin n) ↔ Fin (m * n)
  ×↔ {zero} {n} = {!!}
  ×↔ {suc m} {zero} = {!!}
  ×↔ {suc m} {suc n} = mk-↔ to from from-to to-from
    where
    to : Fin (suc m) × Fin (suc n) → Fin (suc (n + m * suc n))
    to (i , j) =
      subst Fin eq (i +′ suc m ℕ*F j)
      module To where
      open ≡-Reasoning

      eq = begin
        m + suc (n + m * n)    ≡⟨ +-suc m _ ⟩
        suc (m + (n + m * n))  ≡⟨ cong suc (begin
          m + (n + m * n)  ≡⟨ ≡.sym (+-assoc m n (m * n)) ⟩
          (m + n) + m * n  ≡⟨ cong (_+ m * n) (+-comm m n) ⟩
          (n + m) + m * n  ≡⟨ +-assoc n m (m * n) ⟩
          n + (m + m * n)  ≡⟨ cong (n +_) (≡.sym (+-*-suc m n)) ⟩
          n + m * suc n    ∎) ⟩
        suc (n + m * suc n)    ∎

    from : Fin (suc (n + m * suc n)) → Fin (suc m) × Fin (suc n)
    from i with toℕ i divMod suc m
    ... | record { quotient = q ; remainder = r ; property = p } =
      r , fromℕ≤ {q} lt
      module From where
      open ≤-Reasoning

      lt = (*-cancelʳ-< q (suc n) m (begin
        suc (q * suc m)          ≤⟨ s≤s (z≤n {toℕ r} ⟨ +-mono-≤ ⟩ ≤-refl) ⟩
        suc (toℕ r + q * suc m)  ≡⟨ cong suc (≡.sym p) ⟩
        suc (toℕ i)              ≤⟨ bounded i ⟩
        suc m * suc n            ≡⟨ *-comm (suc m) (suc n) ⟩
        suc n * suc m            ∎))

    from-to : ∀ ij → from (to ij) ≡ ij
    from-to (i , j) =
      let record { quotient = q ; remainder = r ; property = p } =
           toℕ k divMod suc m in
      {!lt q r p!}
      where
      open To i j
      k = subst Fin eq (i +′ suc m ℕ*F j)
      open From k

    to-from : ∀ i → to (from i) ≡ i
    to-from i with toℕ i divMod suc m
    ... | record { quotient = q ; remainder = r ; property = p } =
      toℕ-injective (begin
        toℕ (subst Fin eq (_ +′ suc m ℕ*F fromℕ≤ lt))  ≡⟨ toℕ-subst eq _ ⟩
        toℕ (_ +′ suc m ℕ*F fromℕ≤ lt)  ≡⟨ {!!} ⟩
        toℕ i  ∎) --(≡.trans (toℕ-subst eq _) {!!})
      where
      open From i q r p
      open To r (fromℕ≤ lt)
      open ≡-Reasoning
