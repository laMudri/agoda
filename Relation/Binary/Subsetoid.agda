open import Relation.Binary

module Relation.Binary.Subsetoid {c l} (S : Setoid c l) where
  open Setoid S

  open import Data.Product
  open import Data.Unit

  open import Function as F hiding (id; _∘_; const)
  open import Function.Equality as E hiding (id; _∘_; const)
  open import Function.Inverse as I hiding (id; _∘_; sym)

  open import Level

  open import Relation.Unary

  Subsetoid : ∀ {p} → (Carrier → Set p) → Setoid (c ⊔ p) l
  Subsetoid P = record
    { Carrier = ∃ P
    ; _≈_ = _≈_ on proj₁
    ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    }

  -- Meant for S ∣ P notation
  _∣_ = Subsetoid

  intoSub : ∀ {p c′ l′} {P : Carrier → Set p} {S′ : Setoid c′ l′} →
            (f : S′ ⟶ S) → ((x : Setoid.Carrier S′) → P (f ⟨$⟩ x)) →
            S′ ⟶ Subsetoid P
  intoSub f g = record
    { _⟨$⟩_ = λ x → f ⟨$⟩ x , g x
    ; cong = cong f
    }

  outofSub : ∀ {p c′ l′} {P : Carrier → Set p} {S′ : Setoid c′ l′} →
             (f : ∀ x → P x → Setoid.Carrier S′) →
             (∀ {x y} → x ≈ y → (px : P x) (py : P y) →
               Setoid._≈_ S′ (f x px) (f y py)) →
             Subsetoid P ⟶ S′
  outofSub f g = record
    { _⟨$⟩_ = uncurry f
    ; cong = λ { {x , px} {y , py} xy → g xy px py }
    }

  ↔∣U : S ⟨ Inverse ⟩ Subsetoid U
  ↔∣U = record
    { to = intoSub E.id (λ _ → tt)
    ; from = outofSub F.const (λ eq _ _ → eq)
    ; inverse-of = record
      { left-inverse-of = λ x → refl {x}
      ; right-inverse-of = λ x → refl
      }
    }
