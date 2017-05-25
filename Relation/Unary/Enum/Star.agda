open import Relation.Binary

module Relation.Unary.Enum.Star {a t} {A : Set a} {T : Rel A t} where

  open import Data.List as List hiding (any)
  open import Data.List.Any as Any
  open Membership-≡
  open import Data.List.Any.Properties as AnyP
  open import Data.Maybe as Maybe
  open import Data.Nat
  open import Data.Product as Σ
  open import Data.Star
  open import Data.Star.Rats
  open import Data.Sum

  open import Function
  open import Function.Inverse.PropositionalEquality

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Type

  Rats-enum : Decidable (_≡_ {A = A}) →
              Enum-type A → (∀ a → Enum (T a)) → ∀ a → Enum (Rats T a)
  Rats-enum _≟_ ae te a = record
    { list = proj₁ go-terminates
    ; consistent = {!!}
    ; complete = {!!}
    }
    where
    module A = Enum ae
    module T a = Enum (te a)

    go : ℕ → List A → List A → Maybe (List A)
    go t hs [] = just hs
    go t hs (q ∷ qs) with any (q ≟_) hs
    go t hs (q ∷ qs) | yes p = go t hs qs
    go zero hs (q ∷ qs) | no ¬p = nothing
    go (suc t) hs (q ∷ qs) | no ¬p = go t (q ∷ hs) (T.list q ++ qs)

    go-terminates : ∃ λ l → just l ≡ go (length A.list) [] (a ∷ [])
    go-terminates = {!!}

    go-consistent : ∀ t hs qs →
                    Consistent (Rats T a) hs → Consistent (Rats T a) qs →
                    Maybe.All (Consistent (Rats T a)) (go t hs qs)
    go-consistent t hs [] chs cqs = just chs
    go-consistent t hs (q ∷ qs) chs cqs with any (q ≟_) hs
    go-consistent t hs (q ∷ qs) chs cqs | yes p =
      go-consistent t hs qs chs (cqs ∘ there)
    go-consistent zero hs (q ∷ qs) chs cqs | no ¬p = nothing
    go-consistent (suc t) hs (q ∷ qs) chs cqs | no ¬p =
      go-consistent t (q ∷ hs) (T.list q ++ qs) chs′ cqs′
      where
      chs′ : Consistent (Rats T a) (q ∷ hs)
      chs′ (here refl) = cqs (here refl)
      chs′ (there h∈) = chs h∈

      open module Dummy {a p} {A : Set a} {P : A → Set p} {xs ys} =
        ↔ (++↔ {a} {p} {A} {P} {xs} {ys})

      cqs′ : Consistent (Rats T a) (T.list q ++ qs)
      cqs′ r∈ with from {xs = T.list q} {qs} r∈
      cqs′ r∈ | inj₁ r∈T = T.consistent q r∈T ◅ cqs (here refl)
      cqs′ r∈ | inj₂ r∈qs = cqs (there r∈qs)

    --go-complete
