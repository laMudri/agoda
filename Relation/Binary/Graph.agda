open import Relation.Binary

module Relation.Binary.Graph {v e} {V : Set v} (E : Rel V e) where

  open import Data.Empty
  open import Data.List hiding (any)
  open import Data.List.All
  open import Data.List.All.Membership
  open import Data.List.Any
  open Membership-≡
  open import Data.List.Any.Properties
  open import Data.List.Properties
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.Properties
  open import Data.Nat.Properties.Simple
  open import Data.Product
  open import Data.Star as Star
  open import Data.Star.Rats
  open import Data.Sum

  open import Function
  open import Function.Inverse.PropositionalEquality

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Type

  open import Data.List.Distinct (PEq.setoid V)

  record Finite : Set (v ⊔ e) where
    field
      vertex-enum : Enum-type V
      edge-enum : ∀ v → Enum (E v)

    module V = Enum-type vertex-enum
    module E v = Enum (edge-enum v)

  connected-component :
    Finite → Decidable (_≡_ {A = V}) → ∀ v → Enum (Rats E v)
  connected-component f _≟v_ v = {!!}
    where
    open Finite f
    open Decidable _≟v_

    go : ∀ t (hs : List V) (qs : List V) →
         t + length hs ≤ length V.list →
         Distinct (hs ++ qs) →
         Consistent (Rats E v) hs →
         Consistent (Rats E v) qs →
         Complete (Rats (λ w h → E w h × h ∉ qs) v) hs →
         Complete (λ q → (∃ λ h → h ∈ hs × E h q) × q ∉ hs) qs →
         Enum (Rats E v)
    go t hs [] leq ds shs sqs phs pqs = record
      { list = hs
      ; consistent = shs
      ; complete = complete
      }
      where
      complete : Complete (Rats E v) hs
      complete {w} E*vw = phs {w} (Star.map (_, (λ ())) E*vw)
    go zero hs (q ∷ qs) leq ds shs sqs phs pqs = ⊥-elim {!!}
    go (suc t) hs (q ∷ qs) leq ds shs sqs phs pqs =
      go t (q ∷∉ hs) qs′ leq′ ds′ shs′ sqs′ {!!} {!!}
      where
      dec = λ w → ¬? (any (w ≟v_) (q ∷ hs))
      qs′ = filter (⌊_⌋ ∘ dec) (E.list q) ++∉ qs

      leq′ : t + length (q ∷∉ hs) ≤ length V.list
      leq′ with any (q ≟v_) hs
      leq′ | yes p = ≤⇒pred≤ _ _ leq
      leq′ | no ¬p = begin
        t + suc (length hs)  ≡⟨ +-suc t (length hs) ⟩
        suc (t + length hs)  ≤⟨ leq ⟩
        length V.list        ∎
        where open ≤-Reasoning

      open module Dummy {r xs ys} = ↔ (++↔ {A = V} {P = r ≡_} {xs} {ys})

      ds′ : Distinct ((q ∷∉ hs) ++ qs′)
      ds′ with any (q ≟v_) hs
      ds′ | yes q∈hs =
        ⊥-elim (head-distinct (pull-distinct hs ds) (to (inj₁ q∈hs)))
      ds′ | no q∉hs = (λ { q∈ refl → q∉ q∈ }) ∷ {!!}
        where
        q∉ : q ∉ hs ++ qs′
        q∉ q∈ with from {xs = hs} q∈
        q∉ q∈ | inj₁ q∈hs = q∉hs q∈hs
        q∉ q∈ | inj₂ q∈qs′ = {!!}
          where
          q∉list : q ∉ filter (⌊_⌋ ∘ dec) (E.list q)
          q∉list q∈list =
            All-∈→ (filter-filters (λ w → w ∉ q ∷ hs) dec (E.list q))
                   q∈list
                   (here refl)

          q∉qs : q ∉ qs
          q∉qs = head-distinct (pull-distinct hs ds) ∘ to {xs = hs} ∘ inj₂

      shs′ : Consistent (Rats E v) (q ∷∉ hs)
      shs′ w∈ with any (q ≟v_) hs
      shs′ w∈ | yes p = shs w∈
      shs′ (here px) | no ¬p = sqs (here px)
      shs′ (there w∈) | no ¬p = shs w∈

      sqs′ : Consistent (Rats E v) qs′
      sqs′ w∈ = {!!}
      --sqs′ {r} r∈qs′ with from r∈qs′
      --... | inj₁ r∈list = E.consistent q r∈list ◅ sqs (here refl)
      --... | inj₂ r∈qs = sqs (there r∈qs)

      --pqs′ :
      --  Complete (λ r → (∃ λ h → h ∈ (q ∷ hs) × E h r) × r ∉ (q ∷ hs)) qs′
      --pqs′ {r} ((h , h∈qhs , Ehr), r∉qhs) with pqs {r} {!!}
      --... | here px = ⊥-elim (r∉qhs (here px))
      --... | there r∈qs = to {xs = E.list q} (inj₂ r∈qs)

      phs′ : Complete (Rats (λ w h → E w h × h ∉ qs′) v) (q ∷ hs)
      phs′ {x} rs = to {xs = q ∷ []} {hs} {!phs!}
        where
        l : x ∈ q ∷ [] ⊎ x ∈ hs
        l with x ≟v q
        l | yes x=q = inj₁ (here x=q)
        l | no ¬x=q = inj₂ (phs {!!})
