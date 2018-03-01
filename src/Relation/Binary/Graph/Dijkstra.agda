open import Data.Maybe
open import Data.Nat
open import Data.PriorityQueue

open import Relation.Binary
import Relation.Binary.Graph as G

module Relation.Binary.Graph.Dijkstra
       {v e ℓ} {V : Set v} (E : Rel V e)
       (finite : G.Finite E) (_≈v_ : Rel V ℓ) (DE : IsDecEquivalence _≈v_)
       {q i} (Q : Set q) (pq : PriorityQueue decTotalOrder V i Q)
       (w : ∀ {v v′} → E v v′ → Maybe ℕ) (s : V) where

  open G E
  open PriorityQueue pq

  vDecSetoid : DecSetoid v ℓ
  vDecSetoid = record { Carrier = V ; _≈_ = _≈v_ ; isDecEquivalence = DE }

  open DecSetoid vDecSetoid using () renaming (_≟_ to _≟v_)

  open import Data.List
  open import Data.List.Any
  open Membership-≡
  open import Data.List.Distinct setoid
  open import Data.Nat.IsSuc
  open import Data.Product
  open import Data.Star
  open import Data.Star.Rats
  open import Data.Vec hiding (_∈_)

  open import Function.Update vDecSetoid

  -- TODO: new module
  remove : ∀ {a n} {A : Set a}
           (xs : Vec A (suc n)) {x} → x ∈ toList xs → Vec A n
  remove (x ∷ xs) (here px) = xs
  remove (x ∷ []) (there x∈xs) = []
  remove (x ∷ x′ ∷ xs) (there x∈xs) = x ∷ remove (x′ ∷ xs) x∈xs

  dijkstra : V → Maybe ℕ
  dijkstra v = {!!}
    where
    go : ∀ {n} (as : Vec V n) (qs : Q) → (∀ {q} → q V∈ qs → q ∈ toList as) →
         (V → Maybe ℕ) → (V → Maybe ℕ)
    go {n} as qs sub d with size qs | extract qs | V∈-extract qs
    ... | zero | _ | _ = d
    ... | suc q | ex | _ with ex (is-suc q)
    go {zero} [] qs sub d | suc q | ex | _ | ((k , v) , qs′) = {!!}
    go {suc n} as qs sub d | suc q | ex | V∈-ex | ((k , v) , qs′) =
      go {n} (remove as (sub {v} {!V∈-ex (is-suc q)!})) {!!} {!!} (d ⟨ {!×!} ⟩≔ {!!})
