open import Relation.Binary

module Relation.Binary.Graph.CycleFree {v e} {V : Set v} (E : Rel V e) where

  open import Data.Empty
  open import Data.List
  open import Data.List.All
  open import Data.List.Sorted
  open import Data.Product
  open import Data.Star
  open import Data.Sum

  open import Function

  open import Level

  open import Relation.Binary.Graph E
  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Nullary
  open import Relation.Unary as U using (Pred)

  open import Data.List.Distinct (PEq.setoid V)

  Is-cycle : ∀ {i j} → Pred (Path i j) v
  Is-cycle {i} {j} _ = i ≡ j

  Cycle-free : ∀ {i j} → Pred (Path i j) v
  Cycle-free = Distinct ∘ path-fenceposts

  Cycle-free? : ∀ {i j} → U.Decidable (Cycle-free {i} {j})
  Cycle-free? = SortedBy? {!!} ∘ path-fenceposts

  ¬Cycle-free→Cycle : ∀ {i j} {es : Path i j} → ¬ Cycle-free es →
                      ∃ λ (sub : Subpath es) → Is-cycle (Subpath.ys sub)
  ¬Cycle-free→Cycle {i} {.i} {ε} ¬cf = ⊥-elim (¬cf ([] ∷ []))
  ¬Cycle-free→Cycle {i} {j} {e ◅ es} ¬cf = {!all!}

  simplify-path : ∀ {i j} → Path i j → ∃ λ (es : Path i j) → Cycle-free es
  simplify-path es = {!!}
