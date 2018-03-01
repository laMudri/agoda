open import Relation.Binary
import Relation.Binary.Graph as G

module Relation.Binary.Graph.Labels {v e} {V : Set v} (E : Rel V e) (r : G.Finite E) where

  open import Data.List.All

  open import Level

  open import Relation.Binary.Graph E
  open Finite r

  VertexLabels : ∀ {l} → (V → Set l) → Set (v ⊔ l)
  VertexLabels P = All P V.list
