open import Relation.Binary

module Subgraph {v e} {V : Set v} (E : Rel V e) where

  open import Data.Empty
  open import Data.Product
  open import Data.Unit

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary.PropositionalEquality

  record Subgraph vp ep : Set (lsuc (vp ⊔ ep) ⊔ v ⊔ e) where
    field
      VP : V → Set vp
      EP : ∀ {v w} → VP v → VP w → E v w → Set ep

    graph : Rel (∃ λ v → VP v) (ep ⊔ e)
    graph (v , pv) (w , pw) = ∃ λ (e : E v w) → EP pv pw e

  total-subgraph : Subgraph _ _
  Subgraph.VP total-subgraph _ = ⊤
  Subgraph.EP total-subgraph _ _ _ = ⊤

  empty-subgraph : Subgraph _ _
  Subgraph.VP empty-subgraph _ = ⊥
  Subgraph.EP empty-subgraph _ _ _ = ⊥

  record _⊆sg_ {vp ep} (G H : Subgraph vp ep)
               : Set (lsuc (vp ⊔ ep) ⊔ v ⊔ e) where
    open Subgraph
    field
      VP-⊆ : ∀ {v} → VP G v → VP H v
      EP-⊆ : ∀ {v w} {e : E v w} (v∈G : VP G v) (w∈G : VP G w) →
             EP G v∈G w∈G e → EP H (VP-⊆ v∈G) (VP-⊆ w∈G) e

  ⊆-total-subgraph : ∀ G → G ⊆sg total-subgraph
  _⊆sg_.VP-⊆ (⊆-total-subgraph G) _ = tt
  _⊆sg_.EP-⊆ (⊆-total-subgraph G) _ _ _ = tt

  empty-subgraph-⊆ : ∀ G → empty-subgraph ⊆sg G
  _⊆sg_.VP-⊆ (empty-subgraph-⊆ G) ()
  _⊆sg_.EP-⊆ (empty-subgraph-⊆ G) _ _ ()

  delete-v-subgraph : ∀ {vp ep} → V → Subgraph vp ep → Subgraph (vp ⊔ v) lzero
  Subgraph.VP (delete-v-subgraph v record { VP = VP }) w = v ≢ w × VP w
  Subgraph.EP (delete-v-subgraph v G) _ _ e = ⊤

