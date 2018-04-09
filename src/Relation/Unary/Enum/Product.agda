module Relation.Unary.Enum.Product where

  open import Category.Monad using (RawMonad)

  open import Data.List as List
  open import Data.List.Any as Any
  open import Data.List.Any.Membership.Propositional
  open import Data.List.Any.Membership.Propositional.Properties
  open import Data.List.Sorted
  open import Data.Product hiding (,_)

  open import Function.Inverse
  open import Function.Inverse.PropositionalEquality

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Minimal

  module _ {a p q} {A B : Set a} {P : Pred A p} {Q : Pred B q} where
    _×-enum_ : Enum P → Enum Q → Enum (P ⟨×⟩ Q)
    _×-enum_ pe qe = record
      { list = List.map _,_ P.list ⊛ Q.list
      ; consistent = consistent
      ; complete = complete
      }
      where
      module P = Enum pe
      module Q = Enum qe
      open module Dummy = RawMonad List.monad
      module ⊛ {A B} fs xs {y} = ↔ (⊛-∈↔ {A = A} {B} fs {xs} {y})
      module map {A B} f xs {y} = ↔ (map-∈↔ {A = A} {B} {f} {y} {xs})

      consistent : Consistent (P ⟨×⟩ Q) (List.map _,_ P.list ⊛ Q.list)
      consistent ab∈ with ⊛.from (List.map _,_ P.list) Q.list ab∈
      ... | f , x , f∈ , x∈ , refl with map.from _,_ P.list f∈
      ... | ._ , y∈ , refl = P.consistent y∈ , Q.consistent x∈

      complete : Complete (P ⟨×⟩ Q) (List.map _,_ P.list ⊛ Q.list)
      complete {x , y} (p , q) =
        ⊛.to (List.map _,_ P.list) Q.list
             ((x ,_) , y
             , map.to _,_ P.list (x , P.complete p , refl)
             , Q.complete q , refl)

    _×-enum-minimal_ :
      ∀ {d e} → Minimal P d → Minimal Q e → Minimal _ (d ×-enum e)
    md ×-enum-minimal me = {!!}
