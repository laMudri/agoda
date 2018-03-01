module Relation.Unary.Enum.Product where

  open import Category.Monad using (RawMonad)

  open import Data.List as List
  open import Data.List.Any as Any
  open import Data.List.Any.Membership.Propositional
  open import Data.List.Any.Membership.Propositional.Properties
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
      { list = pure _,_ ⊛ P.list ⊛ Q.list
      ; consistent = consistent
      ; complete = complete
      }
      where
      module P = Enum pe
      module Q = Enum qe
      open module Dummy = RawMonad List.monad
      open module Dummy2 {A B} fs xs {y} = ↔ (⊛-∈↔ {A = A} {B} fs {xs} {y})

      consistent : Consistent (P ⟨×⟩ Q) (pure _,_ ⊛ P.list ⊛ Q.list)
      consistent ab∈ with from (pure _,_ ⊛ P.list) Q.list ab∈
      ... | f , x , f∈ , x∈ , refl with from (pure _,_) P.list f∈
      ... | ._,_ , y , here refl , y∈ , refl =
        P.consistent y∈ , Q.consistent x∈
      ... | g , y , there () , y∈ , refl

      complete : Complete (P ⟨×⟩ Q) (pure _,_ ⊛ P.list ⊛ Q.list)
      complete {x , y} (p , q) =
        to (pure _,_ ⊛ P.list) Q.list
           ((x ,_) , y
           , to (pure _,_) P.list
                (_,_ , x , here refl , P.complete p , refl)
           , Q.complete q , refl)

    _×-enum-minimal_ : ∀ {d e} → Minimal P d → Minimal Q e → Minimal _ (d ×-enum e)
    md ×-enum-minimal me = {!!}
