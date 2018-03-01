module Data.Star.Rats where

  open import Data.Star
  open import Function
  open import Relation.Binary

  Rats : ∀ {i t} {I : Set i} → Rel I t → Rel I _
  Rats T = flip (Star (flip T))
