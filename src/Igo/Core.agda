module Igo.Core where

  open import Data.Bool using (Bool)
  open import Data.Fin
  open import Data.Fin.Properties
  open import Data.List
  open import Data.Maybe hiding (drop-just)
  open import Data.Nat using (ℕ)
  open import Data.Product

  open import Function

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Nullary
  open import Relation.Nullary.Decidable as D
  open import Relation.Nullary.Product

  data Player : Set where
    black white : Player

  playerDecSetoid : DecSetoid _ _
  playerDecSetoid = record
    { Carrier = Player
    ; _≈_ = _≡_
    ; isDecEquivalence = record
      { isEquivalence = PEq.isEquivalence
      ; _≟_ = λ { black black → yes refl
                ; black white → no (λ ())
                ; white black → no (λ ())
                ; white white → yes refl
                }
      }
    }

  open DecSetoid playerDecSetoid public using () renaming (_≟_ to _≟l_)

  Colour : Set
  Colour = Maybe Player

  private
    drop-just : ∀ {a} {A : Set a} {x y : A} →
                _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
    drop-just refl = refl

  colourDecSetoid : DecSetoid _ _
  colourDecSetoid = record
    { Carrier = Colour
    ; _≈_ = _≡_
    ; isDecEquivalence = record
      { isEquivalence = PEq.isEquivalence
      ; _≟_ = λ { (just x) (just y) → D.map′ (PEq.cong just) drop-just (x ≟l y)
                ; (just x) nothing → no (λ ())
                ; nothing (just y) → no (λ ())
                ; nothing nothing → yes refl
                }
      }
    }

  open DecSetoid colourDecSetoid public using () renaming (_≟_ to _≟c_)

  Position : ℕ → Set
  Position n = Fin n × Fin n

  positionDecSetoid : ℕ → DecSetoid _ _
  positionDecSetoid n = record
    { Carrier = Position n
    ; _≈_ = _≡_
    ; isDecEquivalence = record
      { isEquivalence = PEq.isEquivalence
      ; _≟_ = test
      }
    }
    where
    to : ∀ {a b} {A : Set a} {B : Set b} {x x′ : A} {y y′ : B} →
         x ≡ x′ × y ≡ y′ → (x , y) ≡ (x′ , y′)
    to (refl , refl) = refl

    from : ∀ {a b} {A : Set a} {B : Set b} {x x′ : A} {y y′ : B} →
           (x , y) ≡ (x′ , y′) → x ≡ x′ × y ≡ y′
    from refl = (refl , refl)

    test : (p q : Position n) → Dec (p ≡ q)
    test (px , py) (qx , qy) = D.map′ to from ((px ≟ qx) ×-dec (py ≟ qy))

  Board : ℕ → Set
  Board n = Position n → Colour

  History : ℕ → Set
  History n = List (Board n)

  Move : ℕ → Set
  Move n = Maybe (Position n)

  record State (n : ℕ) : Set where
    field
      nextPlayer : Player
      history : History n
      wasPass : Bool
