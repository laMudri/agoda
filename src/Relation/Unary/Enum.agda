open import Relation.Binary as B using (Setoid; REL)

module Relation.Unary.Enum where

  open import Category.Monad using (RawMonad)

  open import Data.Bool as Bool
  open import Data.Bool.Properties as BoolP
  open import Data.Empty
  open import Data.List as List
  open import Data.List.All as All
  open import Data.List.All.Membership
  open import Data.List.Any as Any
  open import Data.List.Any.Properties as AnyP
  open import Data.List.Categorical as LC
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Map as MemMap
  open import Data.List.Membership.Propositional.Properties
  open import Data.List.Properties as ListP
  open import Data.List.Relation.Sublist.Propositional.Properties
  open import Data.Product as Σ hiding (,_)
  open import Data.Sum as ⊎

  open import Function
  import Function.Equivalence as Equiv
  open import Function.Equivalence.PropositionalEquality
  open import Function.Inverse.PropositionalEquality

  open import Level

  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary as U hiding (_∈_)

  Consistent : ∀ {a p} {A : Set a} → Pred A p → List A → Set _
  Consistent P list = ∀ {a} → a ∈ list → P a

  Complete : ∀ {a p} {A : Set a} → Pred A p → List A → Set _
  Complete P list = ∀ {a} → P a → a ∈ list

  record Enum {a p} {A : Set a} (P : Pred A p) : Set (a ⊔ p) where
    field
      list : List A
      consistent : Consistent P list
      complete : Complete P list

  module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where
    infixr 2 _∪-enum_ _∩-enum_

    _∪-enum_ : Enum P → Enum Q → Enum (P ∪ Q)
    pe ∪-enum qe = record
      { list = P.list ++ Q.list
      ; consistent = ⊎.map P.consistent Q.consistent ∘ from
      ; complete = to ∘ (⊎.map P.complete Q.complete)
      }
      where
      module P = Enum pe
      module Q = Enum qe

      open module Dummy {a} = ↔ (++↔ {P = a ≡_} {P.list} {Q.list})

    _∩-enum_ : Enum P → U.Decidable Q → Enum (P ∩ Q)
    pe ∩-enum qd = record
      { list = filter qd list
      ; consistent = λ a∈ → Σ.map consistent id (∈-filter⁻ qd a∈)
      ; complete = λ { (pa , qa) → ∈-filter⁺ qd (complete pa) qa
        }
      }
      where
      open Enum pe

    Enum→ : (∀ {a} → P a ⇔ Q a) → Enum P → Enum Q
    Enum→ equiv pe = record
      { list = list
      ; consistent = λ a∈ → to (consistent a∈)
      ; complete = λ qa → complete (from qa)
      }
      where
      open module Dummy {a} = ⇔ (equiv {a})
      open Enum pe

  module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where
    -- Separate from above because we need P and Q to be general

    Enum⇔ : (∀ {a} → P a ⇔ Q a) → Enum P ⇔ Enum Q
    Enum⇔ equiv = record
      { to = →-to-⟶ (Enum→ equiv)
      ; from = →-to-⟶ (Enum→ (Equiv.sym equiv))
      }

  module _ {a p q} {A : Set a} {B : Set a} {P : Pred A p} {Q : REL A B q} where
    _>>=-enum_ : Enum P → (∀ a → Enum (Q a)) →
                 Enum (λ b → ∃ λ a → P a × Q a b)
    pe >>=-enum qe = record
      { list = P.list >>= Q.list
      ; consistent = λ b∈ →
        Σ.map id (Σ.map P.consistent (Q.consistent _)) (from b∈)
      ; complete = λ { (a , pa , qab) →
                       to (a , P.complete pa , Q.complete a qab)
                     }
      }
      where
      module P = Enum pe
      module Q (a : _) = Enum (qe a)
      open RawMonad LC.monad
      open module Dummy {y : _} = ↔ (>>=-∈↔ {A = A} {B} {P.list} {Q.list} {y})

  module _ {a p A P} (eq? : B.Decidable (_≡_ {A = A}))
           (e : Enum {a} {p} {A} P) where
    open Enum e

    Enum→Dec : U.Decidable P
    Enum→Dec a with Any.any (eq? a) list
    ... | yes a∈ = yes (consistent a∈)
    ... | no ¬a∈ = no (¬a∈ ∘ complete)

  ∈-enum : ∀ {a} {A : Set a} (xs : List A) → Enum (_∈ xs)
  ∈-enum xs = record { list = xs ; consistent = id ; complete = id }

  -- TODO: move
  infixr 4 _=[_]⇒_

  _=[_]⇒_ : ∀ {a b p q} {A : Set a} {B : Set b} →
            Pred A p → (A → B) → Pred B q → Set _
  P =[ f ]⇒ Q = P U.⊆ Q ∘ f

  map-enum : ∀ {a b p q} {A : Set a} {B : Set b} {P : Pred A p} {Q : Pred B q}
             (inv : A ↔ B) → let open ↔ inv in
             P =[ to ]⇒ Q → Q =[ from ]⇒ P → Enum P → Enum Q
  map-enum {P = P} {Q} inv pq qp e = record
    { list = List.map to list
    ; consistent =
        subst Q (right-inverse-of _)
      ∘ pq
      ∘ consistent
      ∘ Any.map (λ t → trans (PEq.cong from t) (left-inverse-of _))
      ∘ M.from
    ; complete =
        M.to
      ∘ Any.map (trans (sym (right-inverse-of _)) ∘ PEq.cong to)
      ∘ complete
      ∘ qp
    }
    where
    open Enum e
    open ↔ inv

    module M {a} = ↔ (map↔ {P = a ≡_} {to} {list})

  image-enum : ∀ {a b p} {A : Set a} {B : Set b} {P : Pred A p}
               (f : A → B) → Enum P → (Enum λ b → ∃ λ a → b ≡ f a × P a)
  image-enum f pe = record
    { list = List.map f list
    ; consistent = λ b∈ → Σ.map id (Σ.map id consistent) (∈-unmap f b∈)
    ; complete = λ { (a , b≡fa , pa) →
                     subst (_∈ _) (sym b≡fa) (∈-map f (complete pa))
                   }
    }
    where
    open Enum pe

  module _ {a p} {A : Set a} {P : Pred A p} where
    Consistent-tail : ∀ {x xs} → Consistent P (x ∷ xs) → Consistent P xs
    Consistent-tail sxxs y∈ = sxxs (there y∈)

    Complete-tail : ∀ {x xs} → ¬ P x → Complete P (x ∷ xs) → Complete P xs
    Complete-tail {x} {xs} ¬px cxxs {y} py with cxxs py
    ... | here refl = ⊥-elim (¬px py)
    ... | there z = z
