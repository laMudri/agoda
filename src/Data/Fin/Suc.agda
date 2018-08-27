module Data.Fin.Suc where

  open import Data.Fin as Fin
  open import Data.Fin.Properties as FinP
  open import Data.List as List
  open import Data.List.Any as Any
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Data.List.Any.Properties as AnyP
  open import Data.Nat as N
  open import Data.Product as Σ

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Function.Inverse.PropositionalEquality

  open import Relation.Binary as B
  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Unary as U hiding (_∈_)
  open import Relation.Unary.Enum

  -- x Suc y iff y is the successor of x
  data _Suc_ : ∀ {n} → Rel (Fin (suc n)) lzero where
    0S1 : ∀ {n} → zero Suc (suc (zero {n}))
    sSs : ∀ {n} {x y : Fin (suc n)} → x Suc y → suc x Suc suc y

  private
    drop-suc : ∀ {n} {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
    drop-suc refl = refl

  suc-enum-step : ∀ {n} {i : Fin (suc n)} → Enum (i Suc_) → Enum (suc i Suc_)
  suc-enum-step {n} {i} e = record
    { list = list′
    ; consistent = consistent′
    ; complete = complete′
    }
    where
    open Enum e
    module M {a b p} {A : Set a} {B : Set b} {P : Pred B p}
             {f : A → B} {xs : List A} =
      ↔ (map↔ {A = A} {B} {p} {P} {f} {xs})

    list′ = List.map suc list

    consistent′ : ∀ {j} → j ∈ list′ → suc i Suc j
    consistent′ {zero} elem with satisfied (M.from elem)
    ... | _ , ()
    consistent′ {suc j} elem =
      sSs (consistent (Any.map drop-suc (M.from elem)))

    complete′ : ∀ {j} → suc i Suc j → j ∈ list′
    complete′ {.(suc _)} (sSs s) = ∈-map⁺ (complete s)

  suc-enum : ∀ {n} (i : Fin (suc n)) → Enum (i Suc_)
  suc-enum {zero} zero = record
    { list = []
    ; consistent = λ ()
    ; complete = λ { {zero} () ; {suc ()} s }
    }
  suc-enum {suc n} zero = record
    { list = suc zero ∷ []
    ; consistent = λ { (here refl) → 0S1 ; (there ()) }
    ; complete = λ { 0S1 → here refl }
    }
  suc-enum {zero} (suc ())
  suc-enum {suc zero} (suc i) = record
    { list = []
    ; consistent = λ ()
    ; complete = λ { {zero} () ; {suc zero} (sSs ()) ; {suc (suc ())} s }
    }
  suc-enum {suc (suc n)} (suc i) = suc-enum-step (suc-enum i)

  inject₁-Suc-suc : ∀ {n} (i : Fin n) → inject₁ i Suc suc i
  inject₁-Suc-suc zero = 0S1
  inject₁-Suc-suc (suc i) = sSs (inject₁-Suc-suc i)

  !-Suc-suc : ∀ {n p} (i : Fin n) → p Suc suc i → p ≡ inject₁ i
  !-Suc-suc {.(suc _)} {zero} .zero 0S1 = refl
  !-Suc-suc {.(suc _)} {suc p} zero (sSs ())
  !-Suc-suc {.(suc _)} {suc p} (suc i) (sSs s) = PEq.cong suc (!-Suc-suc i s)

  pred-enum : ∀ {n} (i : Fin (suc n)) → Enum (_Suc i)
  pred-enum {n} zero = record
    { list = []
    ; consistent = λ ()
    ; complete = λ ()
    }
  pred-enum {n} (suc i) = record
    { list = inject₁ i ∷ []
    ; consistent = λ { (here refl) → inject₁-Suc-suc i ; (there ()) }
    ; complete = λ s → here (!-Suc-suc i s)
    }
