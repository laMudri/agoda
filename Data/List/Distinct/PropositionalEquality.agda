module Data.List.Distinct.PropositionalEquality where
  open import Data.Empty
  open import Data.List as List hiding (any)
  open import Data.List.All as All
  open import Data.List.All.Properties
  open import Data.List.Any as Any
  open import Data.List.Any.Membership.Propositional
  open import Data.List.Any.Properties
  open import Data.List.Sorted
  open import Data.Sum as ⊎

  open import Function
  --open import Function.Equality using (_⟨$⟩_; cong)
  open import Function.Equivalence using (Equivalence; _⇔_)
  open import Function.Equivalence.PropositionalEquality
  open import Function.Injection using (Injection; _↣_)
  open import Function.Injection.PropositionalEquality
  open import Function.Inverse using (Inverse; _↔_)
  open import Function.Inverse.PropositionalEquality

  open import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Nullary
  open import Relation.Unary as U hiding (_∈_; _∉_; Decidable)

  open import Data.List.Distinct as D using ()
    renaming (module Decidable to Decidable′)
  open module Dummy {a} {A : Set a} =
    D (PEq.setoid A) public hiding (module Decidable)

  ∈≡ : ∀ {a A x xs} → Distinct {a} {A} xs → (e f : x ∈ xs) → e ≡ f
  ∈≡ ds (here refl) (here refl) = refl
  ∈≡ (dx ∷ ds) (here refl) (there f) = ⊥-elim (lookup dx f refl)
  ∈≡ (dx ∷ ds) (there e) (here refl) = ⊥-elim (lookup dx e refl)
  ∈≡ (dx ∷ ds) (there e) (there f) = cong there (∈≡ ds e f)

  module Decidable {a A} (_≟_ : Decidable (_≡_ {a} {A})) where

    open Decidable′ (PEq.setoid A) _≟_ public

    ∷∉⇔ : ∀ {p} {P : Pred A p} x {ys} (dys : Distinct ys) →
          (P x ⊎ Any P ys) ⇔ Any P (x ∷∉ ys)
    ∷∉⇔ {P = P} x {ys} dys = mk-⇔ [ toˡ , toʳ ] from
      where
      toˡ : P x → Any P (x ∷∉ ys)
      toˡ px with any (x ≟_) ys
      toˡ px | yes x∈ys = Any.map (λ eq → subst P eq px) x∈ys
      toˡ px | no x∉ys = here px

      toʳ : Any P ys → Any P (x ∷∉ ys)
      toʳ pxs with any (x ≟_) ys
      toʳ pxs | yes x∈ys = pxs
      toʳ pxs | no x∉ys = there pxs

      from : Any P (x ∷∉ ys) → P x ⊎ Any P ys
      from ps with any (x ≟_) ys
      from ps | yes x∈ys = inj₂ ps
      from (here px) | no x∉ys = inj₁ px
      from (there ps) | no x∉ys = inj₂ ps

    {-+}
    ++∉⇔ : ∀ {p} {P : Pred A p} xs {ys} (dys : Distinct ys) →
           (Any P xs ⊎ Any P ys) ⇔ Any P (xs ++∉ ys)
    ++∉⇔ {P = P} xs {ys} dys = mk-⇔ [ toˡ , toʳ ] from
      where
      toˡ : Any P xs → Any P (xs ++∉ ys)
      toˡ (here {x} {xs} px) = {!to (inj₁ px)!}
        where
        open ⇔ (∷∉⇔ {P = P} x dys)
      toˡ (there pxs) = {!!}

      toʳ : Any P ys → Any P (xs ++∉ ys)
      toʳ pxs = {!!}

      from : Any P (xs ++∉ ys) → Any P xs ⊎ Any P ys
      from ps = {!!}
    {+-}

  Distinct-map : ∀ {a b} {A : Set a} {B : Set b} (f : A ↣ B) {xs} →
        let open ↣ f in Distinct xs → Distinct (List.map to xs)
  Distinct-map f {[]} [] = []
  Distinct-map f {x ∷ xs} (dx ∷ dxs) =
    All-map (All.map (_∘ injective) dx) ∷ Distinct-map f dxs
    where open ↣ f
