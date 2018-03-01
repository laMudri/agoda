module Data.List.Any.Membership.Extras {a} {A : Set a} where

  open import Data.Empty
  open import Data.Fin using (Fin; zero; suc)
  open import Data.List
  open import Data.List.All as All
  open import Data.List.Any as Any
  open import Data.List.Any.Membership.Propositional
  open import Data.List.Extras
  -- ↓ Data.List.Distinct
  open import Data.List.Sorted
  open import Data.Maybe using (Maybe; nothing; just)
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.Properties hiding (suc-injective)
  open import Data.Product

  open import Function

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary
  open import Relation.Binary.PartialOrderReasoning
    (DecTotalOrder.poset ≤-decTotalOrder)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary.Enum

  open import Data.List.Distinct (setoid A)

  ∈-remove : ∀ {x : A} {xs} → x ∈ xs → List A
  ∈-remove (here {xs = xs} px) = xs
  ∈-remove (there {x = x} elem) = x ∷ ∈-remove elem

  ∈-remove-length : ∀ {x : A} {xs} (x∈xs : x ∈ xs) →
                    suc (length (∈-remove x∈xs)) ≡ length xs
  ∈-remove-length (here px) = refl
  ∈-remove-length (there elem) = cong suc (∈-remove-length elem)

  ∈-remove-others-∈ : ∀ {p} {P : A → Set p} {x : A} {xs}
                      (any : Any P xs) (x∈xs : x ∈ xs) →
                      Any.index any ≢ Any.index x∈xs →
                      Any P (∈-remove x∈xs)
  ∈-remove-others-∈ (here _) (here _) neq = ⊥-elim (neq refl)
  ∈-remove-others-∈ (there any) (here px) neq = any
  ∈-remove-others-∈ (here px) (there elem) neq = here px
  ∈-remove-others-∈ (there any) (there elem) neq =
    there (∈-remove-others-∈ any elem (neq ∘ cong suc))

  suc-injective : ∀ {n} {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
  suc-injective refl = refl

  ≡-from-index : ∀ {y z : A} {xs} {y∈xs : y ∈ xs} {z∈xs : z ∈ xs} →
                 index y∈xs ≡ index z∈xs → y ≡ z
  ≡-from-index {y∈xs = here refl} {here refl} eq = refl
  ≡-from-index {y∈xs = here px} {there z∈xs} ()
  ≡-from-index {y∈xs = there y∈xs} {here px} ()
  ≡-from-index {y∈xs = there y∈xs} {there z∈xs} eq =
    ≡-from-index {y∈xs = y∈xs} {z∈xs} (suc-injective eq)

  ⊆-index-injection : ∀ {x y : A} {xs ys} → Distinct xs →
                      (sub : xs ⊆ ys) (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) →
                      index (sub x∈xs) ≡ index (sub y∈xs) →
                      index x∈xs ≡ index y∈xs
  ⊆-index-injection dxs sub (here px) (here px₁) eq = refl
  ⊆-index-injection {.x} {w} {x ∷ xs} {ys} (dx ∷ dxs) sub (here refl) (there w∈xs) eq = ⊥-elim (x≢w x≡w)
    where
    x≡w = ≡-from-index eq
    x≢w = lookup dx w∈xs
  ⊆-index-injection {v} {.x} {x ∷ xs} {ys} (dx ∷ dxs) sub (there v∈xs) (here refl) eq = ⊥-elim (x≢v (sym v≡x))
    where
    v≡x = ≡-from-index eq
    x≢v = lookup dx v∈xs
  ⊆-index-injection {v} {w} {x ∷ xs} {ys} (dx ∷ dxs) sub (there v∈xs) (there w∈xs) eq = cong suc (⊆-index-injection dxs (sub ∘ there) v∈xs w∈xs eq)

  ⊆-reduce : ∀ {x : A} {xs ys} → Distinct (x ∷ xs) → x ∷ xs ⊆ ys →
             ∃ λ ys′ → suc (length ys′) ≡ length ys × xs ⊆ ys′
  ⊆-reduce {x} {xs} {ys} dxs sub =
    ∈-remove (sub (here refl)) , ∈-remove-length (sub (here refl))
    , (λ y∈xs → ∈-remove-others-∈ (sub (there y∈xs)) (sub (here refl)) ((λ ()) ∘ ⊆-index-injection dxs sub (there y∈xs) (here refl)))

  ⊆-length : ∀ {xs ys : List A} → Distinct xs →
             xs ⊆ ys → length xs ≤ length ys
  ⊆-length {[]} {ys} dxs sub = z≤n
  ⊆-length {x ∷ xs} {ys} (dx ∷ dxs) sub with ⊆-reduce (dx ∷ dxs) sub
  ... | ys′ , l , sub′  = begin
    suc (length xs)   ≤⟨ s≤s (⊆-length dxs sub′) ⟩
    suc (length ys′)  ≈⟨ l ⟩
    length ys         ∎
