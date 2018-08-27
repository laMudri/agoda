open import Relation.Binary

module Relation.Binary.Graph {v e} {V : Set v} (E : Rel V e) where

  open import Category.Monad

  open import Data.Bool as 𝔹
  open import Data.Bool.Properties using (¬-not)
  open import Data.Empty
  open import Data.List as L hiding (any)
  import Data.List.Categorical as LC
  open module Dummy {a} = RawMonad (LC.monad {a})
  open import Data.List.All as All
  open import Data.List.All.Membership
  open import Data.List.Any as Any
  open import Data.List.Any.Properties
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Extras
  open import Data.List.Properties
  open import Data.List.Sorted
  open import Data.Maybe as M hiding (All)
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.Properties
  open import Data.Nat.Properties.Simple
  open import Data.Product
  open import Data.Star as Star using (Star; ε; _◅_; _◅◅_)
  open import Data.Star.Properties
  open import Data.Star.Rats
  open import Data.Sum
  open import Data.Unit using (⊤; tt)

  open import Function
  open import Function.Inverse.PropositionalEquality

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary.PropositionalEquality as PEq
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary as U using ()
  open import Relation.Unary.Enum
  open import Relation.Unary.Enum.Type

  open import Data.List.Distinct (PEq.setoid V)

  record Finite : Set (v ⊔ e) where
    field
      vertex-enum : Enum-type V
      edge-enum : ∀ v → Enum (E v)

    module V = Enum-type vertex-enum
    module E v = Enum (edge-enum v)
  --open Finite public

  Path : Rel V (v ⊔ e)
  Path = Rats E

  path-fenceposts : ∀ {v w} → Path v w → List V
  path-fenceposts {v} ε = v ∷ []
  path-fenceposts {v} (e ◅ es) = v ∷ path-fenceposts es

  record Subpath {i j} (es : Path i j) : Set (v ⊔ e) where
    field
      {i′ j′} : V
      xs : Path i i′
      ys : Path i′ j′
      zs : Path j′ j
      eq : zs ◅◅ ys ◅◅ xs ≡ es

  record _≈sub_ {i j} {es : Path i j} (subl subr : Subpath es)
                : Set (v ⊔ e) where
    open Subpath subl renaming (i′ to i′l; j′ to j′l; ys to ysl)
    open Subpath subr renaming (i′ to i′r; j′ to j′r; ys to ysr)
    field
      i′ : i′l ≡ i′r
      j′ : j′l ≡ j′r
      ys : subst₂ Path i′ j′ ysl ≡ ysr

  drop-suc : ∀ {x y} → suc x ≡ suc y → x ≡ y
  drop-suc refl = refl

  gfilter-all : ∀ {a b} {A : Set a} {B : Set b}
                (p : A → Maybe B) (xs : List A) →
                length (gfilter p xs) ≡ length xs → All (Is-just ∘ p) xs
  gfilter-all p [] eq = []
  gfilter-all p (x ∷ xs) eq with p x | inspect p x
  gfilter-all p (x ∷ xs) eq | just y | [ pxeq ] =
    subst (M.Any (λ _ → ⊤)) (sym pxeq) (just tt)
    ∷ gfilter-all p xs (drop-suc eq)
  gfilter-all p (x ∷ xs) eq | nothing | [ _ ] =
    ⊥-elim (<⇒≢ (s≤s (length-gfilter p xs)) eq)

  {-+}
  filter-all : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) →
               length (filter p xs) ≡ length xs → All (T ∘ p) xs
  filter-all p xs eq = All.map f (gfilter-all _ xs eq)
    where
    f : ∀ {x} → Is-just (if p x then just x else nothing) → T (p x)
    f {x} j with p x
    f {x} () | false
    f {x} _ | true = tt
  {+-}

  {-+}
  connected-component :
    (f : Finite) → Distinct (V.list f) → Decidable (_≡_ {A = V}) →
    ∀ v → Enum (Rats E v)
  connected-component f dvlist _≟v_ v = {!dvlist!}

  ∉-filter : ∀ {a p} {A : Set a} (P : A → Set p)
             (dec : U.Decidable P) xs {x} →
             x ∉ filter (⌊_⌋ ∘ dec) xs → ¬ P x
  ∉-filter P dec xs ∉ px = ∉ (filter-∈ (⌊_⌋ ∘ dec) xs {!!} {!!})
    --{!lookup (filter-filters P dec xs)!}
  {+-}

  {-+}
  connected-component :
    (f : Finite) → Distinct (V.list f) → Decidable (_≡_ {A = V}) → ∀ v → Enum (Rats E v)
  connected-component f dvlist _≟v_ v = {!Data.Nat.Properties!}
    where
    open Finite f
    open Decidable _≟v_

    go : ∀ t (unvisited : V → Bool) →
         length (filter unvisited V.list) ≤ t →
         Enum (Rats E v)
    go zero uv le = {!le!}
    go (suc t) uv le = go t uv′ {!!}
      where
      vs vs′ : List V
      vs = filter (not ∘ uv) V.list
      vs′ = (vs >>= E.list) ++ vs

      uv′ : V → Bool
      uv′ v = ⌊ ¬? (any (v ≟v_) vs′) ⌋

      vs⊆vs′ : vs ⊆ vs′
      vs⊆vs′ = ([] ⊆ (vs >>= E.list) ∋ λ ()) ++-mono id

      uv′⊆uv : filter uv′ V.list ⊆ filter uv V.list
      uv′⊆uv {v} v∈uv′ =
        let v∉vs′ = lookup (filter-filters (λ x → ¬ (x ∈ vs′)) (λ x → ¬? (any (x ≟v_) vs′)) V.list) v∈uv′ in
        let v∉vs = v∉vs′ ∘ vs⊆vs′ in
        --filter-∈ uv V.list (V.complete v) {!filter-filters (λ x → not (uv x) ≡ true) ? V.list ,′ vs!}
        case uv v 𝔹.≟ true of λ
        { (yes p) → filter-∈ uv V.list (V.complete v) p
        ; (no ¬p) → ⊥-elim (v∉vs (filter-∈ (not ∘ uv) V.list (V.complete v) (sym (¬-not (¬p ∘ sym)))))
        }

      uv′≤uv : length (filter uv′ V.list) ≤ length (filter uv V.list)
      uv′≤uv = ⊆-length (filter-Distinct uv′ {xs = V.list} {!!}) uv′⊆uv

      uv′<uv : suc (length (filter uv′ V.list)) ≤ length (filter uv V.list)
      uv′<uv = {!!}
  {+-}
