module Data.Graph where
  open import Category.Monad

  open import Data.Bool
  open import Data.Bool.Properties
  open import Data.Empty
  open import Data.Fin
  open import Data.Fin.Properties as FP
  open import Data.List as List hiding ([_])
  open import Data.List.All as All
  open import Data.List.Any as Any renaming (any to any?)
  import Data.List.Categorical as LC
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Data.List.Any.Properties as AP
  open import Data.List.Properties
  open import Data.Maybe
  open import Data.Nat as ℕ
  open import Data.Product as ×
  open import Data.Sum as ⊎
  open import Data.Unit

  open import Function
  open import Function.Equality hiding (id; _∘_)
  open import Function.Equivalence hiding (id; _∘_)
  open import Function.Inverse hiding (id; _∘_)

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; _≢_; refl; subst; _≗_; inspect)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Unary as U hiding (_∈_; _∉_)

  Graph : ℕ → Set
  Graph n = (u v : Fin n) → Bool

  infixr 5 [_,_]_◅_
  data Path {n} (G : Graph n) : (u v : Fin n) → Set where
    ε : ∀ {u} → Path G u u
    [_,_]_◅_ : ∀ u v {w} (e : T (G u v)) → Path G v w → Path G u w

  data SimplePath {n} (G : Graph n) : (u v : Fin n) → Set
  simplePath-vertices : ∀ {n G u v} → SimplePath {n} G u v → List (Fin n)

  data SimplePath {n} G where
    ε : ∀ {u} → SimplePath G u u
    _◅_[_] : ∀ {u v w} (e : T (G u v)) (p : SimplePath G v w)
             (nin : u ∉ simplePath-vertices p) → SimplePath G u w
  simplePath-vertices (ε {u}) = u ∷ []
  simplePath-vertices (_◅_[_] {u} e p nin) = u ∷ simplePath-vertices p

  data SimplePathVisiting {n} (G : Graph n)
                          : List (Fin n) → (u w : Fin n) → Set where
    ε : ∀ {u} → SimplePathVisiting G (u ∷ []) u u
    _◅[_]_ : ∀ {u v w vs} (e : T (G u v)) (nin : u ∉ vs) →
             SimplePathVisiting G vs v w → SimplePathVisiting G (u ∷ vs) u w

  punchOut-v : ∀ {n} → Fin (suc n) → Graph (suc n) → Graph n
  punchOut-v u G v w = G (punchIn u v) (punchIn u w)

  lift-path : ∀ {n G} u {v w} → Path {n} (punchOut-v u G) v w →
                                Path G (punchIn u v) (punchIn u w)
  lift-path u ε = ε
  lift-path u {v} {w} ([_,_]_◅_ u′ v′ {w′} e p) =
    [ punchIn u u′ , punchIn u v′ ] e ◅ lift-path u {v′} {w′} p

  unPunchOut-path :
    ∀ {n G u v w} (u≢v : u ≢ v) (u≢w : u ≢ w) →
    Path {n} (punchOut-v u G) (punchOut u≢v) (punchOut u≢w) → Path G v w
  unPunchOut-path {u = u} {v} {w} u≢v u≢w p
    with         punchOut u≢v |         punchOut u≢w
       | inspect punchOut u≢v | inspect punchOut u≢w
  unPunchOut-path {u = u} {v} {w} u≢v u≢w ε
    | v′ | .v′ | ≡.[ eqv ] | ≡.[ eqw ]
    with punchOut-injective u≢v u≢w (≡.trans eqv (≡.sym eqw))
  ... | refl = ε
  unPunchOut-path {G = G} {u = u} {v} {w} u≢v u≢w ([ .v′ , x′ ] e ◅ p)
    | v′ | w′ | ≡.[ refl ] | ≡.[ refl ] =
    [ v , punchIn u x′ ]
    subst (λ x → T (G x _)) (punchIn-punchOut u≢v) e
    ◅ subst (Path G _) (punchIn-punchOut u≢w) (lift-path u p)

  u∈simplePath-vertices : ∀ {n G u v} (p : SimplePath {n} G u v) →
                          u ∈ simplePath-vertices p
  u∈simplePath-vertices ε = here refl
  u∈simplePath-vertices (e ◅ p [ nin ]) = here refl

  v∈simplePath-vertices : ∀ {n G u v} (p : SimplePath {n} G u v) →
                          v ∈ simplePath-vertices p
  v∈simplePath-vertices ε = here refl
  v∈simplePath-vertices (e ◅ p [ nin ]) = there (v∈simplePath-vertices p)

  punchOut-proof-irrelevant :
    ∀ {n} {i j : Fin (suc n)} (neq neq′ : i ≢ j) → punchOut neq ≡ punchOut neq′
  punchOut-proof-irrelevant {n} {zero} {zero} neq neq′ = ⊥-elim (neq refl)
  punchOut-proof-irrelevant {n} {zero} {suc j} neq neq′ = refl
  punchOut-proof-irrelevant {zero} {suc ()} {j} neq neq′
  punchOut-proof-irrelevant {suc n} {suc i} {zero} neq neq′ = refl
  punchOut-proof-irrelevant {suc n} {suc i} {suc j} neq neq′ =
    ≡.cong suc (punchOut-proof-irrelevant (neq  ∘ ≡.cong suc)
                                          (neq′ ∘ ≡.cong suc))

  punchOut-edge :
    ∀ {n} G {u v w : Fin (suc n)} (u≢v : u ≢ v) (u≢w : u ≢ w) →
    T (G v w) → T ((punchOut-v u G) (punchOut u≢v) (punchOut u≢w))
  punchOut-edge G u≢v u≢w e
    rewrite punchIn-punchOut u≢v | punchIn-punchOut u≢w = e

  punchOut-simplePath :
    ∀ {n G u v w} (u≢v : u ≢ v) (u≢w : u ≢ w)
    (p : SimplePath G v w) → u ∉ simplePath-vertices p →
    SimplePath {n} (punchOut-v u G) (punchOut u≢v) (punchOut u≢w)
  unPunchOut-simplePath-vertices :
    ∀ {n G u v v′ w} (u≢v : u ≢ v) (u≢v′ : u ≢ v′) (u≢w : u ≢ w)
    (p : SimplePath {suc n} G v′ w) (u∉ : u ∉ simplePath-vertices p) →
    punchOut u≢v ∈ simplePath-vertices (punchOut-simplePath u≢v′ u≢w p u∉) →
    v ∈ simplePath-vertices p

  punchOut-simplePath u≢v u≢w ε _ rewrite punchOut-proof-irrelevant u≢v u≢w = ε
  punchOut-simplePath {G = G} {u = u} u≢v u≢w (_◅_[_] {v = v′} e p v∉) u∉ =
    punchOut-edge G u≢v u≢v′ e ◅ punchOut-simplePath u≢v′ u≢w p (u∉ ∘ there)
    [ v∉ ∘ unPunchOut-simplePath-vertices u≢v u≢v′ u≢w p (u∉ ∘ there) ]
    where
    u≢v′ : u ≢ v′
    u≢v′ refl = u∉ (there (u∈simplePath-vertices p))

  unPunchOut-simplePath-vertices u≢v u≢v′ u≢w ε u∉ elem
    rewrite punchOut-proof-irrelevant u≢v′ u≢w with elem
  ... | here px = here (punchOut-injective u≢v u≢w px)
  ... | there ()
  unPunchOut-simplePath-vertices u≢v u≢v′ u≢w (e ◅ p [ nin ]) u∉ (here px) =
    here (punchOut-injective u≢v u≢v′ px)
  unPunchOut-simplePath-vertices u≢v u≢v′ u≢w (e ◅ p [ nin ]) u∉ (there elem) =
    there (unPunchOut-simplePath-vertices u≢v _ u≢w p (u∉ ∘ there) elem)

  simplePath→Path : ∀ {n G u v} → SimplePath G u v → Path {n} G u v
  simplePath→Path ε = ε
  simplePath→Path (e ◅ p [ nin ]) = [ _ , _ ] e ◅ simplePath→Path p

  simplePath-drop :
    ∀ {n G u v w}
    (p : SimplePath {n} G v w) → u ∈ simplePath-vertices p → SimplePath G u w
  simplePath-drop ε (here refl) = ε
  simplePath-drop ε (there ())
  simplePath-drop (e ◅ p [ v∉ ]) (here refl) = e ◅ p [ v∉ ]
  simplePath-drop (e ◅ p [ v∉ ]) (there u∈) = simplePath-drop p u∈

  path→SimplePath : ∀ {n G u v} → Path {n} G u v → SimplePath G u v
  path→SimplePath ε = ε
  path→SimplePath {n} {G} {.u} {w} ([ u , v ] e ◅ p) with path→SimplePath p
  ... | p′ with any? (u FP.≟_) (simplePath-vertices p′)
  ...   | yes u∈ = simplePath-drop p′ u∈
  ...   | no u∉ = e ◅ p′ [ u∉ ]

  T∘f? : ∀ {a} {A : Set a} (f : A → Bool) → U.Decidable (T ∘ f)
  T∘f? f x with f x
  ... | true = yes tt
  ... | false = no id

  ⌊T∘f?⌋ : ∀ {a} {A : Set a} (f : A → Bool) → ⌊_⌋ ∘ T∘f? f ≗ f
  ⌊T∘f?⌋ f x with f x
  ... | true = refl
  ... | false = refl

  gfilter-≗ : ∀ {a b A B f g} → f ≗ g → (xs : List A) →
              gfilter {a} {b} {A} {B} f xs ≡ gfilter g xs
  gfilter-≗ fg [] = refl
  gfilter-≗ {f = f} {g} fg (x ∷ xs) with f x | g x | fg x
  ... | just y | .(just y) | refl = ≡.cong (y ∷_) (gfilter-≗ fg xs)
  ... | nothing | .nothing | refl = gfilter-≗ fg xs

  {-
  filter-≗ : ∀ {a A p q} → p ≗ q → (xs : List A) →
             filter {a} {A} p xs ≡ filter q xs
  filter-≗ pq xs = gfilter-≗ (λ x → ≡.cong (if_then _ else _) (pq x)) xs

  open RawMonad {lzero} LC.monad

  connected-vertices : ∀ {n} → List (Fin n) → Graph n → List (Fin n)
  connected-vertices {zero} us G = []
  connected-vertices {suc n} us G =
    us >>= λ u →
    let
      us′ : List (Fin n)
      --us′ = filter (λ v → G u (punchIn u v)) (allFin n)
      us′ = filter (G u ∘ punchIn u) (allFin n)
    in
    u ∷ (List.map (punchIn u) (connected-vertices us′ (punchOut-v u G)))

  connected-vertices-consistent :
    ∀ {n} (us : List (Fin n)) (G : Graph n) →
    ∀ {v} → v ∈ connected-vertices us G → ∃ λ u → u ∈ us × Path G u v
  connected-vertices-consistent {zero} us G ()
  connected-vertices-consistent {suc n} us G {v} v∈cvs with
    find (Inverse.from (>>=↔ {xs = us}) ⟨$⟩ v∈cvs)
  ... | .v , v∈ , here refl = v , v∈ , ε
  ... | u , u∈ , there v∈ with u FP.≟ v
  ...   | yes refl = u , u∈ , ε
  ...   | no u≢v with
    connected-vertices-consistent _ (punchOut-v u G) {punchOut u≢v}
      (Any.map (λ { {x} refl → punchIn-injective u (punchOut u≢v) x
                                                 (punchIn-punchOut u≢v) })
               (Inverse.from map↔ ⟨$⟩ v∈))
  ...     | w , w∈ , p = u , u∈
    , [ u , punchIn u w ]
      All.lookup
        ?
        -- (filter-filters (T ∘ G u ∘ punchIn u)
        --                 (T∘f? (G u ∘ punchIn u))
        --                 (allFin n))
        (subst (w ∈_)
               (≡.sym (filter-≗ (⌊T∘f?⌋ (G u ∘ punchIn u)) (allFin n)))
               w∈)
      ◅ subst (Path G (punchIn u w)) (punchIn-punchOut u≢v) (lift-path u p)

  ∈-allFin : ∀ {n} i → i ∈ allFin n
  ∈-allFin i = tabulate⁺ i refl

  connected-vertices-complete′ :
    ∀ {n} (us : List (Fin n)) (G : Graph n) →
    ∀ {u v} → u ∈ us → SimplePath G u v → v ∈ connected-vertices us G
  connected-vertices-complete′ {zero} us G {()} {v} u∈us p
  connected-vertices-complete′ {suc n} us G {u} {.u} u∈us ε =
    Inverse.to (>>=↔ {xs = us}) ⟨$⟩ Any.map here u∈us
  connected-vertices-complete′ {suc n} us G {u} {w} u∈us (_◅_[_] {v = v} e p nin) =
    Inverse.to (>>=↔ {xs = us})
      ⟨$⟩ Any.map (λ { refl → there
        (Inverse.to map↔
          ⟨$⟩ Any.map {P = punchOut u≢w ≡_} {Q = (w ≡_) ∘ punchIn u}
                      (λ { refl → ≡.sym (punchIn-punchOut u≢w) })
                      (connected-vertices-complete′ _
                        (punchOut-v u G) {punchOut u≢v} {punchOut u≢w}
                        (filter-∈
                          (G u ∘ punchIn u) (allFin n) (∈-allFin _)
                          (Equivalence.to T-≡
                            ⟨$⟩ (subst (T ∘ G u)
                                       (≡.sym (punchIn-punchOut u≢v))
                                       e)))
                        (punchOut-simplePath u≢v u≢w p nin))) })
        u∈us
    where
    u≢v : u ≢ v
    u≢v refl = nin (u∈simplePath-vertices p)

    u≢w : u ≢ w
    u≢w refl = nin (v∈simplePath-vertices p)

  connected-vertices-complete :
    ∀ {n} (us : List (Fin n)) (G : Graph n) →
    ∀ {u v} → u ∈ us → Path G u v → v ∈ connected-vertices us G
  connected-vertices-complete us G u∈us p =
    connected-vertices-complete′ us G u∈us (path→SimplePath p)

  connected? : ∀ {n} (G : Graph n) (u v : Fin n) → Dec (Path G u v)
  connected? G u v =
    map′ to from (any? (v FP.≟_) (connected-vertices (u ∷ []) G))
    where
    to : v ∈ connected-vertices (u ∷ []) G → Path G u v
    to v∈ with connected-vertices-consistent (u ∷ []) G v∈
    to v∈ | _ , here refl , p = p
    to v∈ | u′ , there () , p

    from : Path G u v → v ∈ connected-vertices (u ∷ []) G
    from = connected-vertices-complete (u ∷ []) G (here refl)

  -- Remove edges to and from deleted nodes (but keep all the nodes themselves)
  subgraph : ∀ {n} → (Fin n → Bool) → Graph n → Graph n
  subgraph p G u v = p u ∧ p v ∧ G u v
  -}
