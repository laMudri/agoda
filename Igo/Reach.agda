open import Data.Nat hiding (_⊔_)

module Igo.Reach {n : ℕ} where

  open import Data.Fin
  open import Data.Fin.Suc
  open import Data.List as List using (List; []; _∷_; _++_)
  open import Data.List.Any as Any
  open import Data.List.Any.Membership.Map
  open import Data.List.Any.Properties as AnyP using (map↔; ++↔)
  open import Data.List.NonEmpty as List⁺
  open import Data.List.Properties as ListP
  open Membership-≡ using (_∈_; map-with-∈)
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  open import Data.Product as Σ hiding (,_)
  open import Data.Star using (Star; ε; _◅_; _◅◅_)
  open import Data.Sum as ⊎
  open import Data.SymmetricClosure
  open import Data.Unit

  open import Function
  open import Function.Equivalence.PropositionalEquality
  open import Function.Inverse.PropositionalEquality

  open import Igo.Core

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Relation.Binary as B hiding (Sym; _=[_]⇒_)
  open import Relation.Binary.PropositionalEquality as PEq hiding (cong)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable as D
  open import Relation.Unary as U using (Pred)
  open import Relation.Unary.Enum

  open DecSetoid (positionDecSetoid (suc n)) using () renaming (_≟_ to _≟p_)

  infix 4 _Touches↘_ _Touches_

  data _Touches↘_ : Rel (Position (suc n)) lzero where
    east : ∀ {x x′ y} → x Suc x′ → (x , y) Touches↘ (x′ , y)
    south : ∀ {x y y′} → y Suc y′ → (x , y) Touches↘ (x , y′)

  _Touches↘-enum : (p : Position (suc n)) → Enum (p Touches↘_)
  _Touches↘-enum p@(x , y) = record
    { list = xlist ++ ylist
    ; consistent = [ xconsistent , yconsistent ]′ ∘ ++.from
    ; complete = ++.to ∘ complete
    }
    where
    module X = Enum (suc-enum x)
    module Y = Enum (suc-enum y)

    xlist = List.map (_, y) X.list
    ylist = List.map (x ,_) Y.list

    module ++ {p} {P : Pred _ p} = ↔ (++↔ {P = P} {xlist} {ylist})
    module M {a p} {A : Set a} {P : Pred (Position (suc n)) p}
             {f : A → _} {xs : List _} =
      ↔ (map↔ {P = P} {f} {xs})

    xconsistent : ∀ {q} → q ∈ xlist → p Touches↘ q
    xconsistent elem
      with satisfied (Any.map (PEq.cong proj₂) (M.from elem))
    ... | _ , refl =
      east (X.consistent (Any.map (PEq.cong proj₁) (M.from elem)))

    yconsistent : ∀ {q} → q ∈ ylist → p Touches↘ q
    yconsistent elem
      with satisfied (Any.map (PEq.cong proj₁) (M.from elem))
    yconsistent elem | proj₃ , refl =
      south (Y.consistent (Any.map (PEq.cong proj₂) (M.from elem)))

    complete : ∀ {q} → p Touches↘ q → q ∈ xlist ⊎ q ∈ ylist
    complete (east s) =
      inj₁ (M.to (Any.map (PEq.cong (_, y)) (X.complete s)))
    complete (south s) =
      inj₂ (M.to (Any.map (PEq.cong (x ,_)) (Y.complete s)))

  _Touches↖-enum : (q : Position (suc n)) → Enum (_Touches↘ q)
  _Touches↖-enum q@(x , y) = record
    { list = xlist ++ ylist
    ; consistent = [ xconsistent , yconsistent ]′ ∘ ++.from
    ; complete = ++.to ∘ complete
    }
    where
    module X = Enum (pred-enum x)
    module Y = Enum (pred-enum y)

    xlist = List.map (_, y) X.list
    ylist = List.map (x ,_) Y.list

    module ++ {p} {P : Pred _ p} = ↔ (++↔ {P = P} {xlist} {ylist})
    module M {a p} {A : Set a} {P : Pred (Position (suc n)) p}
             {f : A → _} {xs : List _} =
      ↔ (map↔ {P = P} {f} {xs})

    xconsistent : ∀ {p} → p ∈ xlist → p Touches↘ q
    xconsistent elem
      with satisfied (Any.map (PEq.cong proj₂) (M.from elem))
    xconsistent elem | _ , refl =
      east (X.consistent (Any.map (PEq.cong proj₁) (M.from elem)))

    yconsistent : ∀ {p} → p ∈ ylist → p Touches↘ q
    yconsistent elem
      with satisfied (Any.map (PEq.cong proj₁) (M.from elem))
    yconsistent elem | proj₃ , refl =
      south (Y.consistent (Any.map (PEq.cong proj₂) (M.from elem)))

    complete : ∀ {p} → p Touches↘ q → p ∈ xlist ⊎ p ∈ ylist
    complete (east s) =
      inj₁ (M.to (Any.map (PEq.cong (_, y)) (X.complete s)))
    complete (south s) =
      inj₂ (M.to (Any.map (PEq.cong (x ,_)) (Y.complete s)))

  _Touches_ : Rel (Position (suc n)) lzero
  _Touches_ = Sym _Touches↘_

  _Touches-enum : (p : Position (suc n)) → Enum (p Touches_)
  _Touches-enum p = p Touches↘-enum ∪-enum p Touches↖-enum

  On_,_Touches_ : Board (suc n) → Rel (Position (suc n)) lzero
  On b , p Touches q = p Touches q × b p ≡ b q

  On_,_Touches-enum : (b : Board (suc n)) (p : Position (suc n)) →
                      Enum (On b , p Touches_)
  On b , p Touches-enum = p Touches-enum ∩-enum (λ q → b p ≟c b q)

  On_,_ConnectsTo_ : Board (suc n) → Rel (Position (suc n)) lzero
  On b , p ConnectsTo q = Star (On b ,_Touches_) p q

  -- Hard problem.
  On_,_ConnectsTo-enum : (b : Board (suc n)) (p : Position (suc n)) →
                         Enum (On b , p ConnectsTo_)
  On b , p ConnectsTo-enum = record
    { list = {!List.map proj₁ (go (n * n) [] ((p , ε) ∷ []))!}
    ; consistent = {!!}
    ; complete = {!!}
    }
    where
    go : ℕ → (hist : List (∃ λ q → On b , p ConnectsTo q))
         (queue : List (∃ λ q → On b , p ConnectsTo q)) →
         Maybe (List (∃ λ q → On b , p ConnectsTo q))
    go t hs [] = just hs
    go t hs (q ∷ qs) with any (proj₁ q ≟p_) (List.map proj₁ hs)
    ... | yes p = go t hs qs
    go zero hs (q ∷ qs) | no ¬p = nothing
    go (suc t) hs (q ∷ qs) | no ¬p =
      go t (q ∷ hs)
         (map-with-∈ list (λ {x} x∈ → x , proj₂ q ◅◅ consistent x∈ ◅ ε) ++ qs)
      -- TODO: Star should associate the other way, like Starˡ.
      where open Enum (On b , (proj₁ q) Touches-enum)

  record On_,_ReachesPos_ (b : Board (suc n)) (p r : Position (suc n))
                          : Set lzero where
    constructor _◄_
    field
      {q} : Position (suc n)
      adj : q Touches r
      adjs : On b , p ConnectsTo q

  record On_,_Reaches_ (b : Board (suc n)) (p : Position (suc n))
                       (c : Colour) : Set lzero where
    constructor reaches
    field
      {q} : Position (suc n)
      {colour} : True (c ≟c b q)
      reachesPos : On b , p ReachesPos q

  On_,_ReachesPos-enum : (b : Board (suc n)) (p : Position (suc n)) →
                         Enum (On b , p ReachesPos_)
  On b , p ReachesPos-enum = Enum→ equiv enum
    where
    equiv : ∀ {r} →
      (∃ λ q → On b , p ConnectsTo q × q Touches r) ⇔ On b , p ReachesPos r
    equiv {r} = record
      { to = →-to-⟶ (λ { (q , ts , t) → t ◄ ts })
      ; from = →-to-⟶ (λ { (t ◄ ts) → _ , ts , t })
      }

    enum = On b , p ConnectsTo-enum >>=-enum (λ q → q Touches-enum)

  On_,_Reaches-enum : (b : Board (suc n)) (p : Position (suc n)) →
                      Enum (On b , p Reaches_)
  On b , p Reaches-enum = Enum→ equiv enum
    where
    equiv : ∀ {c} →
      (∃ λ q → c ≡ b q × On b , p ReachesPos q) ⇔ On b , p Reaches c
    equiv {c} = record
      { to = →-to-⟶
        λ { (q , colour , reachesPos) →
            reaches {colour = fromWitness colour} reachesPos
          }
      ; from = →-to-⟶
        λ { (reaches {colour = colour} reachesPos) →
            _ , toWitness colour , reachesPos
          }
      }

    enum = image-enum b (On b , p ReachesPos-enum)

  On_,_Reaches?_ : (b : Board (suc n)) (p : Position (suc n))
                   (c : Colour) → Dec (On b , p Reaches c)
  On_,_Reaches?_ b p = Enum→Dec _≟c_ (On b , p Reaches-enum)
