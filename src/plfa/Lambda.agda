module plfa.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String)
open import Data.String.Unsafe using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  ‵suc_
infix  9  ‵_

data Term : Set where
  -- lambda
  ‵_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  -- consts
  ‵zero                   :  Term
  ‵suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

two : Term
two = ‵suc ‵suc ‵zero

plus : Term
plus = μ "+" ⇒ ƛ "n" ⇒ ƛ "m" ⇒
  case ‵ "n"
    [zero⇒ ‵zero
    |suc "n" ⇒ ‵suc (‵ "+" · ‵ "n" · ‵ "m")
    ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ‵ "s" · (‵ "s" · ‵ "z")

plusᶜ : Term
plusᶜ = ƛ "n" ⇒ ƛ "m" ⇒
  ƛ "s" ⇒ ƛ "z" ⇒ ‵ "n" · ‵ "s" · (‵ "m" · ‵ "s" · ‵ "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒
  ƛ "s" ⇒ ƛ "z" ⇒ ‵ "s" · (‵ "n" · ‵ "s" · ‵ "z")

one : Term
one = ‵suc ‵zero

-- TODO: unsure about the "+" application
mult : Term
mult = μ "*" ⇒ ƛ "n" ⇒ ƛ "m" ⇒
  case ‵ "n"
    [zero⇒ one
    |suc "n" ⇒ plus · ‵ "+" · ‵ "n" · (‵ "*" · ‵ "n" · ‵ "m")
    ]

-- TODO: check
multᶜ : Term
multᶜ = ƛ "n" ⇒ ƛ "m" ⇒
  ƛ "s" ⇒ ƛ "z" ⇒ ‵ "n" · (plusᶜ · ‵ "m") · (ƛ "s" ⇒ ƛ "z" ⇒ ‵ "z")

data Value : Term → Set where
  V-ƛ : ∀{x : Id} {N : Term} → Value (ƛ x ⇒ N)
  V-zero : Value ‵zero
  V-suc : ∀{V : Term} → Value V → Value (‵suc V)

infix 9 _[_:=_]
_[_:=_] : Term → Id → Term → Term
(‵ x) [ y := K ]
  with x ≟ y
...  | yes _ = K
...  | no  _ = ‵ x
(ƛ x ⇒ N) [ y := K ]
  with x ≟ y
...  | yes _ = ƛ x ⇒ N
...  | no  _ = ƛ x ⇒ N [ y := K ]
(N · M) [ y := K ] = N [ y := K ] · M [ y := K ]
‵zero [ y := K ] = ‵zero
(‵suc N) [ y := K ] = ‵suc N [ y := K ]
case N [zero⇒ M |suc n ⇒ K ] [ y := P ]
  with n ≟ y
...  | yes _ = case N [ y := P ] [zero⇒ M [ y := P ] |suc n ⇒ K ]
...  | no  _ = case N [ y := P ] [zero⇒ M [ y := P ] |suc n ⇒ K [ y := P ] ]

(μ x ⇒ N) [ y := K ]
  with x ≟ y
...  | yes _ = μ x ⇒ N
...  | no  _ = μ x ⇒ N [ y := K ]

infix 9 _[_:=_]'
_[_:=_]' : Term → Id → Term → Term
boundSubst : Id → Term → Id → Term → Term

(‵ x) [ y := K ]'
  with x ≟ y
...  | yes _ = K
...  | no  _ = ‵ x
(ƛ x ⇒ N) [ y := K ]' = ƛ x ⇒ boundSubst x N y K
(N · M) [ y := K ]' = N [ y := K ]' · M [ y := K ]'
‵zero [ y := K ]' = ‵zero
(‵suc N) [ y := K ]' = ‵suc N [ y := K ]'
case N [zero⇒ M |suc n ⇒ K ] [ y := P ]'
  = case N [ y := P ]' [zero⇒ M [ y := P ]'
                       |suc n ⇒ boundSubst n K y P
                       ]
(μ x ⇒ N) [ y := K ]' = μ x ⇒ boundSubst x N y K

boundSubst x N y K
  with x ≟ y
...  | yes _ = N
...  | no  _ = N [ y := K ]'
