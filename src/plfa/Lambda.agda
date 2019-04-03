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
