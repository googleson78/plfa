module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀{n : ℕ}
      → zero ≤ n
  s≤s : ∀{n m : ℕ}
      → n ≤ m
      → suc n ≤ suc m

infix 4 _≤_

≤-refl : ∀{n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀{n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans z≤n _ = z≤n
≤-trans (s≤s nk) (s≤s mk) = s≤s (≤-trans nk mk)

≤-antisym : ∀{n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s nm) (s≤s mn) = cong suc (≤-antisym nm mn)

data _or_ (a b : Set) : Set where
  left : a → a or b
  right : b → a or b

infixl 1 _or_

≤-total : ∀{n m : ℕ} → n ≤ m or m ≤ n
≤-total {zero} {m} = left z≤n
≤-total {suc n} {zero} = right z≤n
≤-total {suc n} {suc m} with ≤-total
... | left p = left (s≤s p)
... | right p = right (s≤s p)

+-rightMono-≤ : ∀(n m k : ℕ) → m ≤ k → n + m ≤ n + k
+-rightMono-≤ zero _ _ m≤k = m≤k
+-rightMono-≤ (suc n) m k m≤k = s≤s (+-rightMono-≤ n m k m≤k)

+-leftMono-≤ : ∀(n m k : ℕ) → m ≤ k → m + n ≤ k + n
+-leftMono-≤ n m k m≤k rewrite +-comm m n | +-comm k n = +-rightMono-≤ n m k m≤k

+-mono-≤ : ∀(n m p q : ℕ)
         → n ≤ m
         → p ≤ q
         → n + p ≤ m + q
+-mono-≤ n m p q n≤m p≤q = ≤-trans (+-leftMono-≤ p n m n≤m) (+-rightMono-≤ m p q p≤q)
