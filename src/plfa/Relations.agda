module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-suc; *-comm; +-assoc)
import plfa.Induction as Ind
open Ind using (Bin; nil; c0_; c1_; inc; to; from; fromToIsId)


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

*-rightMono-≤ : ∀(n m k : ℕ) → m ≤ k → n * m ≤ n * k
*-rightMono-≤ zero m k m≤k = z≤n
*-rightMono-≤ (suc n) m k m≤k = +-mono-≤ m k (n * m) (n * k) m≤k (*-rightMono-≤ n m k m≤k)

*-leftMono-≤ : ∀(n m k : ℕ) → m ≤ k → m * n ≤ k * n
*-leftMono-≤ n m k m≤k rewrite *-comm m n | *-comm k n = *-rightMono-≤ n m k m≤k

*-mono-≤ : ∀(n m p q : ℕ)
         → n ≤ m
         → p ≤ q
         → n * p ≤ m * q
*-mono-≤ n m p q n≤m p≤q = ≤-trans (*-leftMono-≤ p n m n≤m) (*-rightMono-≤ m p q p≤q)

data _<_ : ℕ → ℕ → Set where
  z<s : ∀{n : ℕ}
      → zero < suc n
  s<s : ∀{n m : ℕ}
      → n < m
      → suc n < suc m

infix 4 _<_

<-trans : ∀{n m k : ℕ} → n < m → m < k → n < k
<-trans z<s (s<s m<k) = z<s
<-trans (s<s n<m) (s<s m<k) = s<s (<-trans n<m m<k)

<-weak-tricho : ∀(n m : ℕ) →  n < m
                           or n ≡ m
                           or m < n
<-weak-tricho zero zero = left (right refl)
<-weak-tricho zero (suc _) = left (left z<s)
<-weak-tricho (suc _) zero = right z<s
<-weak-tricho (suc n) (suc m)
    with <-weak-tricho n m
...    | left (left p) = left (left (s<s p))
...    | left (right p) = left (right (cong suc p))
...    | right p = right (s<s p)

<-suc : ∀{n : ℕ} → n < suc n
<-suc {zero} = z<s
<-suc {suc n} = s<s <-suc

<-suc-mono : ∀{n m : ℕ} → n < m → n < suc m
<-suc-mono z<s = z<s
<-suc-mono (s<s n<m) = s<s (<-suc-mono n<m)

+-rightMono-< : (n m k : ℕ) → m < k → n + m < n + k
+-rightMono-< zero m k m<k = m<k
+-rightMono-< (suc n) m k m<k = s<s (+-rightMono-< n m k m<k)

+-leftMono-< : ∀(n m k : ℕ) → m < k → m + n < k + n
+-leftMono-< n m k m<k rewrite +-comm m n | +-comm k n = +-rightMono-< n m k m<k

+-mono-< : ∀(n m p q : ℕ)
         → n < m
         → p < q
         → n + p < m + q
+-mono-< n m p q n<m p<q = <-trans (+-leftMono-< p n m n<m) (+-rightMono-< m p q p<q)

≤-implies-< : ∀{n m : ℕ} → suc n ≤ m → n < m
≤-implies-< {zero} {.(suc _)} (s≤s sn≤m) = z<s
≤-implies-< {suc n} {.(suc _)} (s≤s sn≤m) = s<s (≤-implies-< sn≤m)

<-implies-≤ : ∀{n m : ℕ} → n < m → suc n ≤ m
<-implies-≤ {.0} {.(suc _)} z<s = s≤s z≤n
<-implies-≤ {.(suc _)} {.(suc _)} (s<s n<m) = s≤s (<-implies-≤ n<m)

≤-suc : ∀{n : ℕ} → n ≤ suc n
≤-suc {zero} = z≤n
≤-suc {suc n} = s≤s ≤-suc

<-trans' : ∀{n m k : ℕ} → n < m → m < k → n < k
<-trans' n<m m<k = ≤-implies-< (≤-trans (≤-trans (<-implies-≤ n<m) ≤-suc) (<-implies-≤ m<k))

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀{n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀{n : ℕ} → even n → odd (suc n)

e+e≡e : ∀{n m : ℕ} → even n → even m → even (n + m)
o+e≡e : ∀{n m : ℕ} → odd n → even m → odd (n + m)

e+e≡e zero em = em
e+e≡e (suc on) em = suc (o+e≡e on em)

o+e≡e (suc en) em = suc (e+e≡e en em)

o+o≡e : ∀{n m : ℕ} → odd n → odd m → even (n + m)
o+o≡e {suc n} {suc m} (suc en) (suc em) rewrite +-suc n m = suc (suc (e+e≡e en em))

data One : Bin → Set where
  nil : One (c1 nil)
  c0_ : ∀{x : Bin} → One x → One (c0 x)
  c1_ : ∀{x : Bin} → One x → One (c1 x)

data Can : Bin → Set where
  zero : Can (c0 nil)
  leading : ∀{x : Bin} → One x → Can x

inc-one : ∀{x : Bin} → One x → One (inc x)
inc-one nil = c0_ nil
inc-one (c0 ox) = c1 ox
inc-one (c1 ox) = c0 (inc-one ox)

inc-canon : ∀{x : Bin} → Can x → Can (inc x)
inc-canon zero = leading nil
inc-canon (leading cx) = leading (inc-one cx)

to-can : ∀(n : ℕ) → Can (to n)
to-can zero = zero
to-can (suc n) = inc-canon (to-can n)


-- WTF???
l : ∀(n : ℕ) → 0 < n → to (2 * n) ≡ c0 (to n)
l (suc n) z<s rewrite +-comm n (suc (n + 0))
                    | +-comm (n + 0) n = ?

_+-bin_ : Bin → Bin → Bin
nil +-bin y = y
(c0 x) +-bin nil = c0 x
(c0 x) +-bin (c0 y) = c0 (x +-bin y)
(c0 x) +-bin (c1 y) = c1 (x +-bin y)
(c1 x) +-bin nil = c1 x
(c1 x) +-bin (c0 y) = c1 (x +-bin y)
(c1 x) +-bin (c1 y) = c0 (inc (x +-bin y))

infixl 6 _+-bin_

+-bin-left-zero : ∀(x : Bin) → Can x → c0 nil +-bin x ≡ x
+-bin-left-zero .(c0 nil) zero = refl
+-bin-left-zero .(c1 nil) (leading nil) = refl
+-bin-left-zero .(c0 _) (leading (c0 ox)) = refl
+-bin-left-zero .(c1 _) (leading (c1 ox)) = refl

+-bin-left-inc : ∀(x y : Bin) → inc x +-bin y ≡ inc (x +-bin y)
+-bin-left-inc nil nil = refl
+-bin-left-inc nil (c0 y) = refl
+-bin-left-inc nil (c1 y) = refl
+-bin-left-inc (c0 x) nil = refl
+-bin-left-inc (c0 x) (c0 y) = refl
+-bin-left-inc (c0 x) (c1 y) = refl
+-bin-left-inc (c1 x) nil = refl
+-bin-left-inc (c1 x) (c0 y) rewrite +-bin-left-inc x y = refl
+-bin-left-inc (c1 x) (c1 y) rewrite +-bin-left-inc x y = refl

to-homo : ∀(n m : ℕ) → to (n + m) ≡ to n +-bin to m
to-homo zero m rewrite +-bin-left-zero (to m) (to-can m) = refl
to-homo (suc n) m
  rewrite to-homo n m
        | sym (+-bin-left-inc (to n) (to m)) = refl

x+-bin-x-is-shift : ∀(x : Bin) → One x → x +-bin x ≡ c0 x
x+-bin-x-is-shift .(c1 nil) nil = refl
x+-bin-x-is-shift (c0 x) (c0 ox) rewrite x+-bin-x-is-shift x ox = refl
x+-bin-x-is-shift (c1 x) (c1 ox) rewrite x+-bin-x-is-shift x ox = refl

to-from-id-one : ∀(x : Bin) → One x → to (from x) ≡ x
to-from-id-one .(c1 nil) nil = refl
to-from-id-one (c0 x) (c0 ox)
  rewrite +-comm (from x) 0
        | to-homo (from x) (from x)
        | to-from-id-one x ox = x+-bin-x-is-shift x ox
to-from-id-one (c1 x) (c1 ox)
  rewrite +-comm (from x) 0
        | to-homo (from x) (from x)
        | to-from-id-one x ox
        | x+-bin-x-is-shift x ox = refl

to-from-id-can : ∀{x : Bin} → Can x → to (from x) ≡ x
to-from-id-can zero = refl
to-from-id-can {x} (leading ox) = to-from-id-one x ox
