module plfa.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{A : Set} {x y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
trans refl refl = refl

cong : ∀{A B : Set} {x y : A} {f : A -> B}
     → x ≡ y → f x ≡ f y
cong refl = refl

cong2 : ∀ {A B C : Set}
          {x y : A}
          {u v : B}
          {f : A -> B -> C}
      → x ≡ y
      → u ≡ v
      → f x u ≡ f y v
cong2 refl refl = refl

cong-app : ∀ {A B : Set}
             {x : A}
             {f : A → B}
             {g : A → B}
         → f ≡ g
         → f x ≡ g x
cong-app refl = refl

subst : ∀ {A : Set}
          {p : A -> Set}
          {x y : A}
      → x ≡ y
      → p x
      → p y
subst refl px = px

module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ {y : A} (x : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀{y z : A} (x : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _ ∎ = refl

open ≡-Reasoning


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-comm : ∀ (n m : ℕ) → n + m ≡ m + n

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀{n : ℕ}
      → zero ≤ n
  s≤s : ∀{n m : ℕ}
      → n ≤ m
      → suc n ≤ suc m

postulate
  ≤-trans : ∀{n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
  ≤-refl : ∀{n : ℕ} → n ≤ n

infix 4 _≤_

module ≤-Reasoning where

  infix 1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _qed

  ≤-begin_ : ∀ {n m : ℕ} → n ≤ m → n ≤ m
  ≤-begin n≤m = n≤m

  _≤⟨⟩_ : ∀ {m : ℕ} (n : ℕ) → n ≤ m → n ≤ m
  _ ≤⟨⟩ n≤m = n≤m

  _≤⟨_⟩_ : ∀{m k : ℕ} (n : ℕ) → n ≤ m → m ≤ k → n ≤ k
  _ ≤⟨ n≤m ⟩ m≤k = ≤-trans n≤m m≤k

  _qed : ∀ (n : ℕ) → n ≤ n
  _ qed = ≤-refl

open ≤-Reasoning

+-mono-right-≤ : ∀(n m k : ℕ) → m ≤ k → n + m ≤ n + k
+-mono-right-≤ zero m k m≤k =
  ≤-begin
    zero + m
  ≤⟨⟩
    m
  ≤⟨ m≤k ⟩
    k
  qed
+-mono-right-≤ (suc n) m k m≤k =
  ≤-begin
    suc n + m
  ≤⟨⟩
    suc (n + m)
  ≤⟨ s≤s (+-mono-right-≤ n m k m≤k) ⟩
    suc (n + k)
  ≤⟨⟩
    suc n + k
  qed

≡-implies-≤ : ∀{n m : ℕ} → n ≡ m → n ≤ m
≡-implies-≤ {zero} {.zero} refl = z≤n
≡-implies-≤ {suc n} {.(suc n)} refl = s≤s (≡-implies-≤ refl)

+-mono-left-≤ : ∀ (n m k : ℕ) → m ≤ k → m + n ≤ k + n
+-mono-left-≤ n m k m≤k =
  ≤-begin
    m + n
  ≤⟨ ≡-implies-≤ (+-comm m n) ⟩
    n + m
  ≤⟨ +-mono-right-≤ n m k m≤k ⟩
    n + k
  ≤⟨ ≡-implies-≤ (+-comm n k) ⟩
    k + n
  qed

+-mono-≤ : ∀ (n m p q : ℕ) → n ≤ m → p ≤ q → n + p ≤ m + q
+-mono-≤ n m p q n≤m p≤q =
  ≤-begin
    n + p
  ≤⟨ +-mono-right-≤ n p q p≤q ⟩
    n + q
  ≤⟨ +-mono-left-≤ q n m n≤m ⟩
    m + q
  qed
