module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Level using (Level)

_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

postulate
  extensionality : ∀{A B : Set} {f g : A → B}
                 → (∀(x : A) → f x ≡ g x)
                 → f ≡ g

∘-assoc : ∀{A B C D : Set}
           {h : C → D}
           {g : B → C}
           {f : A → B}
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc = refl

_+'_ : ℕ → ℕ → ℕ
n +' zero  = n
n +' suc m = suc (n +' m)

same-app : ∀(n m : ℕ) → n +' m ≡ n + m
same-app n m rewrite +-comm n m = lemma n m
  where
    lemma : ∀ (n m : ℕ) → (n +' m) ≡ m + n
    lemma n (zero) = refl
    lemma n (suc m) = cong suc (lemma n m)

same : _+'_ ≡ _+_
same = extensionality (λ n → extensionality (λ m → same-app n m))

infix 0 _≈_
record _≈_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀{x : A} → from (to x) ≡ x
    to∘from : ∀{y : B} → to (from y) ≡ y
open _≈_

id : ∀{l : Level} {A : Set l} → A → A
id x = x

≈-refl : ∀{A : Set} → A ≈ A
≈-refl =
  record
    { to = id
    ; from = id
    ; from∘to = λ {x} → refl
    ; to∘from = λ {y} → refl
    }

≈-sym : ∀{A B : Set} → A ≈ B → B ≈ A
≈-sym A≈B =
  record
    { to = from A≈B
    ; from = to A≈B
    ; from∘to = to∘from A≈B
    ; to∘from = from∘to A≈B
    }

≈-trans : ∀{A B C : Set}
        → A ≈ B
        → B ≈ C
        → A ≈ C
≈-trans A≈B B≈C =
  record
    { to = to B≈C ∘ to A≈B
    ; from = from A≈B ∘ from B≈C
    ; from∘to = λ {x} →
        begin
          (from A≈B ∘ from B≈C) ((to B≈C ∘ to A≈B) x)
        ≡⟨⟩
          from A≈B (from B≈C (to B≈C (to A≈B x)))
        ≡⟨ cong (from A≈B) (from∘to B≈C) ⟩
          from A≈B (to A≈B x)
        ≡⟨ from∘to A≈B ⟩
          x
        ∎
    ; to∘from = λ {y} →
        begin
          (to B≈C ∘ to A≈B) ((from A≈B ∘ from B≈C) y)
        ≡⟨⟩
          to B≈C (to A≈B (from A≈B (from B≈C y)))
        ≡⟨ cong (to B≈C) (to∘from A≈B) ⟩
          to B≈C (from B≈C y)
        ≡⟨ to∘from B≈C ⟩
          y
        ∎
    }

module ≈-Reasoning where
  infix 1 ≈-begin_
  infixr 2 _≈⟨_⟩_
  infix 3 _≈-∎

  ≈-begin_ : ∀{A B : Set} → A ≈ B → A ≈ B
  ≈-begin_ = id

  _≈⟨_⟩_ : ∀{B C : Set} (A : Set) → A ≈ B → B ≈ C → A ≈ C
  _≈⟨_⟩_ = λ _ → ≈-trans

  _≈-∎ : ∀(A : Set) → A ≈ A
  A ≈-∎ = ≈-refl {A}

open ≈-Reasoning

infix 0 _≼_

record _≼_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀{x : A} → from (to x) ≡ x

open _≼_

≼-refl : ∀{A : Set} → A ≼ A
≼-refl =
  record
    { to = id
    ; from = id
    ; from∘to = λ {x} → refl
    }

≼-trans : ∀{A B C : Set} → A ≼ B → B ≼ C → A ≼ C
≼-trans A≼B B≼C =
  record
    { to = to B≼C ∘ to A≼B
    ; from = from A≼B ∘ from B≼C
    ; from∘to = λ {x} →
        begin
          (from A≼B ∘ from B≼C) ((to B≼C ∘ to A≼B) x)
        ≡⟨⟩
          from A≼B (from B≼C (to B≼C (to A≼B x)))
        ≡⟨ cong (from A≼B) (from∘to B≼C) ⟩
          from A≼B (to A≼B x)
        ≡⟨ from∘to A≼B ⟩
          x
        ∎
    }

≼-antisym : ∀{A B}
          → (A≼B : A ≼ B)
          → (B≼A : B ≼ A)
          → to A≼B ≡ from B≼A
          → from A≼B ≡ to B≼A
          → A ≈ B
≼-antisym A≼B B≼A refl refl =
  record
    { to = to A≼B
    ; from = from A≼B
    ; from∘to = from∘to A≼B
    ; to∘from = from∘to B≼A
    }

module ≼-Reasoning where
  infix 1 ≼-begin_
  infixr 2 _≼⟨_⟩_
  infix 3 _≼-∎

  ≼-begin_ : ∀{A B : Set} → A ≼ B → A ≼ B
  ≼-begin_ = id

  _≼⟨_⟩_ : ∀{B C : Set} (A : Set) → A ≼ B → B ≼ C → A ≼ C
  _≼⟨_⟩_ = λ _ → ≼-trans

  _≼-∎ : ∀(A : Set) → A ≼ A
  A ≼-∎ = ≼-refl {A}

open ≼-Reasoning
