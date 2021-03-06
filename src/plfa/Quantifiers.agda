module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (¬_)
open import Function using (_∘_; id)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≼_; extensionality)

open import plfa.Negation using (⊎-elim)
open import plfa.Induction using (Bin; to; from; fromToIsId)
open import plfa.Relations using (One; Can; to-from-id-can; to-can)

∀-elim : ∀{A : Set} {B : A → Set}
       → (L : ∀(x : A) → B x)
       → (M : A)
       → (B M)
∀-elim = id

∀-distrib-× : ∀{A : Set} {B C : A → Set}
            → (∀(x : A) → B x × C x) ≃ (∀(x : A) → B x) × (∀(x : A) → C x)
∀-distrib-× =
  record { to = λ ∀xBx×Cx → ⟨ proj₁ ∘ ∀xBx×Cx , proj₂ ∘ ∀xBx×Cx ⟩
         ; from = λ{ ⟨ ∀xBx , ∀xCx ⟩ x → ⟨ ∀xBx x , ∀xCx x ⟩}
         ; from∘to = refl
         ; to∘from = refl
         }

⊎∀-implies-∀⊎ : ∀{A : Set} {B C : A → Set}
              → (∀(x : A) → B x) ⊎ (∀(x : A) → C x)
              → ∀(x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ ∀xBx) x = inj₁ (∀xBx x)
⊎∀-implies-∀⊎ (inj₂ ∀xCx) x = inj₂ (∀xCx x)

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- agda doesn't understand whether I'm talking about
-- _,_ from _×_ or from Σ
-- so I made this convenience synonym
Σtup : ∀{A : Set} {B : A → Set}
     → (x : A) → B x → Σ A B
Σtup = ⟨_,_⟩

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀{A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀{A C : Set} {B : A → Set}
       → (∀(x : A) → B x → C)
       → ∃[ x ] B x
       → C
∃-elim f ⟨ x , Bx ⟩ = f x Bx

∀∃-currying : ∀{A C : Set} {B : A → Set}
            → (∀(x : A) → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record { to = ∃-elim
         ; from = λ f x Bx → f ⟨ x , Bx ⟩
         ; from∘to = refl
         ; to∘from = extensionality λ{ ⟨ x , Bx ⟩ → refl}
         }

∃-distrib-⊎ : ∀{A : Set} {B C : A → Set}
            → ∃[ x ] (B x ⊎ C x) ≃ ∃[ x ] B x ⊎ ∃[ x ] C x
∃-distrib-⊎ =
  record { to = λ{ ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
                 ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩
                 }
         ; from = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
                   ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩
                   }
         ; from∘to = λ{ {⟨ x , inj₁ Bx ⟩} → refl
                      ; {⟨ x , inj₂ Cx ⟩} → refl
                      }
         ; to∘from = λ{ {inj₁ ⟨ x , Bx ⟩} → refl
                      ; {inj₂ ⟨ x , Cx ⟩} → refl
                      }
         }

∃×-implies-×∃ : ∀{A : Set} {B C : A → Set}
              → ∃[ x ] (B x × C x)
              → ∃[ x ] B x × ∃[ x ] C x
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

-- the converse is not true in general;
-- you have no way of knowing whether the x for which B x
-- is the same x for which C x

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀{n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀{n : ℕ} → odd n  → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ 0 , refl ⟩
even-∃ (even-suc ox)
  with odd-∃ ox
...  | ⟨ x/2 , refl ⟩ = ⟨ suc x/2 , refl ⟩
odd-∃ (odd-suc ex)
  with even-∃ ex
...  | ⟨ x/2 , refl ⟩ = ⟨ x/2 , refl ⟩

∃-even : ∀{n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀{n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc x , refl ⟩ = even-suc (∃-odd ⟨ x , refl ⟩)
∃-odd ⟨ x , refl ⟩ = odd-suc (∃-even ⟨ x , refl ⟩)

even-∃' : ∀{n : ℕ} → even n → ∃[ m ] (    2 * m ≡ n)
odd-∃'  : ∀{n : ℕ} → odd n  → ∃[ m ] (1 + 2 * m ≡ n)

even-∃' even-zero = ⟨ zero , refl ⟩
even-∃' (even-suc ox)
  with odd-∃' ox
...  | ⟨ x , refl ⟩ = ⟨ suc x , cong suc (+-suc x (x + zero)) ⟩
odd-∃' (odd-suc ex)
  with even-∃' ex
...  | ⟨ x , refl ⟩ = ⟨ x , refl ⟩

∃-+-≤ : ∀(n m : ℕ) → n ≤ m → ∃[ k ] (k + n ≡ m)
∃-+-≤ n m z≤n = ⟨ m , +-comm m zero ⟩
∃-+-≤ (suc n) (suc m) (s≤s n≤m)
  with ∃-+-≤ n m n≤m
...  | ⟨ k , refl ⟩ = ⟨ k , +-suc k n ⟩

¬∃≅∀¬ : ∀{A : Set} {B : A → Set}
      → ¬ ∃[ x ] B x ≃ (∀(x : A) → ¬ B x)
¬∃≅∀¬ =
  record { to = λ{ ¬∃B x Bx → ¬∃B ⟨ x , Bx ⟩}
         ; from = λ{ f ⟨ x , Bx ⟩ → f x Bx}
         ; from∘to = extensionality λ{ ⟨ x , Bx ⟩ → refl}
         ; to∘from = refl
         }

∃¬-implies-¬∀ : ∀{A : Set} {B : A → Set}
              → Σ[ x ∈ A ] (¬ B x)
              → ¬ (∀(x : A) → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ f = ¬Bx (f x)

-- this probably has a better name
Functional : ∀{A : Set} → (A → Set) → Set
Functional {A} B = ∀{x : A} → (bx1 : B x) → (bx2 : B x) → bx1 ≡ bx2

one-functional : Functional One
one-functional One.nil One.nil = refl
one-functional One.nil (One.c1 ())
one-functional (One.c0 ox1) (One.c0 ox2) = cong (One.c0_) (one-functional ox1 ox2)
one-functional (One.c1 ()) One.nil
one-functional (One.c1 ox1) (One.c1 ox2) = cong (One.c1_) (one-functional ox1 ox2)

can-functional : Functional Can
can-functional Can.zero Can.zero = refl
can-functional Can.zero (Can.leading (One.c0 ()))
can-functional (Can.leading (One.c0 ())) Can.zero
can-functional (Can.leading ox1) (Can.leading ox2) = sym (cong Can.leading (one-functional ox2 ox1))

-- this probably has a better name
-- and can be generalized, or is just a usage of "subst" which I don't understand
Σ-functional : ∀{A : Set} {B : A → Set} {x y : A}
             → x ≡ y
             → Functional B
             → (Bx : B x)
             → (By : B y)
             → Σtup x Bx ≡ Σtup y By
Σ-functional refl fnb Bx By rewrite fnb Bx By = refl

ℕ≃∃Can : ℕ ≃ Σ[ x ∈ Bin ] (Can x)
ℕ≃∃Can =
  record { to = λ n → ⟨ to n , to-can n ⟩
         ; from = λ{ ⟨ x , _ ⟩ → from x}
         ; from∘to = fromToIsId
         ; to∘from = λ{ {⟨ x , Canx ⟩} → Σ-functional (to-from-id-can Canx)
                                                      can-functional
                                                      (to-can (from x))
                                                      Canx }
         }
