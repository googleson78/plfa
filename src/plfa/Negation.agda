module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≼_; extensionality)

open import plfa.Relations using (_<_; z<s; s<s)

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

id : ∀{A : Set} → A → A
id x = x

¬-elim : ∀{A : Set} → ¬ A → A → ⊥
¬-elim = id

¬¬-intro : ∀{A : Set} → A → ¬ ¬ A
¬¬-intro x ¬x = ¬-elim ¬x x

¬¬¬-elim : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀{A B : Set} → (A → B) → ¬ B → ¬ A
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀{A : Set} → A → A → Set
A ≢ B = ¬ A ≡ B

_ : 1 ≢ 2
_ = λ ()

-- bogus
assimilation : ∀{A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x _ = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀{n : ℕ} → ¬ n < n
<-irreflexive (s<s n<n) = <-irreflexive n<n

<-s<s-preserves-¬ : ∀{n m : ℕ} → ¬ (n < m) → ¬ (suc n < suc m)
<-s<s-preserves-¬ ¬n<m (s<s n<m) = ¬n<m n<m

<-trichotomy : ∀{n m : ℕ}
             →   n < m × ¬ n ≡ m × ¬ m < n
             ⊎ ¬ n < m ×   n ≡ m × ¬ m < n
             ⊎ ¬ n < m × ¬ n ≡ m ×   m < n
<-trichotomy {zero} {zero} = inj₂ (inj₁ ⟨ (λ ()) , ⟨ refl , (λ ()) ⟩ ⟩)
<-trichotomy {zero} {suc m} = inj₁ ⟨ z<s , ⟨ (λ ()) , (λ ()) ⟩ ⟩
<-trichotomy {suc n} {zero} = inj₂ (inj₂ ⟨ (λ ()) , ⟨ (λ ()) , z<s ⟩ ⟩)
<-trichotomy {suc n} {suc m}
    with <-trichotomy {n} {m}
...    | inj₁ ⟨ n<m , ⟨ ¬n≡m , ¬m<n ⟩ ⟩ = inj₁ ⟨ s<s n<m , ⟨ (λ{ refl → ¬n≡m refl }) , <-s<s-preserves-¬ ¬m<n ⟩ ⟩
...    | inj₂ (inj₁ ⟨ ¬n<m , ⟨ refl , ¬m<n ⟩ ⟩) = inj₂ (inj₁ ⟨ <-irreflexive , ⟨ refl , <-irreflexive ⟩ ⟩)
...    | inj₂ (inj₂ ⟨ ¬n<m , ⟨ ¬n≡m , m<n ⟩ ⟩) = inj₂ (inj₂ ⟨ <-s<s-preserves-¬ ¬n<m , ⟨ (λ{ refl → ¬n≡m refl }) , s<s m<n ⟩ ⟩)
