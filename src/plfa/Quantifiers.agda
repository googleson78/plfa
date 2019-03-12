module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (¬_)
open import Function using (_∘_; id)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≼_; extensionality)

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
