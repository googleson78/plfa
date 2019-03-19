module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_; extensionality)


data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_
_++_ : ∀{A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

++-assoc : ∀{A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identity-right : ∀{A : Set} → {xs : List A} → xs ++ [] ≡ xs
++-identity-right {_} {[]} = refl
++-identity-right {_} {x ∷ xs} = cong (x ∷_) ++-identity-right

length : ∀{A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀{A : Set} (xs ys : List A)→ length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀{A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-commute : ∀{A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute [] ys = sym ++-identity-right
reverse-++-commute (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-commute xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀{A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-commute (reverse xs) [ x ] ⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

shunt : ∀{A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀{A : Set} → (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ x ∷ ys
  ≡⟨⟩
    reverse xs ++ [ x ] ++ ys
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

fast-reverse : ∀{A : Set} → List A → List A
fast-reverse xs = shunt xs []

fast-reverse-is-reverse : ∀{A : Set} → (xs : List A) → fast-reverse xs ≡ reverse xs
fast-reverse-is-reverse [] = refl
fast-reverse-is-reverse (x ∷ xs) = shunt-reverse xs [ x ]

map : ∀{A B : Set} → (A → B) → List A → List B
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-compose-pointful : ∀{A B C : Set}
                        (f : A → B) (g : B → C)
                        (xs : List A)
                     → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-pointful f g [] = refl
map-compose-pointful f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ∷_) (map-compose-pointful f g xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
  ≡⟨⟩
    g (f x) ∷ map g (map f xs)
  ≡⟨⟩
    map g (f x ∷ map f xs)
  ≡⟨⟩
    map g (map f (x ∷ xs))
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎

map-compose : ∀{A B C : Set}
               {f : A → B} {g : B → C}
            → map (g ∘ f) ≡ map g ∘ map f
map-compose {_} {_} {_} {f} {g} =
  begin
    map (g ∘ f)
  ≡⟨⟩
    map (λ x → g (f x))
  ≡⟨ extensionality (map-compose-pointful f g) ⟩
    (λ xs → map g (map f xs))
  ≡⟨⟩
    (map g) ∘ (map f)
  ∎

map-homomorphic-++ : ∀{A B : Set} (f : A → B) (xs ys : List A)
                    → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-homomorphic-++ f [] ys = refl
map-homomorphic-++ f (x ∷ xs) ys =
  begin
    map f (x ∷ xs ++ ys)
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-homomorphic-++ f xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨⟩
    (f x ∷ map f xs) ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-tree : ∀{A B C D : Set}
         → (A → C) → (B → D)
         → Tree A B → Tree C D
map-tree f _ (leaf x) = leaf (f x)
map-tree f g (node l x r) = node (map-tree f g l) (g x) (map-tree f g r)

foldr : ∀{A B : Set} → (A → B → B) → B → List A → B
foldr _ v [] = v
foldr f v (x ∷ xs) = f x (foldr f v xs)

product : List ℕ → ℕ
product = foldr (_*_) 1

foldr-++ : ∀{A B : Set}
            (f : A → B → B) (v : B) (xs ys : List A)
         → foldr f (foldr f v ys) xs ≡ foldr f v (xs ++ ys)
foldr-++ f v [] ys = refl
foldr-++ f v (x ∷ xs) ys =
  begin
    foldr f (foldr f v ys) (x ∷ xs)
  ≡⟨⟩
    f x (foldr f (foldr f v ys) xs)
  ≡⟨ cong (f x) (foldr-++ f v xs ys) ⟩
    f x (foldr f v (xs ++ ys))
  ≡⟨⟩
    foldr f v (x ∷ xs ++ ys)
  ≡⟨⟩
    foldr f v ((x ∷ xs) ++ ys)
  ∎

map-is-foldr-pointful : ∀{A B : Set} {f : A → B} (xs : List A) → map f xs ≡ foldr (_∷_ ∘ f) [] xs
map-is-foldr-pointful {_} {_} {f} [] = refl
map-is-foldr-pointful {_} {_} {f} (x ∷ xs) =
  begin
    map f (x ∷ xs)
  ≡⟨⟩
    f x ∷ map f xs
  ≡⟨ cong (f x ∷_) (map-is-foldr-pointful xs) ⟩
    f x ∷ foldr (_∷_ ∘ f) [] xs
  ≡⟨⟩
    _∷_ (f x) (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    (_∷_ (f x)) (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    ((_∷_ ∘ f) x) (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    (_∷_ ∘ f) x (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    foldr (_∷_ ∘ f) [] (x ∷ xs)
  ∎

map-is-foldr : ∀{A B : Set} {f : A → B} → map f ≡ foldr (_∷_ ∘ f) []
map-is-foldr = extensionality map-is-foldr-pointful

fold-tree : ∀ {A B C : Set}
          → (A → C) → (C → B → C → C) → Tree A B → C
fold-tree f _ (leaf x) = f x
fold-tree f g (node l x r) = g (fold-tree f g l) x (fold-tree f g r)

map-tree-is-fold-tree : ∀{A B C D : Set}
                      → (f : A → C) → (g : B → D)
                      → (t : Tree A B)
                      → map-tree f g t ≡ fold-tree (leaf ∘ f) (λ l x r → node l (g x) r) t
map-tree-is-fold-tree f g (leaf x) = refl
map-tree-is-fold-tree {A} {B} {C} {D} f g (node l x r) =
  begin
    map-tree f g (node l x r)
  ≡⟨⟩
    node (map-tree f g l) (g x) (map-tree f g r)
  ≡⟨ cong (λ l' → node l' (g x) (map-tree f g r)) (map-tree-is-fold-tree f g l) ⟩
    node (fold-tree f' g' l) (g x) (map-tree f g r)
  ≡⟨ cong (λ r' → node (fold-tree f' g' l) (g x) r') (map-tree-is-fold-tree f g r) ⟩
    node (fold-tree f' g' l) (g x) (fold-tree f' g' r)
  ≡⟨⟩
    fold-tree f' g' (node l x r)
  ∎
    where
      f' : ∀{D' : Set} → A → Tree C D'
      f' = leaf ∘ f
      g' : ∀{C' : Set} → Tree C' D → B → Tree C' D → Tree C' D
      g'  l x r = node l (g x) r
