module Algebra.Structures where
    open import Algebra.Equality

    op₁ : Set → Set
    op₁ A = A → A

    op₂ : Set → Set
    op₂ A = A → A → A

    associative : {A : Set} → op₂ A → Set
    associative _·_ = ∀ m n p → (m · n) · p ≡ m · (n · p)

    commutative : {A : Set} → op₂ A → Set
    commutative _·_ = ∀ m n → m · n ≡ n · m

    left-identity : {A : Set} → op₂ A → (e : A) → Set
    left-identity _·_ e = ∀ m → e · m ≡ m

    right-identity : {A : Set} → op₂ A → (e : A) → Set
    right-identity _·_ e = ∀ m → m · e ≡ m

    record Identity {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            left : left-identity _·_ e
            right : right-identity _·_ e

    open Identity public

    record Semigroup {A : Set} (_·_ : op₂ A) : Set where
        field
            assoc : associative _·_

    open Semigroup public

    record Monoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            semigroup : Semigroup _·_
            identity : Identity _·_ e

    open Monoid public
