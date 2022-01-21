module Algebra.Structures.Monoid where
    open import Algebra.Structures.Semigroup public

    record Identity {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            left : left-identity _·_ e
            right : right-identity _·_ e

    open Identity public

    record IsMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            semigroup : IsSemigroup _·_
            identity : Identity _·_ e

    open IsMonoid public
    
    record Monoid : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            e : Carrier
            isMonoid : IsMonoid _·_ e             

    open Monoid public

    record IsCommutativeMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            monoid : IsMonoid _·_ e
            comm : commutative _·_ 

        swap021 : ∀ (m n p : A) → (m · n) · p ≡ (m · p) · n
        swap021 m n p = begin
            (m · n) · p ≡⟨ assoc (semigroup monoid) m n p ⟩
            m · (n · p) ≡⟨ cong (λ a → m · a) (comm n p) ⟩
            m · (p · n) ≡⟨ sym (assoc (semigroup monoid) m p n) ⟩
            (m · p) · n ∎

        swap102 : ∀ (m n p : A) → (m · n) · p ≡ (n · m) · p
        swap102 m n p = begin
            (m · n) · p ≡⟨ cong (λ a → a · p) (comm m n) ⟩
            (n · m) · p ∎

        swap120 : ∀ (m n p : A) → (m · n) · p ≡ (n · m) · p
        swap120 m n p = begin 
            (m · n) · p ≡⟨ cong (λ a → a · p) (comm m n) ⟩ 
            (n · m) · p ∎

        swap210 : ∀ (m n p : A) → (m · n) · p ≡ (p · n) · m
        swap210 m n p = begin
            (m · n) · p ≡⟨ comm (m · n) p ⟩
            p · (m · n) ≡⟨ cong (λ a → p · a) (comm m n) ⟩
            p · (n · m) ≡⟨ sym (assoc (semigroup monoid) p n m) ⟩
            (p · n) · m ∎

        swap201 : ∀ (m n p : A) → (m · n) · p ≡ (p · m) · n
        swap201 m n p = begin
            (m · n) · p ≡⟨ comm (m · n) p ⟩
            p · (m · n) ≡⟨ sym (assoc (semigroup monoid) p m n) ⟩
            (p · m) · n ∎

    open IsCommutativeMonoid public

    record CommutativeMonoid : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            e : Carrier
            isCommutativeMonoid : IsCommutativeMonoid _·_ e    

    open CommutativeMonoid public      