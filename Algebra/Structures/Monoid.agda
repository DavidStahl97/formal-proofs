module Algebra.Structures.Monoid where
    open import Algebra.Structures.Semigroup public
    open import Algebra.Equality

    record Identity {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            left : left-identity _·_ e
            right : right-identity _·_ e

    record IsMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            semigroup : IsSemigroup _·_
            identity : Identity _·_ e
    
    record Monoid : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            e : Carrier
            isMonoid : IsMonoid _·_ e             

    record IsCommutativeMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            isSemigroup : IsSemigroup _·_
            leftIdentity : left-identity _·_ e
            comm : commutative _·_ 

        rightIdentity : right-identity _·_ e
        rightIdentity m = begin
            m · e ≡⟨ comm m e ⟩
            e · m ≡⟨ leftIdentity m ⟩
            m ∎

        identity : Identity _·_ e
        Identity.left identity = leftIdentity
        Identity.right identity = rightIdentity

        isMonoid : IsMonoid _·_ e
        IsMonoid.semigroup isMonoid = isSemigroup
        IsMonoid.identity isMonoid = identity

        swap021 : ∀ (m n p : A) → (m · n) · p ≡ (m · p) · n
        swap021 m n p = begin
            (m · n) · p ≡⟨ IsSemigroup.assoc isSemigroup m n p ⟩
            m · (n · p) ≡⟨ cong (λ a → m · a) (comm n p) ⟩
            m · (p · n) ≡⟨ sym (IsSemigroup.assoc isSemigroup m p n) ⟩
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
            p · (n · m) ≡⟨ sym (IsSemigroup.assoc isSemigroup p n m) ⟩
            (p · n) · m ∎

        swap201 : ∀ (m n p : A) → (m · n) · p ≡ (p · m) · n
        swap201 m n p = begin
            (m · n) · p ≡⟨ comm (m · n) p ⟩
            p · (m · n) ≡⟨ sym (IsSemigroup.assoc isSemigroup p m n) ⟩
            (p · m) · n ∎

    record CommutativeMonoid : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            e : Carrier
            isCommutativeMonoid : IsCommutativeMonoid _·_ e        