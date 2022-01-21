module Algebra.Naturals.Addition where  
  open import Algebra.Naturals.Definition public

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

  infixl 6 _+_

  +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc zero n p = refl
  +-assoc (suc m) n p = cong suc (+-assoc m n p)

  +-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc' zero n p = begin
    (zero + n) + p ≡⟨⟩
    n + p ≡⟨⟩
    zero + (n + p) ∎
  +-assoc' (suc m) n p = begin
    (suc m + n) + p ≡⟨⟩
    suc (m + n) + p ≡⟨⟩
    suc ((m + n) + p) ≡⟨ cong suc (+-assoc' m n p) ⟩
    suc (m + (n + p)) ∎

  {- Semigroup -} 
  ℕ-+-IsSemigroup : IsSemigroup _+_
  assoc ℕ-+-IsSemigroup = +-assoc

  ℕ-+-Semigroup : Semigroup
  Carrier ℕ-+-Semigroup = ℕ
  _·_ ℕ-+-Semigroup = _+_
  isSemigroup ℕ-+-Semigroup = ℕ-+-IsSemigroup

  {- Identity -}
  +-right-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-right-identity zero = refl
  +-right-identity (suc n) = cong suc (+-right-identity n)

  +-left-identity : ∀ (m : ℕ) → zero + m ≡ m
  +-left-identity m = refl

  ℕ-+-HasIdentity : Identity _+_ 0
  left ℕ-+-HasIdentity = +-left-identity
  right ℕ-+-HasIdentity = +-right-identity

  {- Monoid -}
  ℕ-+-IsMonoid : IsMonoid _+_ 0
  semigroup ℕ-+-IsMonoid = ℕ-+-IsSemigroup
  identity ℕ-+-IsMonoid = ℕ-+-HasIdentity

  ℕ-+-Monoid : Monoid
  Carrier ℕ-+-Monoid = ℕ
  _·_ ℕ-+-Monoid = _+_
  e ℕ-+-Monoid = 0
  isMonoid ℕ-+-Monoid = ℕ-+-IsMonoid

  {- Commutative Monoid -}
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero = +-right-identity m
  +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

  +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm' m zero = +-right-identity m
  +-comm' m (suc n) = begin
      (m + suc n) ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m) ∎

  ℕ-+-IsCommutativeMonoid : IsCommutativeMonoid _+_ 0
  monoid ℕ-+-IsCommutativeMonoid = ℕ-+-IsMonoid
  comm ℕ-+-IsCommutativeMonoid = +-comm

  {- Additional Theorems -}
  +-add1ᵣ : ∀ (m : ℕ) → m + 1 ≡ suc m
  +-add1ᵣ zero = refl
  +-add1ᵣ (suc m) = cong suc (+-add1ᵣ m)

  +-add1ₗ : ∀ (m : ℕ) → 1 + m ≡ suc m
  +-add1ₗ m = refl 