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
  ℕ-+-Semigroup : Semigroup _+_
  assoc ℕ-+-Semigroup = +-assoc

  {- Monoid -}
  +-right-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-right-identity zero = refl
  +-right-identity (suc n) = cong suc (+-right-identity n)

  +-left-identity : ∀ (m : ℕ) → zero + m ≡ m
  +-left-identity m = refl

  ℕ-+-Monoid : Monoid _+_ 0
  semigroup ℕ-+-Monoid = ℕ-+-Semigroup
  left (identity ℕ-+-Monoid) = +-left-identity
  right (identity ℕ-+-Monoid) = +-right-identity

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

  ℕ-+-CommutativeMonoid : CommutativeMonoid _+_ 0
  monoid ℕ-+-CommutativeMonoid = ℕ-+-Monoid
  comm ℕ-+-CommutativeMonoid = +-comm

  {- Additional Theorems -}
  +-add1ᵣ : ∀ (m : ℕ) → m + 1 ≡ suc m
  +-add1ᵣ zero = refl
  +-add1ᵣ (suc m) = cong suc (+-add1ᵣ m)

  +-add1ₗ : ∀ (m : ℕ) → 1 + m ≡ suc m
  +-add1ₗ m = refl