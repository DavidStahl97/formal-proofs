module Algebra.Naturals.Addition where  
  open import Algebra.Naturals.Definition

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

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

  ℕ-+-Semigroup : Semigroup _+_
  assoc ℕ-+-Semigroup = +-assoc

  +-right-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-right-identity zero = refl
  +-right-identity (suc n) = cong suc (+-right-identity n)

  +-left-identity : ∀ (m : ℕ) → zero + m ≡ m
  +-left-identity m = refl

  ℕ-+-Monoid : Monoid _+_ 0
  semigroup ℕ-+-Monoid = ℕ-+-Semigroup
  left (identity ℕ-+-Monoid) = +-left-identity
  right (identity ℕ-+-Monoid) = +-right-identity

  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-add1ᵣ : ∀ (m : ℕ) → m + 1 ≡ suc m
  +-add1ᵣ zero = refl
  +-add1ᵣ (suc m) = cong suc (+-add1ᵣ m)

  +-add1ₗ : ∀ (m : ℕ) → 1 + m ≡ suc m
  +-add1ₗ m = refl

  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero = +-right-identity m
  +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

  +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm' m zero = +-right-identity m
  +-comm' m (suc n) = begin
      (m + suc n) ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m) ∎

{-
  +-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
  +-rearrange m n p q = begin
    (m + n) + (p + q) ≡⟨ assoc ℕ-+-Semigroup m n (p + q) ⟩
    m + (n + (p + q)) ≡⟨ cong (λ a → m + a) (sym (assoc ℕ-+-Semigroup n p q)) ⟩
    m + ((n + p) + q) ≡⟨ sym (assoc ℕ-+-Semigroup m (n + p) q) ⟩
    (m + (n + p)) + q ∎

  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap m n p = begin
    m + (n + p) ≡⟨ +-comm m (n + p) ⟩
    (n + p) + m ≡⟨ assoc ℕ-+-Semigroup n p m ⟩
    n + (p + m) ≡⟨ cong (λ a → n + a) (+-comm p m) ⟩
    n + (m + p) ∎

-}