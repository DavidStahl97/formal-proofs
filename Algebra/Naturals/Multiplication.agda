module Algebra.Naturals.Multiplication where
  open import Algebra.Naturals.Addition

  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = (a * b) + b

  infixl 7 _*_

  *-zero : ∀ (m : ℕ) → m * zero ≡ zero
  *-zero zero = refl
  *-zero (suc m) = begin
    suc m * zero ≡⟨⟩
    m * zero + zero ≡⟨ +-right-identity (m * zero) ⟩
    m * zero ≡⟨ *-zero m ⟩
    zero ∎

  {- Identity -}
  ℕ-*-right-identity : ∀ (m : ℕ) → m * 1 ≡ m
  ℕ-*-right-identity zero = refl
  ℕ-*-right-identity (suc m) = begin
    suc m * 1 ≡⟨⟩
    m * 1 + 1 ≡⟨ cong (λ a → a + 1) (ℕ-*-right-identity m) ⟩
    m + 1 ≡⟨ +-add1ᵣ m ⟩
    suc m ∎

  ℕ-*-left-identity : ∀ (m : ℕ) → 1 * m ≡ m
  ℕ-*-left-identity m = refl

  ℕ-*-HasIdentity : Identity _*_ 1
  left ℕ-*-HasIdentity = ℕ-*-left-identity
  right ℕ-*-HasIdentity = ℕ-*-right-identity

  {- Distributivity -}
  *-distrib-+ᵣ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ᵣ zero n p = refl
  *-distrib-+ᵣ (suc m) n p = begin
    (suc m + n) * p ≡⟨⟩
    suc (m + n) * p ≡⟨⟩
    (m + n) * p + p ≡⟨ cong (λ a → a + p) (*-distrib-+ᵣ m n p) ⟩
    m * p + n * p + p ≡⟨ swap021 ℕ-+-IsCommutativeMonoid (m * p) (n * p) p ⟩
    m * p + p + n * p ≡⟨ cong (λ a → m * p + a + n * p) (ℕ-*-left-identity p) ⟩
    m * p + 1 * p + n * p ≡⟨ cong (λ a → a + n * p) (sym (*-distrib-+ᵣ m 1 p)) ⟩
    (m + 1) * p + n * p ≡⟨ cong (λ a → a * p + n * p) (+-add1ᵣ m) ⟩
    suc m * p + n * p ∎

  *-distrib-+ₗ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
  *-distrib-+ₗ zero n p = refl
  *-distrib-+ₗ (suc m) n p = begin
    suc m * (n + p) ≡⟨⟩
    m * (n + p) + (n + p) ≡⟨ cong (λ a → a + (n + p)) (*-distrib-+ₗ m n p) ⟩
    m * n + m * p + (n + p) ≡⟨ swap021 ℕ-+-IsCommutativeMonoid (m * n) (m * p) (n + p) ⟩
    m * n + (n + p) + m * p ≡⟨ cong (λ a → a + m * p) (sym (assoc ℕ-+-IsSemigroup (m * n) n p)) ⟩
    m * n + n + p + m * p ≡⟨ swap021 ℕ-+-IsCommutativeMonoid (m * n + n) p (m * p) ⟩
    m * n + n + m * p + p ≡⟨⟩
    m * n + 1 * n + m * p + 1 * p ≡⟨ cong (λ a → a + m * p + 1 * p) (sym (*-distrib-+ᵣ m 1 n)) ⟩
    (m + 1) * n + m * p + 1 * p ≡⟨ assoc ℕ-+-IsSemigroup ((m + 1) * n) (m * p) (1 * p) ⟩
    (m + 1) * n + (m * p + 1 * p) ≡⟨ cong (λ a → (m + 1) * n + a) (sym (*-distrib-+ᵣ m 1 p)) ⟩
    (m + 1) * n + (m + 1) * p ≡⟨ cong (λ a → a * n + (m + 1) * p) (+-add1ᵣ m) ⟩
    suc m * n + (m + 1) * p ≡⟨ cong (λ a → suc m * n + a * p) (+-add1ᵣ m) ⟩
    suc m * n + suc m * p ∎

  {- Semigroup -}
  *-assoc : associative _*_
  *-assoc zero n p = refl
  *-assoc (suc m) n p = begin
    (suc m * n) * p ≡⟨⟩
    (m * n + n) * p ≡⟨ *-distrib-+ᵣ (m * n) n p ⟩
    m * n * p + n * p ≡⟨⟩
    m * n * p + 1 * (n * p) ≡⟨ cong (λ a → a + 1 * (n * p)) (*-assoc m n p) ⟩
    m * (n * p) + 1 * (n * p) ≡⟨ sym (*-distrib-+ᵣ m 1 (n * p)) ⟩
    (m + 1) * (n * p) ≡⟨ cong (λ a → a * (n * p)) (+-add1ᵣ m) ⟩
    suc m * (n * p) ∎

  ℕ-*-IsSemigroup : IsSemigroup _*_
  assoc ℕ-*-IsSemigroup = *-assoc

  ℕ-*-Semigroup : Semigroup
  Carrier ℕ-*-Semigroup = ℕ
  _·_ ℕ-*-Semigroup = _*_
  isSemigroup ℕ-*-Semigroup = ℕ-*-IsSemigroup