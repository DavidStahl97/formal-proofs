module Algebra.Naturals.Excercises where
  open import Algebra.Naturals.Addition

  +-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
  +-rearrange m n p q = begin
    (m + n) + (p + q) ≡⟨ assoc ℕ-+-IsSemigroup m n (p + q) ⟩
    m + (n + (p + q)) ≡⟨ cong (λ a → m + a) (sym (assoc ℕ-+-IsSemigroup n p q)) ⟩
    m + ((n + p) + q) ≡⟨ sym (assoc ℕ-+-IsSemigroup m (n + p) q) ⟩
    (m + (n + p)) + q ∎

  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap m n p = begin
    m + (n + p) ≡⟨ +-comm m (n + p) ⟩
    (n + p) + m ≡⟨ assoc ℕ-+-IsSemigroup n p m ⟩
    n + (p + m) ≡⟨ cong (λ a → n + a) (+-comm p m) ⟩
    n + (m + p) ∎