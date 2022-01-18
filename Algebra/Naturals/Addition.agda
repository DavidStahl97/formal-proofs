module Algebra.Naturals.Addition where
  open import Algebra.Naturals.Data
  open import Algebra.Equality  

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

  _∸_ : ℕ → ℕ → ℕ
  a ∸ zero = a
  zero ∸ suc b = zero
  suc a ∸ suc b = a ∸ b

  infixl 6 _+_ _∸_

  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-identity zero = refl
  +-identity (suc n) = cong suc (+-identity n)

  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero = +-identity m
  +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

  +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm' m zero = +-identity m
  +-comm' m (suc n) = begin
      (m + suc n) ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m) ∎
