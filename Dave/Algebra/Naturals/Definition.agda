module Dave.Algebra.Naturals.Definition where
  open import Dave.Core.Naturals public
  
  open import Dave.Relations.Module
  open import Dave.Logic.Module
  open import Dave.Algebra.Structures.Module  

  suc-≡ : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
  suc-≡ ≡-refl = ≡-refl

  suc≡→≡ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
  suc≡→≡ ≡-refl = ≡-refl

  suc-≠ : ∀ {m n : ℕ} → m ≠ n → suc m ≠ suc n
  suc-≠ m≠n suc-≡ = m≠n (suc≡→≡ suc-≡)

  0≠suc : ∀ {n : ℕ} → 0 ≠ suc n
  0≠suc ()

  suc≠0 : ∀ {n : ℕ} → suc n ≠ 0
  suc≠0 sucn=0 = 0≠suc (≡-sym sucn=0)

  ≡ℕ-ExcludedMiddle : ∀ (m n : ℕ) → ExcludedMiddle (m ≡ n)
  ≡ℕ-ExcludedMiddle zero zero = inj₁ ≡-refl
  ≡ℕ-ExcludedMiddle zero (suc n) = inj₂ λ{ () }
  ≡ℕ-ExcludedMiddle (suc m) zero = inj₂ λ{ () }
  ≡ℕ-ExcludedMiddle (suc m) (suc n) with ≡ℕ-ExcludedMiddle m n
  ≡ℕ-ExcludedMiddle (suc m) (suc n) | inj₁ m≡n = inj₁ (suc-≡ m≡n)
  ≡ℕ-ExcludedMiddle (suc m) (suc n) | inj₂ x = inj₂ (suc-≠ x)