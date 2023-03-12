module Dave.Algebra.Naturals.Definition where
  open import Dave.Relations.Module public
  open import Dave.Logic.Module public
  open import Dave.Algebra.Structures.Module public
  
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  one = suc zero
  two = suc one
  three = suc two
  four = suc three
  five = suc four
  six = suc five
  seven = suc six
  eight = suc seven
  nine = suc eight

  {-# BUILTIN NATURAL  ℕ #-} 

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