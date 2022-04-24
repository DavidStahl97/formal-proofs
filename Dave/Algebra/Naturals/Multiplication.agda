module Dave.Algebra.Naturals.Multiplication where
  open import Dave.Algebra.Naturals.Addition public

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
  Identity.left ℕ-*-HasIdentity = ℕ-*-left-identity
  Identity.right ℕ-*-HasIdentity = ℕ-*-right-identity

  {- Distributivity -}
  *-distrib-+ᵣ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ᵣ zero n p = refl
  *-distrib-+ᵣ (suc m) n p = begin
    (suc m + n) * p ≡⟨⟩
    suc (m + n) * p ≡⟨⟩
    (m + n) * p + p ≡⟨ cong (λ a → a + p) (*-distrib-+ᵣ m n p) ⟩
    m * p + n * p + p ≡⟨ IsCommutativeMonoid.swap021 ℕ-+-IsCommutativeMonoid (m * p) (n * p) p ⟩
    m * p + p + n * p ≡⟨ cong (λ a → m * p + a + n * p) (ℕ-*-left-identity p) ⟩
    m * p + 1 * p + n * p ≡⟨ cong (λ a → a + n * p) (sym (*-distrib-+ᵣ m 1 p)) ⟩
    (m + 1) * p + n * p ≡⟨ cong (λ a → a * p + n * p) (+-add1ᵣ m) ⟩
    suc m * p + n * p ∎

  *-distrib1ᵣ-+ᵣ : ∀ (m p : ℕ) → (m + 1) * p ≡ m * p + p
  *-distrib1ᵣ-+ᵣ m p = begin
    (m + 1) * p ≡⟨ *-distrib-+ᵣ m 1 p ⟩
    m * p + 1 * p ≡⟨⟩ 
    m * p + p ∎

  *-distrib1ₗ-+ᵣ : ∀ (m p : ℕ) → (1 + m) * p ≡ p + m * p
  *-distrib1ₗ-+ᵣ m p = begin 
    (1 + m) * p ≡⟨ *-distrib-+ᵣ 1 m p ⟩ 
    1 * p + m * p ≡⟨⟩
    p + m * p ∎

  *-distrib-+ₗ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
  *-distrib-+ₗ zero n p = refl
  *-distrib-+ₗ (suc m) n p = begin
    suc m * (n + p) ≡⟨⟩
    m * (n + p) + (n + p) ≡⟨ cong (λ a → a + (n + p)) (*-distrib-+ₗ m n p) ⟩
    m * n + m * p + (n + p) ≡⟨ IsCommutativeMonoid.swap021 ℕ-+-IsCommutativeMonoid (m * n) (m * p) (n + p) ⟩
    m * n + (n + p) + m * p ≡⟨ cong (λ a → a + m * p) (sym (IsSemigroup.assoc ℕ-+-IsSemigroup (m * n) n p)) ⟩
    m * n + n + p + m * p ≡⟨ IsCommutativeMonoid.swap021 ℕ-+-IsCommutativeMonoid (m * n + n) p (m * p) ⟩
    m * n + n + m * p + p ≡⟨⟩
    m * n + 1 * n + m * p + 1 * p ≡⟨ cong (λ a → a + m * p + 1 * p) (sym (*-distrib-+ᵣ m 1 n)) ⟩
    (m + 1) * n + m * p + 1 * p ≡⟨ IsSemigroup.assoc ℕ-+-IsSemigroup ((m + 1) * n) (m * p) (1 * p) ⟩
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
  IsSemigroup.assoc ℕ-*-IsSemigroup = *-assoc

  ℕ-*-Semigroup : Semigroup
  Semigroup.Carrier ℕ-*-Semigroup = ℕ
  Semigroup._·_ ℕ-*-Semigroup = _*_
  Semigroup.isSemigroup ℕ-*-Semigroup = ℕ-*-IsSemigroup

  {- Monoid -}
  ℕ-*-IsMonoid : IsMonoid _*_ 1
  IsMonoid.semigroup ℕ-*-IsMonoid = ℕ-*-IsSemigroup
  IsMonoid.identity ℕ-*-IsMonoid = ℕ-*-HasIdentity

  ℕ-*-Monoid : Monoid
  Monoid.Carrier ℕ-*-Monoid = ℕ
  Monoid._·_ ℕ-*-Monoid = _*_
  Monoid.e ℕ-*-Monoid = 1
  Monoid.isMonoid ℕ-*-Monoid = ℕ-*-IsMonoid

  {- Commutative Monoid -}
  ℕ-*-comm : commutative _*_
  ℕ-*-comm zero n = begin
    zero * n ≡⟨⟩
    zero ≡⟨ sym (*-zero n) ⟩
    n * zero ∎
  ℕ-*-comm (suc m) n = begin
    suc m * n ≡⟨⟩
    m * n + n ≡⟨ +-comm (m * n) n ⟩
    n + m * n ≡⟨ sym (cong (λ a → a + m * n) (ℕ-*-right-identity n)) ⟩
    n * 1 + m * n ≡⟨ cong (λ a → n * 1 + a) (ℕ-*-comm m n) ⟩
    n * 1 + n * m ≡⟨ sym (*-distrib-+ₗ n 1 m) ⟩
    n * (1 + m) ≡⟨⟩
    n * suc m ∎

  ℕ-*-IsCommutativeMonoid : IsCommutativeMonoid _*_ 1
  IsCommutativeMonoid.isSemigroup ℕ-*-IsCommutativeMonoid = ℕ-*-IsSemigroup
  IsCommutativeMonoid.leftIdentity ℕ-*-IsCommutativeMonoid = ℕ-*-left-identity
  IsCommutativeMonoid.comm ℕ-*-IsCommutativeMonoid = ℕ-*-comm

  ℕ-*-CommutativeMonoid : CommutativeMonoid
  CommutativeMonoid.Carrier ℕ-*-CommutativeMonoid = ℕ
  CommutativeMonoid._·_ ℕ-*-CommutativeMonoid = _*_
  CommutativeMonoid.e ℕ-*-CommutativeMonoid = 1
  CommutativeMonoid.isCommutativeMonoid ℕ-*-CommutativeMonoid = ℕ-*-IsCommutativeMonoid

  *-distrib1ᵣ-+ₗ : ∀ (m p : ℕ) → m * (p + 1) ≡ m * p + m
  *-distrib1ᵣ-+ₗ m p = begin
    m * (p + 1) ≡⟨ ℕ-*-comm m (p + 1) ⟩ 
    (p + 1) * m ≡⟨ *-distrib1ᵣ-+ᵣ p m ⟩
    p * m + m ≡⟨ cong (λ a → a + m) (ℕ-*-comm p m) ⟩
    m * p + m ∎

  *-distrib1ₗ-+ₗ : ∀ (m p : ℕ) → m * (1 + p) ≡ m + m * p
  *-distrib1ₗ-+ₗ m p = begin
    m * (1 + p) ≡⟨ ℕ-*-comm m (1 + p) ⟩ 
    (1 + p) * m ≡⟨ *-distrib1ₗ-+ᵣ p m ⟩
    m + p * m ≡⟨ cong (λ a → m + a) (ℕ-*-comm p m) ⟩
    m + m * p ∎
