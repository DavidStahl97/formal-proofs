module Dave.Algebra.Naturals.Addition where  
  open import Dave.Algebra.Naturals.Definition public

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

  infixl 6 _+_

  {- Semigroup -}
  +-assoc : associative _+_
  +-assoc zero n p = refl
  +-assoc (suc m) n p = cong suc (+-assoc m n p)

  +-assoc' : associative _+_
  +-assoc' zero n p = begin
    (zero + n) + p ≡⟨⟩
    n + p ≡⟨⟩
    zero + (n + p) ∎
  +-assoc' (suc m) n p = begin
    (suc m + n) + p ≡⟨⟩
    suc (m + n) + p ≡⟨⟩
    suc ((m + n) + p) ≡⟨ cong suc (+-assoc' m n p) ⟩
    suc (m + (n + p)) ∎
   
  ℕ-+-IsSemigroup : IsSemigroup _+_
  IsSemigroup.assoc ℕ-+-IsSemigroup = +-assoc

  ℕ-+-Semigroup : Semigroup
  Semigroup.Carrier ℕ-+-Semigroup = ℕ
  Semigroup._·_ ℕ-+-Semigroup = _+_
  Semigroup.isSemigroup ℕ-+-Semigroup = ℕ-+-IsSemigroup

  {- Identity -}
  +-right-identity : right-identity _+_ 0
  +-right-identity zero = refl
  +-right-identity (suc n) = cong suc (+-right-identity n)

  +-left-identity : left-identity _+_ 0
  +-left-identity m = refl

  ℕ-+-HasIdentity : Identity _+_ 0
  Identity.left ℕ-+-HasIdentity = +-left-identity
  Identity.right ℕ-+-HasIdentity = +-right-identity

  {- Monoid -}
  ℕ-+-IsMonoid : IsMonoid _+_ 0
  IsMonoid.semigroup ℕ-+-IsMonoid = ℕ-+-IsSemigroup
  IsMonoid.identity ℕ-+-IsMonoid = ℕ-+-HasIdentity

  ℕ-+-Monoid : Monoid
  Monoid.Carrier ℕ-+-Monoid = ℕ
  Monoid._·_ ℕ-+-Monoid = _+_
  Monoid.e ℕ-+-Monoid = 0
  Monoid.isMonoid ℕ-+-Monoid = ℕ-+-IsMonoid

  {- Commutative Monoid -}
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-comm : commutative _+_
  +-comm m zero = +-right-identity m
  +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

  +-comm' : commutative _+_
  +-comm' m zero = +-right-identity m
  +-comm' m (suc n) = begin
      (m + suc n) ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m) ∎

  ℕ-+-IsCommutativeMonoid : IsCommutativeMonoid _+_ 0
  IsCommutativeMonoid.isSemigroup ℕ-+-IsCommutativeMonoid = ℕ-+-IsSemigroup
  IsCommutativeMonoid.leftIdentity ℕ-+-IsCommutativeMonoid = +-left-identity
  IsCommutativeMonoid.comm ℕ-+-IsCommutativeMonoid = +-comm

  {- Additional Theorems -}
  +-add1ᵣ : ∀ (m : ℕ) → m + 1 ≡ suc m
  +-add1ᵣ zero = refl
  +-add1ᵣ (suc m) = cong suc (+-add1ᵣ m)

  +-add1ₗ : ∀ (m : ℕ) → 1 + m ≡ suc m
  +-add1ₗ m = refl