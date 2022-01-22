module Algebra.Naturals.Bin where
  open import Algebra.Naturals.Definition
  open import Algebra.Naturals.Addition
  open import Algebra.Naturals.Multiplication
  
  data Bin : Set where
    ⟨⟩ : Bin
    _t : Bin → Bin
    _f : Bin → Bin

  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ t
  inc (b t) = (inc b) f
  inc (b f) = b t

  to : ℕ → Bin
  to zero = ⟨⟩ f
  to (suc n) = inc (to n)

  from : Bin → ℕ
  from ⟨⟩ = zero
  from (b t) = 1 + 2  * (from b)
  from (b f) = 2 * (from b)

  from6 = from (⟨⟩ t t f)
  from23 = from (⟨⟩ t f t t t)
  from23WithZeros = from (⟨⟩ f f f t f t t t)

  Bin-ℕ-Suc-Homomorph : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
  Bin-ℕ-Suc-Homomorph ⟨⟩ = refl
  Bin-ℕ-Suc-Homomorph (b t) = begin
    from (inc (b t)) ≡⟨⟩ 
    from ((inc b) f) ≡⟨⟩ 
    2 * (from (inc b)) ≡⟨ cong (λ a → 2 * a) (Bin-ℕ-Suc-Homomorph b) ⟩
    2 * suc (from b) ≡⟨⟩
    2 * (1 + (from b)) ≡⟨ *-distrib1ₗ-+ₗ 2 (from b) ⟩
    2 + 2 * (from b) ≡⟨⟩
    suc (1 + 2 * (from b)) ≡⟨⟩
    suc (from (b t)) ∎
  Bin-ℕ-Suc-Homomorph (b f) = begin
    from (inc (b f)) ≡⟨⟩ 
    from (b t) ≡⟨⟩
    1 + 2 * (from b) ≡⟨⟩
    suc (2 * from b) ≡⟨⟩
    suc (from (b f)) ∎

  to-inverse-from : ∀ (n : ℕ) → from (to n) ≡ n
  to-inverse-from zero = refl
  to-inverse-from (suc n) = begin
    from (to (suc n)) ≡⟨⟩ 
    from (inc (to n)) ≡⟨ Bin-ℕ-Suc-Homomorph (to n) ⟩
    suc (from (to n)) ≡⟨ cong (λ a → suc a) (to-inverse-from n) ⟩
    suc n ∎