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