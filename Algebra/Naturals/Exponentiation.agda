module Algebra.Naturals.Exponentiation where
  open import Algebra.Naturals.Definition
  open import Algebra.Naturals.Multiplication

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = a * (a ^ b)

  infixl 8 _^_ 