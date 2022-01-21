module Algebra.Naturals.Definition where
  open import Algebra.Equality public
  open import Algebra.Structures.Monoid public
  
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