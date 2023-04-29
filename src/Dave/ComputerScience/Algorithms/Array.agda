module Dave.ComputerScience.Algorithms.Array where
    open import Agda.Primitive
    open import Data.Nat
    open import Data.Fin
    open import Relation.Unary

    open import Dave.ComputerScience.Complexity

    private
        variable
            a : Level
            A : Set a            
            n : ℕ

    data Array (A : Set a) : ℕ → Set a where
        []  : Array A zero
        _∷_ : ∀ (x : A) (xs : Array A n) → Array A (suc n)

    lookup : Array A n → Fin n → Count A
    lookup (x ∷ xs) zero    = x , 1
    lookup (x ∷ xs) (suc i) = lookup xs i

    