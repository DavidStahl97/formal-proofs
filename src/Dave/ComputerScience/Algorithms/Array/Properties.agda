module Dave.ComputerScience.Algorithms.Array.Properties where
    open import Data.Nat
    open import Function.LeftInverse
    open import Function.Inverse
    open import Relation.Binary.PropositionalEquality
    import Data.Vec

    open import Dave.ComputerScience.Algorithms.Array

    private
        variable
            A : Set            
            n : ℕ

    tail : Array A (suc n) → Array A n
    tail (x ∷ xs) = xs        

    Array↔Vec : Array A n ↔ Data.Vec.Vec A n
    Array↔Vec = record 
        {
            to = →-to-⟶ Array→Vec;
            from = →-to-⟶ Vec→Array;
            inverse-of = record 
                {
                    left-inverse-of = left-inverse;
                    right-inverse-of = right-inverse
                }
        }
        where
            left-inverse : ∀ (x : Array A n) → Vec→Array (Array→Vec x) ≡ x
            left-inverse [] = refl
            left-inverse (x ∷ xs) = cong (λ xs → x ∷ xs) (left-inverse xs)

            right-inverse : ∀ (x : Data.Vec.Vec A n) → Array→Vec (Vec→Array x) ≡ x
            right-inverse Data.Vec.[] = refl
            right-inverse (x Data.Vec.∷ xs) = cong (λ xs → x Data.Vec.Vec.∷ xs) (right-inverse xs)