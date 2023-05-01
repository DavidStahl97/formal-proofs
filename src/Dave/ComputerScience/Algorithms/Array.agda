module Dave.ComputerScience.Algorithms.Array where
    open import Agda.Primitive
    open import Function.LeftInverse
    open import Function.Inverse
    open import Data.Nat
    open import Data.Fin
    open import Data.Product
    import Data.Vec 
    open import Relation.Unary
    open import Relation.Binary.PropositionalEquality

    open import Dave.ComputerScience.Complexity

    private
        variable
            a : Level
            A : Set a            
            n : ℕ

    data Array (A : Set a) : ℕ → Set a where
        []  : Array A zero
        _∷_ : ∀ (x : A) (xs : Array A n) → Array A (suc n)
        
    private
        Array→Vec : Array A n → Data.Vec.Vec A n
        Array→Vec [] = Data.Vec.Vec.[]
        Array→Vec (x ∷ xs) = Data.Vec._∷_ x (Array→Vec xs)

        Vec→Array : Data.Vec.Vec A n → Array A n
        Vec→Array Data.Vec.[] = []
        Vec→Array (x Data.Vec.∷ xs) = x ∷ Vec→Array xs        

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


    lookup : Array A n × Fin n → Count A
    lookup (x , n) = Data.Vec.lookup (Array→Vec x) n , 1

     