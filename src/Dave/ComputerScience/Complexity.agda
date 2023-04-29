module Dave.ComputerScience.Complexity where
    open import Agda.Primitive
    open import Data.Nat hiding (_⊔_)
    open import Data.Product
    open import Relation.Unary

    private
        variable
            a b : Level
            A : Set a
            B : Set b

    record Count (A : Set a) : Set a where
        constructor _,_
        field
            value : A
            n : ℕ

    Algorithm : (A : Set a) (B : Set b) → Set (a ⊔ b)
    Algorithm A B = A → Count B 

    record O-Pred {A : Set a} {B : Set b} (g : A → ℕ) (f : Algorithm A B) : Set a where
        field
            k : ℕ
            k>0 : k > 0
            n₀ : ℕ
            cond : ∀ (a : A) → (Count.n (f a)) ≥ n₀ → (Count.n (f a)) * k < (g a)

    O : {A : Set a} {B : Set b} (g : A → ℕ) → Pred (Algorithm A B) a
    O {A = A} = O-Pred

    
     