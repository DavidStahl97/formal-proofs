module Dave.ComputerScience.Algorithms.Array where
    open import Agda.Primitive
    open import Function.LeftInverse
    open import Function.Inverse
    open import Agda.Builtin.Nat using (_-_)
    open import Data.Nat hiding (_<_)
    open import Data.Nat.Properties
    open import Data.Fin using (Fin)
    open import Data.Bool using (Bool; if_then_else_; true; false)
    open import Data.Product
    open import Data.Empty.Irrelevant
    import Data.Vec 
    open import Relation.Unary
    open import Relation.Binary.PropositionalEquality
    open import Relation.Binary
    open import Relation.Nullary

    open import Dave.ComputerScience.Complexity

    private
        variable
            A : Set lzero            
            n : ℕ
            _≈_ : Rel A lzero 
            _<_ : Rel A lzero

    data Array (A : Set) : ℕ → Set where
        []  : Array A zero
        _∷_ : ∀ (x : A) (xs : Array A n) → Array A (suc n)        

    Array→Vec : Array A n → Data.Vec.Vec A n
    Array→Vec [] = Data.Vec.Vec.[]
    Array→Vec (x ∷ xs) = Data.Vec._∷_ x (Array→Vec xs)

    Vec→Array : Data.Vec.Vec A n → Array A n
    Vec→Array Data.Vec.[] = []
    Vec→Array (x Data.Vec.∷ xs) = x ∷ Vec→Array xs

    length : Array A n → ℕ
    length {n = n} array = n

    lookup : Array A (suc n) × Fin (suc n) → Cost A
    lookup (x , n) = cost (Data.Vec.lookup (Array→Vec x) n)

    updateAt : Array A n × Fin n × A → Cost (Array A n)
    updateAt (array , n , a) = cost (Vec→Array (Data.Vec.updateAt n (λ _ → a) (Array→Vec array)))

    private
        find-min : Array A n → A 
            →  {_≈_ : Rel A lzero} {_<_ : Rel A lzero} → IsStrictTotalOrder _≈_ _<_ 
            → Cost A
        find-min [] min rel = cost-nothing min
        find-min {A = A} (x ∷ array) min rel = (x cost[ IsStrictTotalOrder._<?_ rel ] min) 
            >>+ λ x<min → if x<min then (find-min array x rel) else (find-min array min rel)

    min : {A : Set} {n : ℕ} 
        → {_≈_ : Rel A lzero} {_<_ : Rel A lzero} → IsStrictTotalOrder _≈_ _<_ 
        → Array A (suc n)
        → Cost A
    min {n = n} rel (x ∷ array) = find-min array x rel               