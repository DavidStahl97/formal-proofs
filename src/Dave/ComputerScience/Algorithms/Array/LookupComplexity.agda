module Dave.ComputerScience.Algorithms.Array.LookupComplexity where
    
    open import Data.Nat
    open import Data.Product
    open import Data.Fin

    open import Dave.ComputerScience.Algorithms.Array
    open import Dave.ComputerScience.Complexity

    private
        variable
            A : Set            
            n : ℕ

    EmptyArray : Array ℕ n
    EmptyArray {n = zero} = []
    EmptyArray {n = suc n} = 0 ∷ EmptyArray {n = n}

    argSize : ArgSize (lookup {A} {n})
    argSize = record 
        {
            n-args = 0;
            f = λ (array , n) → length array
        }


    lookup∈O[1] : (lookup {A} {n}) ∈O[ argSize , (λ n → 1) ]
    lookup∈O[1] = record 
        {
            worst-case = record 
                {
                    f = λ n → 1;
                    f-correctness = {! record 
                        {
                            arg = ?;
                            is-mapped = ?;
                            arg⋆A = ?;
                            f-correct = ?
                        }  !}
                };
            o = {!   !}
        }
 