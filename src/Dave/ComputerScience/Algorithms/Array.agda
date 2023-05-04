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
        
    private
        tail : Array A (suc n) → Array A n
        tail (x ∷ xs) = xs

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


    lookup : Array A n × Fin n → Cost A
    lookup (x , n) = cost (Data.Vec.lookup (Array→Vec x) n)

    lookup∈O[1] : lookup {A} {n} ∈ O[1]
    lookup∈O[1] {A} {n} = record 
        {
            map-args = λ _ → n;
            f = λ n → 1;
            f-isworst = λ x → s≤s z≤n;
            o = record 
                {
                    k = 1;
                    k>0 = λ();
                    n₀ = 0;
                    cond = λ n n≥n₀ → s≤s z≤n
                }
        }

    updateAt : Array A n × Fin n × A → Cost (Array A n)
    updateAt (array , n , a) = cost (Vec→Array (Data.Vec.updateAt n (λ _ → a) (Array→Vec array)))

    updateAt∈O[1] : lookup {A} {n} ∈ O[1]
    updateAt∈O[1] {A} {n} = record 
        {
            map-args = λ _ → n;
            f = λ n → 1;
            f-isworst = λ x → s≤s z≤n;
            o = record 
                {
                    k = 1;
                    k>0 = λ();
                    n₀ = 0;
                    cond = λ n n≥n₀ → s≤s z≤n
                }
        }

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

     
    private
        n≥Cost[find-min] : (array : Array A n) → (start : A)
            → {_≈_ : Rel A lzero} {_<_ : Rel A lzero} → (rel : IsStrictTotalOrder _≈_ _<_)            
            → n ≥ Cost.n (find-min array start rel)
        n≥Cost[find-min] [] start rel = z≤n
        n≥Cost[find-min] (x ∷ array) start rel with Cost.value (x cost[ IsStrictTotalOrder._<?_ rel ] start)
        n≥Cost[find-min] (x ∷ array) start rel | false = s≤s (n≥Cost[find-min] array start rel)
        n≥Cost[find-min] (x ∷ array) start rel | true = s≤s (n≥Cost[find-min] array x rel)

    min∈O[N] : {_≈_ : Rel A lzero} {_<_ : Rel A lzero} → (rel : IsStrictTotalOrder _≈_ _<_) 
        → (min {A} {n} rel) ∈ O[N]
    min∈O[N] {A = A} {n = n} rel = record 
        {
            map-args = λ _ → n;
            f = λ n → n;
            f-isworst = f-isworst;
            o = record 
                {
                    k = 1;
                    k>0 = λ();
                    n₀ = 1;
                    cond = λ n n≥n₀ → m≤n*m n {1} (s≤s z≤n)
                }
        }
            where
                f-isworst : (a : Array A (suc n)) → n ≥ Cost.n (min rel a)
                f-isworst (x ∷ []) = z≤n
                f-isworst (start ∷ (x ∷ array)) = n≥Cost[find-min] (x ∷ array) start rel

       