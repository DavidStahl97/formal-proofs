module Dave.ComputerScience.Complexity where
    open import Agda.Primitive
    open import Data.Bool using (Bool)
    open import Data.Nat hiding (_⊔_)
    open import Data.Product
    open import Relation.Unary hiding (Decidable)
    open import Relation.Nullary
    open import Relation.Binary.PropositionalEquality
    open import Relation.Binary

    private
        variable            
            A B : Set

    record Cost (A : Set) : Set where        
        field
            value : A
            n : ℕ 

    cost : A → Cost A
    cost a = record 
        {
            value = a;
            n = 1
        }

    cost-nothing : A → Cost A
    cost-nothing a = record 
        {
            value = a;
            n = 0
        }    

    _cost[_]_ : A → {rel : Rel A lzero} → Decidable rel → A → Cost Bool
    a cost[ rel ] b = cost (does (rel a b))      

    infixl 1 _>>+_
    _>>+_ : {A B : Set} → Cost A → (A → Cost B) → Cost B
    _>>+_ {A} {B} a f = let b : Cost B
                            b = f (Cost.value a)
                        in
        record 
        {
            value = Cost.value b;
            n = Cost.n a + Cost.n b
        }       

    Algorithm : (A B : Set) → Set
    Algorithm A B = A → Cost B 

    n-× : ℕ → Set
    n-× zero = ℕ
    n-× (suc n) = ℕ × n-× n

    n-≥ : {n-args : ℕ} → (n₀ : n-× n-args) → (n : n-× n-args) → Set
    n-≥ {zero} n₀ n = n ≥ n₀
    n-≥ {suc n-args} (n₀ , n₀-tail) (n , n-tail) = n ≥ n₀ × n-≥ n₀-tail n-tail    

    record O {n-args : ℕ} (g : (n-× n-args) → ℕ) (f : (n-× n-args) → ℕ) : Set where
        field
            k : ℕ
            k>0 : ¬ k ≡ 0
            n₀ : n-× n-args
            cond : ∀ (n : (n-× n-args)) → n-≥ n₀ n → f n ≤ k * g n

    record Ω {n-args : ℕ} (g : (n-× n-args) → ℕ) (f : (n-× n-args) → ℕ) : Set where
        field
            k : ℕ
            k>0 : ¬ k ≡ 0
            n₀ : n-× n-args
            cond : ∀ (n : (n-× n-args)) → n-≥ n₀ n → f n ≥ k * g n    

    record Φ {n-args : ℕ} (g : (n-× n-args) → ℕ) (f : (n-× n-args) → ℕ) : Set where
        field
            worst : O g f
            best : Ω g f    

    record ArgSize (algo : Algorithm A B) : Set where
        field
            n-args : ℕ
            f : A → (n-× n-args)

        type : Set
        type = n-× n-args

    module AlgoComplexity {algo : Algorithm A B} (argSize : ArgSize algo) where

        record rel-case-arg (_⋆_ : Rel ℕ lzero)            
            (n : ArgSize.type argSize)
            (f : ArgSize.type argSize → ℕ) : Set where
            field            
                arg : A
                is-mapped : ArgSize.f argSize arg ≡ n
                arg⋆A : ∀ (a : A) → ArgSize.f argSize a ≡ n → Cost.n (algo arg) ⋆ Cost.n (algo a)
                f-correct : Cost.n (algo arg) ≡ f n

        record rel-case-func (_⋆_ : Rel ℕ lzero) : Set where
            field
                n-args : ℕ
                f : ArgSize.type argSize → ℕ
                args-map : A → ArgSize.type argSize
                is-worst : ∀ (n : ArgSize.type argSize) → rel-case-arg _⋆_ n f    

        record O[_] (g : ArgSize.type argSize → ℕ) : Set where 
            field                
                worst-case : rel-case-func _≥_ 
                o : O g (rel-case-func.f worst-case)

        record Ω[_] (g : ArgSize.type argSize → ℕ) : Set where
            field
                best-case : rel-case-func _≤_
                ω : Ω g (rel-case-func.f best-case)

        record Φ[_] (g : ArgSize.type argSize → ℕ) : Set where
            field
                worst : O[ g ]
                best : Ω[ g ]
