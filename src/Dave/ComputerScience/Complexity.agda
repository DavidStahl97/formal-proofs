module Dave.ComputerScience.Complexity where
    open import Agda.Builtin.Sigma
    open import Agda.Primitive
    open import Data.Bool using (Bool)
    open import Data.Nat hiding (_⊔_)
    open import Data.Product
    open import Relation.Unary hiding (Decidable)
    open import Relation.Nullary
    open import Relation.Binary using (Rel; Decidable) 
    open import Relation.Binary.PropositionalEquality

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

    record _∈O[_] {n-args : ℕ} (f : (n-× n-args) → ℕ) (g : (n-× n-args) → ℕ) : Set where
        field
            k : ℕ
            k>0 : ¬ k ≡ 0
            n₀ : n-× n-args
            cond : ∀ (n : (n-× n-args)) → n-≥ n₀ n → f n ≤ k * g n

    record _∈Ω[_] {n-args : ℕ} (f : (n-× n-args) → ℕ) (g : (n-× n-args) → ℕ) : Set where
        field
            k : ℕ
            k>0 : ¬ k ≡ 0
            n₀ : n-× n-args
            cond : ∀ (n : (n-× n-args)) → n-≥ n₀ n → f n ≥ k * g n    

    f∈O[g]⇔g∈Ω[f] : {n-args : ℕ} (f : (n-× n-args) → ℕ) (g : (n-× n-args) → ℕ) → 
        f ∈O[ g ] ⇔ g ∈Ω[ f ]
    f∈O[g]⇔g∈Ω[f] f g = {!   !}
        where
            f∈O[g]→g∈Ω[f] : f ∈O[ g ] → g ∈Ω[ f ]
            f∈O[g]→g∈Ω[f] O = {!   !}

    record _∈Φ[_] {n-args : ℕ} (f : (n-× n-args) → ℕ) (g : (n-× n-args) → ℕ) : Set where
        field
            worst : f ∈O[ g ]
            best : f ∈Ω[ g ]

    record ArgSize (algo : Algorithm A B) : Set where
        field
            n-args : ℕ
            f : A → (n-× n-args)

        type : Set
        type = n-× n-args

        isOfSize : type → A → Set
        isOfSize n a = n ≡ f a      

    record _∈O[_,_] 
        (algo : Algorithm A B)
        (argSize : ArgSize algo)
        (g : ArgSize.type argSize → ℕ) : Set where 
        field                
            f : ArgSize.type argSize → ℕ
            f-correctness : ∀ (n : ArgSize.type argSize) (a : A) → f n ≥ Cost.n (algo a)
            isInO : f ∈O[ g ]

    record _∈Ω[_,_] 
        (algo : Algorithm A B)
        (argSize : ArgSize algo)
        (g : ArgSize.type argSize → ℕ) : Set where 
        field                
            f : ArgSize.type argSize → ℕ
            f-correctness : ∀ (n : ArgSize.type argSize) (a : A) → f n ≤ Cost.n (algo a)
            isInΩ : f ∈Ω[ g ]

    record _∈Φ[_,_] 
        (algo : Algorithm A B)
        (argSize : ArgSize algo)
        (g : ArgSize.type argSize → ℕ) : Set where 
        field                
            f : ArgSize.type argSize → ℕ
            isInO : f ∈O[ g ]
            isInΩ : f ∈Ω[ g ]
            

    special-case : Rel ℕ lzero → (algo : Algorithm A B) → ArgSize algo → Set
    special-case {A = A} _⋆_ algo argSize = (n : ArgSize.type argSize) →
        {a : A} → ArgSize.isOfSize argSize n a → 
        Σ A λ special → ArgSize.isOfSize argSize n special × Cost.n (algo special) ⋆ Cost.n (algo a)

    worst-case : (algo : Algorithm A B) → ArgSize algo → Set
    worst-case = special-case _≥_

    best-case : (algo : Algorithm A B) → ArgSize algo → Set
    best-case = special-case _≤_            