module Dave.ComputerScience.Complexity where
    open import Agda.Primitive
    open import Data.Nat hiding (_⊔_)
    open import Data.Product
    open import Relation.Unary
    open import Relation.Nullary
    open import Relation.Binary.PropositionalEquality

    private
        variable            
            A B : Set

    record Count (A : Set) : Set where
        constructor _,_
        field
            value : A
            n : ℕ

    Algorithm : (A B : Set) → Set
    Algorithm A B = A → Count B 

    n-× : ℕ → Set
    n-× zero = ℕ
    n-× (suc n) = ℕ × n-× n

    n-≥ : {n-args : ℕ} → (n₀ : n-× n-args) → (n : n-× n-args) → Set
    n-≥ {zero} n₀ n = n ≥ n₀
    n-≥ {suc n-args} (n₀ , n₀-tail) (n , n-tail) = n ≥ n₀ × n-≥ n₀-tail n-tail 

    record O (n-args : ℕ) (g : (n-× n-args) → ℕ) (f : (n-× n-args) → ℕ) : Set where
        field
            k : ℕ
            k>0 : ¬ k ≡ 0
            n₀ : n-× n-args
            cond : ∀ (n : (n-× n-args)) → n-≥ n₀ n → f n ≤ k * g n

    record IsInO (n-args : ℕ) (g : (n-× n-args) → ℕ) 
        (algo : Algorithm A B) : Set where 
        field
            map-args : A → (n-× n-args)
            f : (n-× n-args) → ℕ
            f-isworst : ∀ (a : A) → f (map-args a) ≥ Count.n (algo a)
            o : O n-args g f

    O₁ : {A : Set} {B : Set} → (g : ℕ → ℕ) → Pred (Algorithm A B) lzero
    O₁ = IsInO 0

    O[1] : {A : Set} {B : Set} → Pred (Algorithm A B) lzero
    O[1] = O₁ (λ n → 1)

    O[N] : {A : Set} {B : Set} → Pred (Algorithm A B) lzero
    O[N] = O₁ (λ n → n) 