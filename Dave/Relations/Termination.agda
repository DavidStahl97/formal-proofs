module Dave.Relations.Termination where
    open import Agda.Primitive
    open import Dave.Relations.Definitions    
    open import Dave.Logic.Module

    data Acc {ℓ} {A : Set ℓ} (_<_ : HomoRel A ℓ) (x : A) : Set ℓ where
        acc : ({y : A} → y < x → Acc _<_ y) → Acc _<_ x
    
    WellFounded : {ℓ : Level} {A : Set ℓ} → HomoRel A ℓ → Set ℓ
    WellFounded {ℓ} {A} _<_ = ∀ (x : A) → Acc _<_ x

    OrderRel-WF : {ℓ : Level} {A : Set ℓ} 
        → (rel : StrictPartialOrderRel A)
        → LowerBound rel
        → WellFounded (StrictPartialOrderRel.rel rel)
    OrderRel-WF {ℓ} {A} rel (a , x) n = acc {!  !}        
        where
            lem : {n m : A} → StrictPartialOrderRel.rel rel m n → Acc (StrictPartialOrderRel.rel rel) m
            lem {n} {m} m<n = {!   !}

            tst : Acc (StrictPartialOrderRel.rel rel) a
            tst = acc λ{ {y} y<a → ⊥-elim (StrictPartialOrderRel.asymetric rel y<a (x y))}

            

            