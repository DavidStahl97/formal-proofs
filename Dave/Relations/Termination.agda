module Dave.Relations.Termination where
    open import Agda.Primitive
    open import Dave.Relations.Definitions    
    open import Dave.Logic.Module

    data Acc {ℓ} {A : Set ℓ} (_<_ : HomoRel A ℓ) (x : A) : Set ℓ where
        acc : ({y : A} → y < x → Acc _<_ y) → Acc _<_ x
    
    WellFounded : {ℓ : Level} {A : Set ℓ} → HomoRel A ℓ → Set ℓ
    WellFounded {ℓ} {A} _<_ = ∀ (x : A) → Acc _<_ x

    {- OrderRel-WF : {ℓ : Level} {A : Set ℓ} 
        → (rel : StrictPartialOrderRel A)
        → LowerBound rel
        → WellFounded (StrictPartialOrderRel.rel rel)
    OrderRel-WF {ℓ} {A} rel (low , low<x) n = acc lem        
        where
            lem : {y : A} → StrictPartialOrderRel.rel rel y n → Acc (StrictPartialOrderRel.rel rel) y
            lem {y} y<n = {!   !}

            tst : Acc (StrictPartialOrderRel.rel rel) low
            tst = acc λ{ {y} y<a → ⊥-elim (StrictPartialOrderRel.asymetric rel y<a (low<x y))}

            hsllo : ∀ {y : A} → StrictPartialOrderRel.rel rel y n → Acc (StrictPartialOrderRel.rel rel) y
            hsllo y>n = {! !}             -}

            

            