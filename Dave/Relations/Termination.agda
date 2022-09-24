module Dave.Relations.Termination where
    open import Agda.Primitive
    open import Dave.Relations.Definitions    

    data Acc {ℓ} {A : Set ℓ} (_<_ : HomoRel A ℓ) (x : A) : Set ℓ where
        acc : ({y : A} → y < x → Acc _<_ y) → Acc _<_ x
    
    WellFounded : {ℓ : Level} {A : Set ℓ} → HomoRel A ℓ → Set ℓ
    WellFounded {ℓ} {A} _<_ = ∀ (x : A) → Acc _<_ x