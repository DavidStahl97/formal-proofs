module Dave.Relations.Termination where
    open import Agda.Primitive
    open import Dave.Relations.Definitions    
    open import Dave.Logic.Module
    open import Dave.Relations.Isomorphism

    data ↓ {ℓ ℓ'} {A : Set ℓ} (_<_ : HomoRel A ℓ') (x : A) : Set (ℓ ⊔ ℓ') where
        pf↓ : ({y : A} → y < x → ↓ _<_ y) → ↓ _<_ x
    
    WellFounded : {ℓ : Level} {A : Set ℓ} → HomoRel A ℓ → Set ℓ
    WellFounded {ℓ} {A} _<_ = ∀ (x : A) → ↓ _<_ x     

    module measure-module {ℓ ℓ' ℓ1 ℓ2 : Level} {A : Set ℓ} {B : Set ℓ'}
                {_<A_ : HomoRel A ℓ1} {_<B_ : HomoRel B ℓ2}
                {m : A → B}
                (decreasem : ∀ {a a' : A} → a <A a' → m a <B m a')
        where
            measure-↓ : ∀ {a : A} → ↓ _<B_ (m a) → ↓ _<A_ a
            measure-↓ {a} (pf↓ fM) = pf↓ h
                where
                    h : {y : A} → y <A a → ↓ _<A_ y
                    h p = measure-↓ (fM (decreasem p))

    open measure-module public



     

    