module Dave.NaturalDeduction.NJ.Rules where

    data ℕ : Set where
        zero : ℕ
        suc : ℕ → ℕ

    data Formula : Set where
        X : ℕ → Formula
        _⇒_ : Formula → Formula → Formula        

    data Context : Set where
        ε : Context
        _,_ : (Γ : Context) → (A : Formula) → Context

    infixl 20 _,_

    _,,_ : Context → Context → Context
    Γ ,, ε = Γ
    Γ ,, (Δ , A) = (Γ ,, Δ) , A

    infixl 19 _,,_

    infix 18 _⊢_

    data _⊢_ : Context → Formula → Set where
        ax : ∀ {Γ A} → Γ , A ⊢ A
        wk : ∀ {Γ A B} → Γ ⊢ B → Γ , A ⊢ B
        ⇒E : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
        ⇒I : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B

    constr : ∀ {Γ A B} → ∀ Γ' → Γ , A , A ,, Γ' ⊢ B → Γ , A ,, Γ' ⊢ B
    constr ε ax = ax
    constr ε (wk p) = p
    constr ε (⇒E p q) = ⇒E (constr ε p) (constr ε q)
    constr ε (⇒I p) = ⇒I (constr (ε , _) p)
    constr (Γ' , A) ax = ax
    constr (Γ' , A) (wk p) = wk (constr _ p)
    constr (Γ' , A) (⇒E p q) = ⇒E (constr (Γ' , A) p) (constr (Γ' , A) q)
    constr (Γ' , A) (⇒I p) = ⇒I (constr (Γ' , A , _) p)
