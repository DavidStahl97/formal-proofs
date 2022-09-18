module Dave.ComputerScience.Typing.SimpleLanguage where
    open import Dave.Base.Module
    open import Dave.Algebra.Naturals.Module renaming (_+_ to _+ℕ_ ; _<_ to _<ℕ_)
    open import Dave.ComputerScience.Datastructures.Boolean hiding (if_then_else_)
    open import Dave.ComputerScience.Algorithms.NaturalNumbers.Ordering 

    {- see Program=Proof -}

    data Value : Set where
        VNat : ℕ → Value
        VBool : Bool → Value

    data Prog : Set where
        V : Value → Prog
        _+_ : Prog → Prog → Prog
        _<_ : Prog → Prog → Prog
        if_then_else_ : Prog → Prog → Prog → Prog

    infix 50 _+_
    infix 40 _<_
    infix 30 if_then_else_

    data _⇒_ : Prog → Prog → Set where
        ⇒-Add : (m n : ℕ) → V (VNat m) + V (VNat n) ⇒ V (VNat (m +ℕ n))
        ⇒-Add-l : {p p' : Prog} → p ⇒ p' → (q : Prog) → p + q ⇒ p' + q
        ⇒-Add-r : {q q' : Prog} → (p : Prog) → q ⇒ q' → p + q ⇒ p + q'
        ⇒-Lt : (m n : ℕ) → V (VNat m) < V (VNat n) ⇒ V (VBool (is m < n))
        ⇒-Lt-l : {p p' : Prog} → p ⇒ p' → (q : Prog) → p < q ⇒ p' < q
        ⇒-Lt-r : {q q' : Prog} → (p : Prog) → q ⇒ q' → p < q ⇒ p < q'
        ⇒-If : {p p' : Prog} → p ⇒ p' → (q r : Prog) → if p then q else r ⇒ if p' then q else r
        ⇒-If-t : (p q : Prog) → if V (VBool true) then p else q ⇒ p
        ⇒-If-f : (p q : Prog) → if V (VBool false) then p else q ⇒ q

    data Type : Set where
        TNat TBool : Type

    data ⊢_∷_ : Prog → Type → Set where
        ⊢-Nat : (n : ℕ) → ⊢ V (VNat n) ∷ TNat
        ⊢-Bool : (b : Bool) → ⊢ V (VBool b) ∷ TBool
        ⊢-Add : {p q : Prog} → ⊢ p ∷ TNat → ⊢ q ∷ TNat → ⊢ p + q ∷ TNat
        ⊢-Lt : {p q : Prog} → ⊢ p ∷ TNat → ⊢ q ∷ TNat → ⊢ p < q ∷ TBool
        ⊢-If : {p q r : Prog} {A : Type} → ⊢ p ∷ TBool → ⊢ q ∷ A → ⊢ r ∷ A → ⊢ if p then q else r ∷ A

    
    {- Theorem 1.4.3.1 : Type uniqueness -}
    TUniq : {p : Prog} {A A' : Type} → ⊢ p ∷ A → ⊢ p ∷ A' → A ≡ A'
    TUniq (⊢-Nat n) (⊢-Nat .n) = ≡-refl
    TUniq (⊢-Bool b) (⊢-Bool .b) = ≡-refl
    TUniq (⊢-Add x x₁) (⊢-Add y y₁) = ≡-refl
    TUniq (⊢-Lt x x₁) (⊢-Lt y y₁) = ≡-refl
    TUniq (⊢-If x x₁ x₂) (⊢-If y y₁ y₂) = TUniq x₂ y₂

    {- Theorem 1.4.3.2 : Subject reduction -}
    SubRed : {p p' : Prog} {A : Type} → (p ⇒ p') → ⊢ p ∷ A → ⊢ p' ∷ A
    SubRed (⇒-Add m n) (⊢-Add p∷A p∷A₁) = ⊢-Nat (m +ℕ n)
    SubRed (⇒-Add-l p⇒p' q) (⊢-Add p∷A q∷A) = ⊢-Add (SubRed p⇒p' p∷A) q∷A
    SubRed (⇒-Add-r p p⇒p') (⊢-Add p∷A q∷A) = ⊢-Add p∷A (SubRed p⇒p' q∷A)
    SubRed (⇒-Lt m n) (⊢-Lt p∷A q∷A) = ⊢-Bool (is m < n)
    SubRed (⇒-Lt-l p⇒p' q) (⊢-Lt p∷A q∷A) = ⊢-Lt (SubRed p⇒p' p∷A) q∷A
    SubRed (⇒-Lt-r p p⇒p') (⊢-Lt p∷A q∷A) = ⊢-Lt p∷A (SubRed p⇒p' q∷A)
    SubRed (⇒-If p⇒p' q r) (⊢-If p∷Bool q∷A r∷A) = ⊢-If (SubRed p⇒p' p∷Bool) q∷A r∷A
    SubRed (⇒-If-t p q) (⊢-If (⊢-Bool .true) q∷A r∷A) = q∷A
    SubRed (⇒-If-f p q) (⊢-If (⊢-Bool .false) q∷A r∷A) = r∷A

    {- Theorem 1.4.3.3 : Progress -}
    Progress : {p : Prog} {A : Type} 
        → ⊢ p ∷ A 
        → Σ Value (λ v → p ≡ V v) ⊎ Σ Prog (λ p' → p ⇒ p')
    Progress (⊢-Nat n) = inj₁ (VNat n , ≡-refl)
    Progress (⊢-Bool b) = inj₁ (VBool b , ≡-refl)
    Progress (⊢-Add p∷TNat q∷TNat) with Progress p∷TNat
    Progress (⊢-Add p∷TNat q∷TNat) | inj₁ (v , p≡v) with Progress q∷TNat 
    Progress (⊢-Add p∷TNat q∷TNat) | inj₁ (VNat m , ≡-refl) | inj₁ (VNat n , ≡-refl) = inj₂ (V (VNat (m +ℕ n)) , ⇒-Add m n)
    Progress (⊢-Add p∷TNat q∷TNat) | inj₁ (v , p≡v) | inj₂ (q-prog , x) = inj₂ ((_ + q-prog) , ⇒-Add-r _ x)
    Progress (⊢-Add p∷TNat q∷TNat) | inj₂ (p' , p⇒p') = inj₂ ((p' + _) , ⇒-Add-l p⇒p' _)
    Progress (⊢-Lt p∷TNat q∷TNat) with Progress p∷TNat
    Progress (⊢-Lt p∷TNat q∷TNat) | inj₁ (a , x) with Progress q∷TNat
    Progress (⊢-Lt p∷TNat q∷TNat) | inj₁ (VNat m , ≡-refl) | inj₁ (VNat n , ≡-refl) = inj₂ (V (VBool (is m < n)) , ⇒-Lt m n)
    Progress (⊢-Lt p∷TNat q∷TNat) | inj₁ (v , p≡v) | inj₂ (q , q⇒q') = inj₂ ((_ < q) , ⇒-Lt-r _ q⇒q')
    Progress (⊢-Lt p∷TNat q∷TNat) | inj₂ (p , p⇒p') = inj₂ ((p < _) , ⇒-Lt-l p⇒p' _)
    Progress (⊢-If p∷TBool q∷A r∷A) with Progress p∷TBool
    Progress (⊢-If p∷TBool q∷A r∷A) | inj₁ (VBool false , ≡-refl) = inj₂ ( _ , ⇒-If-f _ _)
    Progress (⊢-If p∷TBool q∷A r∷A) | inj₁ (VBool true , ≡-refl) = inj₂ ( _ , ⇒-If-t _ _)
    Progress (⊢-If p∷TBool q∷A r∷A) | inj₂ (p' , p⇒p') = inj₂ ((if p' then _ else _) , ⇒-If p⇒p' _ _)

    {- Type Inference -}

    TInf : Prog → Maybe Type

    private
        ShouldBeNat : Type → Maybe Type
        ShouldBeNat TNat = just TNat
        ShouldBeNat _ = nothing

        ShouldBeBool : Type → Maybe Type
        ShouldBeBool TBool = just TBool
        ShouldBeBool _ = nothing

        _=Type_ : Prog → Type → Maybe Type
        _=Type_ prog  = λ{TNat → CreateMaybe ShouldBeNat
                         ; TBool → CreateMaybe ShouldBeBool}
            where
                CreateMaybe : (Type → Maybe Type) → Maybe Type
                CreateMaybe f = TInf prog >>=Maybe f   
    
    TInf (V (VNat x)) = just TNat
    TInf (V (VBool x)) = just TBool
    TInf (p + q) = p =Type TNat >>=Maybe λ _ → q =Type TNat
    TInf (p < q) = p =Type TNat 
        >>=Maybe λ _ → q =Type TNat 
        >>=Maybe λ _ → just TBool
    TInf (if p then q else r) = p =Type TBool 
        >>=Maybe λ _ → TInf q 
        >>=Maybe λ qType → r =Type qType
         
    {- Correctness of Type Inference -}
    TInf-Correct : ∀ {p : Prog} {t : Type} → just t ≡ TInf p → ⊢ p ∷ t
    TInf-Correct {V (VNat n)} {TNat} ≡-refl = ⊢-Nat n
    TInf-Correct {V (VBool b)} {TBool} ≡-refl = ⊢-Bool b
    TInf-Correct {p + q} {t} t≡TInf = ⊢p+q∷TNat
        where
            p≡TNat : just TNat ≡ TInf p
            p≡TNat with TInf p
            p≡TNat | just TNat = ≡-refl

            q≡TNat : just TNat ≡ TInf q
            q≡TNat with TInf p | TInf q
            q≡TNat | just TNat | just TNat = ≡-refl            

            t≡TNat : t ≡ TNat
            t≡TNat with TInf p | TInf q
            t≡TNat | just TNat | just TNat = ≡-just t≡TInf            

            ⊢p+q∷TNat : ⊢ (p + q) ∷ t
            ⊢p+q∷TNat with t≡TNat
            ⊢p+q∷TNat | ≡-refl = ⊢-Add (TInf-Correct p≡TNat) (TInf-Correct q≡TNat)
  
    TInf-Correct {p < q} {t} t≡TInf = ⊢p<q∷TBool    
        where
            p≡TNat : just TNat ≡ TInf p
            p≡TNat with TInf p
            p≡TNat | just TNat = ≡-refl

            q≡TNat : just TNat ≡ TInf q
            q≡TNat with TInf p | TInf q
            q≡TNat | just TNat | just TNat = ≡-refl

            t≡TBool : t ≡ TBool
            t≡TBool with TInf p | TInf q
            t≡TBool | just TNat | just TNat = ≡-just t≡TInf                       

            ⊢p<q∷TBool : ⊢ (p < q) ∷ t
            ⊢p<q∷TBool with t≡TBool
            ⊢p<q∷TBool | ≡-refl = ⊢-Lt (TInf-Correct p≡TNat) (TInf-Correct q≡TNat)

    TInf-Correct {if p then q else r} {t} t≡TInf =  IsCorrect                    
        where
            p≡TBool : just TBool ≡ TInf p
            p≡TBool with TInf p
            p≡TBool | just TBool = ≡-refl            

            ReturnType : just t ≡ TInf q × just t ≡ TInf r
            ReturnType with TInf p
            ReturnType | just TBool with TInf q
            ReturnType | just TBool | just TNat with TInf r
            ReturnType | just TBool | just TNat | just TNat rewrite t≡TInf = ⟨ ≡-refl , ≡-refl ⟩
            ReturnType | just TBool | just TBool with TInf r
            ReturnType | just TBool | just TBool | just TBool rewrite t≡TInf = ⟨ ≡-refl , ≡-refl ⟩

            IsCorrect : ⊢ (if p then q else r) ∷ t
            IsCorrect = ⊢-If (TInf-Correct p≡TBool) (TInf-Correct (proj₁ ReturnType)) (TInf-Correct (proj₂ ReturnType))

            



 