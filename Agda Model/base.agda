open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module base where

  -- Formalization of basic type-theoretic constructions as minimal as possible
  -- for the sake of an intent machine model.

  -- Type stand in to Set
  Type : (i : Level) → Set (lsuc i)
  Type i = Set i


  -- Coproduct type data
  data _+_ {l1 l2}(A : Type l1) (B : Type l2) : Set (l1 ⊔ l2) where
       inl : A → A + B
       inr : B → A + B

  rec+ : {l1 l2 l3 : Level}  {A : Type l1} {B : Type l2 } {C : Type l3 } →
         (A → C) → (B → C) → (A + B → C)
  rec+ f g (inl x) = f x
  rec+ f g (inr x) = g x

  ind+ : {l1 l2 l3 : Level} {A : Type l1 } {B : Type l2 } (C :  A + B  → Type l3 ) →
         ((a : A) → C (inl a)) → ( (b : B) → (C (inr b)) ) → ((c : A + B) → (C c))
  ind+ C f g (inl x) = f x
  ind+ C f g (inr x) = g x


  -- Product type data
  data _×_ {l1 l2} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
    _,_ : A → B → A × B

  pair : {l1 l2 : Level} {A : Type l1} {B : Type l2} → A → B → A × B
  pair a b = a , b

  rec× : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : Type l3) →
         (A → B → C) → (A × B → C)
  rec× C f (x , x₁) = f x x₁

  ind× : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : A × B → Type l3) →
         ((a : A) → ∀ (b : B) → C(pair a b)) → ( (x : A × B) → C(x))
  ind× C f (x , x₁) = f x x₁

  pr₁ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (x : A × B) → A
  pr₁ (x , x₁) = x

  pr₂ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (x : A × B) → B
  pr₂ (x , x₁) = x₁

  _×fun_ : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} (f : A → B) (g : C → D) → ( (A × C) → (B × D) )
  f ×fun g = λ { (x , x₁) → (f x) , (g x₁)}


  -- Σ type data
  data Σ {l1 l2 : Level} (A : Type l1) (B : A → Type l2) : Type (l1 ⊔ l2) where
    _,,_ :  (x : A) → B x → Σ A B

  deppair :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x : A) → B x → Σ A B
  deppair x y = x ,, y

  Σ-recursion :  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} (C : Type l3) →
                                                 (∀ (a : A) → B a → C) → (Σ A B → C)
  Σ-recursion C f (x ,, x₁) = f x x₁


  Σ-induction : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} (C : (Σ A B) → Type l3) →
                                     (∀ (a : A) → ∀ (b : B a) → (C (deppair a b))) → (∀ (x : Σ A B) → C x)
  Σ-induction C f (x ,, x₁) = f x x₁

  proj₁ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x : Σ A B) →  A
  proj₁ (x ,, x₁) = x

  proj₂ :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x : Σ A B) → B (proj₁ x)
  proj₂ (x ,, x₁) = x₁

  Σ-syntax = Σ
  infix 2 Σ-syntax
  syntax Σ-syntax A (λ x → B) = Σ[ x ∶ A ] B {- ths colum is gotten by -backdash- + : -}


  -- Equality type data
  data _≡_ {l1} {A : Type l1} :  A → A → Type l1  where
    refl : ∀ (a : A) →  a ≡ a

  -- General
  fun-ap :  {l1 l2 : Level} {A : Type l1} {B : Type l2} {x y : A} (f : A → B) (p : x ≡ y) → (f x) ≡ (f y)
  fun-ap f (refl _) = refl _

  _∘_ : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

  id : {l1 : Level} (A : Type l1) → A → A
  id A x = x

  _∼_ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (g : A → B) → Type (l1 ⊔ l2)
  f ∼ g  = (x : _) → f x ≡ g x

  is-an-equiv :  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → Type ((l1 ⊔ l2))
  is-an-equiv {_} {_} {A} {B} f = ( Σ[ g ∶ (B → A) ] ((f ∘ g) ∼ (id _)) ) × ( Σ[ g ∶ (B → A) ] ((g ∘ f) ∼ (id _)) )

  is-embed : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → Type (l1 ⊔ l2)
  is-embed f = (x y : _) → is-an-equiv (fun-ap {_} {_} {_} {_} {x} {y} f)
