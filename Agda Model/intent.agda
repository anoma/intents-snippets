open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module intent where

  import base
  open base

  {- The report has interpretations in any bicartesian CC. For convenience,
     we instead instantiate this in any category with a universe interpeting
     the morphisms as terms of the function type and composition as function
     composition. To ease dependent typing we postulate specific states, batches
     and batch-prodcessing functions as postulates. The only non-standard
     terms used are:

     a) is-embed signifying an "injection" into a type (see HoTT Book 4.6)

     b) _×fun_ specifying product morphism argument-wise with typing:

     (f : A → B) (g : C → D) ⊢ f ×fun g : A × C → B × D

     c) Σ specifying the dependent sum type.

     All notation and terms can be canonically associated with the HoTT Book
     notation. -}

  -- We postulate an interval of real numbers [0 , 1]
  postulate Interval : Type lzero
  -- We fix a specific set 𝑺
            𝑺 : Type lzero

  -- A unit type telling us whether a transaction is non-satisfactory
  data Error : Type lzero where
    not-satisfied : Error

  -- Intent then - for a fixed 𝑺 - takes a state transition function  and says
  -- what preference is there in a transaction or if it is not satisfied [11]
  Intent = (𝑺 → 𝑺) × (𝑺 × 𝑺 → Error + Interval)

  -- Batch is just a collection of intents current implementation supports
  -- infinite subsets. Practically they are finite. A batch is a type with
  -- a proof that it is a subtype of the type of Intents
  record Batch : Type (lsuc lzero) where
    constructor _,_
    field
      set : Type lzero
      inclusion : Σ[ f ∶ (set → Intent) ] (is-embed f)

  -- For finite case we can replace inclusion with the type checking that set
  -- is equal to some finite list over Intent

  -- We now fix some state-space over which we parametrise our machines
  State = Type lzero

  -- Fix a probability monad P. We represent it as some assignment on objects
  postulate P-obj : Type lzero → Type lzero
  -- And morphisms
            P-mor : (A B : State) → (A → B) → ((P-obj A) → (P-obj B))
  -- Need join in Haskell, i.e. multiplication for monad P
            mult : (A : State) → (P-obj (P-obj A)) → (P-obj A)

  -- We define our monad 𝑴. We first specify assignment on objects
  𝑴-obj : Batch → State → Type lzero
  𝑴-obj (BatchB , subset-proof) StateS =
        BatchB → P-obj ((StateS × BatchB))
  -- And morphisms
  𝑴-mor : (BatchB : Batch)  (StateS1 StateS2 : State) → (StateS1 → StateS2)
                                                       → ((𝑴-obj BatchB StateS1)
                                                       → (𝑴-obj BatchB StateS2))
  𝑴-mor (Batch1 , _) StateS1 StateS2 f =
        λ m_obj batch → P-mor _ _
                              (f ×fun (id Batch1))
                              (m_obj batch)

  -- This can be just seen as the composition of the exponential functor, the
  -- product functor and P given a fixed batch

  -- We can define multiplication for 𝑴 as well
  𝑴-mult : (BatchB : Batch) (StateS : State) → (𝑴-obj BatchB (𝑴-obj BatchB StateS)) → (𝑴-obj BatchB StateS)
  𝑴-mult (BatchB , p) StateS =
         λ f b → (mult _) (P-mor ((𝑴-obj (BatchB , p) StateS) × BatchB)
                                 (P-obj (StateS × BatchB))
                                 (λ { (f1 , b1) → f1 b1})
                                 (f b))

  -- Define a batch-machine.
  machine : Batch → State → Type lzero
  -- Given a state, a Batch machine is a coalgebra of form
  machine BatchB StateS = StateS → 𝑴-obj BatchB StateS

  -- For the first two compositions we fix a batch
  postulate Batch𝑩 : Batch
  -- and a combination function on it named U in the report.
            combine : (Batch.set Batch𝑩) × (Batch.set Batch𝑩) → (Batch.set Batch𝑩)
  -- Fix a state-set
            State𝑺 : State

  -- Define Kleisli composition [2] in the report
  comp2 : machine Batch𝑩 State𝑺 → machine Batch𝑩 State𝑺 → machine Batch𝑩 State𝑺
  comp2 m1 m2 =
        (𝑴-mult Batch𝑩 _ ∘ (𝑴-mor Batch𝑩 _ _ m1)) ∘ m2

  -- Define composition [3] in the report
  -- Types can be automatically assigned by Agda if needed
  comp3 : machine Batch𝑩 State𝑺 → machine Batch𝑩 State𝑺 → machine Batch𝑩 State𝑺
  comp3 m1 m2 =
        λ (s : State𝑺) (b : (Batch.set Batch𝑩)) → mult _
                                                        (P-mor _ _
                                                        (λ { (s' , b') → P-mor _ _
                                                                               (λ { (s'' , b'') → s'' , combine (b' , b'')})
                                                                               (m1 s' b)})
                                                               (m2 s b))

  -- We unroduce a filtering function F
  postulate filter : (Batch.set Batch𝑩) × (Batch.set Batch𝑩) → (Batch.set Batch𝑩)


  -- Define composition [4] in the report
  comp4 : machine Batch𝑩 State𝑺  → machine Batch𝑩 State𝑺 → machine Batch𝑩 State𝑺
  comp4 m1 m2 =
        λ (s : State𝑺) (b : (Batch.set Batch𝑩)) →  mult _
                                                         (P-mor _ _
                                                                (λ { (s' , b') → P-mor _ _
                                                                                       (λ { (s'' , b'') → s'' , (combine (b' , b''))})
                                                                                       (m1 s' (filter (b , b')))})
                                                                (m2 s b))

  -- Fix two new state-sets
  postulate StateS1 : State
            StateS2 : State

  -- Definition of product composition [5]
  comp5 : machine Batch𝑩 StateS1 → machine Batch𝑩 StateS2 → machine Batch𝑩 (StateS1 × StateS2)
  comp5 m1 m2 =
        λ { (s1 , s2) b → mult _
                               (P-mor _ _
                                      (λ { (s'1 , b1) → P-mor _ _
                                                              (λ { (s'2 , b2) → (s'1 , s'2) , (combine (b1 , b2))})
                                                              (m2 s2 b)})
                                      (m1 s1 b))}

  -- Now fix several batches
  postulate BatchB1 : Batch
            BatchB2 : Batch
  -- And corresponding filtering functions
            filter1 : (Batch.set Batch𝑩) → (Batch.set BatchB1)
            filter2 : (Batch.set Batch𝑩) → (Batch.set BatchB2)
  -- And a varying combination function
            combine-var : (Batch.set BatchB1) × (Batch.set BatchB2) → (Batch.set Batch𝑩)

  -- Definition of composition [6]
  comp6 : machine BatchB1 StateS1 → machine BatchB2 StateS2 → machine Batch𝑩 (StateS1 × StateS2)
  comp6 m1 m2 =
        λ { (s1 , s2) b → mult _
                               (P-mor _ _
                                      (λ {(s'1 , b1) → P-mor _ _
                                                             (λ { (s'2 , b2) → (s'1 , s'2) , (combine-var (b1 , b2))})
                                                             (m2 s2 (filter2 b))})
                                      (m1 s1 (filter1 b)))}

  -- Definition of composition [7]
  comp7 : machine Batch𝑩 StateS1 → machine Batch𝑩 StateS2 → machine Batch𝑩 (StateS1 + StateS2)
  comp7 m1 m2 (inl s1) = 𝑴-mor Batch𝑩 _ _ inl (m1 s1)
  comp7 m1 m2 (inr s2) = 𝑴-mor Batch𝑩 _ _ inr (m2 s2)

  -- Fix сast-back functions
  postulate back1 : (Batch.set BatchB1) → (Batch.set Batch𝑩)
            back2 : (Batch.set BatchB2) → (Batch.set Batch𝑩)

  -- Define composition [9]
  comp9 : machine BatchB1 StateS1 → machine BatchB2 StateS2 → machine Batch𝑩 (StateS1 + StateS2)
  comp9 m1 m2 (inl s1) = λ b → (P-mor _ _ (inl ×fun back1)) ((m1 s1) (filter1 b))
  comp9 m1 m2 (inr s2) = λ b → (P-mor _ _ (inr ×fun back2)) ((m2 s2) (filter2 b))
