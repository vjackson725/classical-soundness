module SysL where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (_+_ to _+N_)
open import Agda.Builtin.Equality

open import Agda.Primitive


-- Either

data _+_ {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A + B
  inr : B → A + B

-- Product

infixr 20 _,_
record _×_ {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B


-- Boolean

_∪_ : Bool → Bool → Bool
false ∪ b = b
true ∪ b = true

_∩_ : Bool → Bool → Bool
false ∩ b = false
true ∩ b = b

~_ : Bool → Bool
~ false = true
~ true = false

_⇒_ : Bool → Bool → Bool
a ⇒ true = true
false ⇒ false = true
true ⇒ false = false


∩-tt-l : ∀ {a b} → a ∩ b ≡ true → a ≡ true
∩-tt-l {false} {b} ()
∩-tt-l {true} {.true} refl = refl

∩-tt-r : ∀ {a b} → a ∩ b ≡ true → b ≡ true
∩-tt-r {false} {b} ()
∩-tt-r {true} {.true} refl = refl

∪-r-tt-is-tt : ∀ {a} → a ∪ true ≡ true
∪-r-tt-is-tt {false} = refl
∪-r-tt-is-tt {true} = refl

~~-elim : ∀ {a} → ~ (~ a) ≡ a
~~-elim {false} = refl
~~-elim {true} = refl



∪-tt-evidence : ∀ {a b} → a ∪ b ≡ true → (a ≡ true) + (b ≡ true)
∪-tt-evidence {false} {.true} refl = inr refl
∪-tt-evidence {true} {b} refl = inl refl

⇒-tt-evidence : ∀ {a b} → a ⇒ b ≡ true → (b ≡ true) + ((a ≡ false) × (b ≡ false))
⇒-tt-evidence {false} {false} refl = inr (refl , refl)
⇒-tt-evidence {true} {false} ()
⇒-tt-evidence {a} {true} refl = inl refl

⇒-tt-build : ∀ {a b} → (b ≡ true) + ((a ≡ false) × (b ≡ false))→ a ⇒ b ≡ true
⇒-tt-build (inl refl) = refl
⇒-tt-build (inr (refl , refl)) = refl

bool-cases : ∀ a → (a ≡ true) + (a ≡ false)
bool-cases false = inr refl
bool-cases true = inl refl


-- Vecs

infixr 16 _∷_
data Vec {l} (X : Set l) : Nat → Set l where
  _∷_ : ∀ {n} → X → Vec X n → Vec X (suc n)
  [] : Vec X zero

[_] : ∀ {x} {X : Set x} → X → Vec X 1
[ x ] = x ∷ []

-- evidence an element is in a vec
data Elem {l} {X : Set l} : {n : Nat} → X → Vec X n → Set where
  here : ∀ {x n} {xs : Vec X n} → Elem x (x ∷ xs)
  there : ∀ {x y n} {xs : Vec X n} → Elem x xs → Elem x (y ∷ xs)

-- McBride's Thinnings
-- ways of embedding m things into n
data _≤'_ : Nat → Nat → Set where
  os : {m n : Nat} → m ≤' n → (suc m) ≤' (suc n)
  o' : {m n : Nat} → m ≤' n → m ≤' (suc n)
  oz : 0 ≤' 0

-- thin out a vec by a thinning
vec-thin : ∀ {l} {m n : Nat} {X : Set l} → Vec X n → m ≤' n → Vec X m
vec-thin (x ∷ xs) (os th) = x ∷ vec-thin xs th
vec-thin (x ∷ xs) (o' th) = vec-thin xs th
vec-thin [] oz = []

-- evidence of a vector thinning
data _⊑_[_] {l} {X : Set l} : {m n : Nat} → Vec X m → Vec X n → m ≤' n → Set where
  ths : {m n : Nat} {xs : Vec X m} {ys : Vec X n} {th : m ≤' n} {x : X} → xs ⊑ ys [ th ]  → (x ∷ xs) ⊑ (x ∷ ys) [ os th ]
  th' : {m n : Nat} {xs : Vec X m} {ys : Vec X n} {th : m ≤' n} {y : X} → xs ⊑ ys [ th ]  → xs ⊑ (y ∷ ys) [ o' th ]
  thz : [] ⊑ [] [ oz ]

-- expand an element proof into a bigger vector
elem-thin : ∀ {l} {m n : Nat} {X : Set l} {x : X} {xs : Vec X m} {ys : Vec X n} {th : m ≤' n} →
            Elem x xs → xs ⊑ ys [ th ] → Elem x ys
elem-thin el (th' th) = there (elem-thin el th)
elem-thin here (ths th) = here
elem-thin (there el) (ths th) = there (elem-thin el th)
elem-thin () thz



-- Proposition

data Prop : Set where
  var : Nat → Prop
  _∧_ : Prop → Prop → Prop
  _∨_ : Prop → Prop → Prop
  _⊃_ : Prop → Prop → Prop
  ¬_ : Prop → Prop

-- technically a sequent with restricted right side
-- forgive me for my abuse of syntax
infix 12 _⊢_
data _⊢_ : ∀ {n} → Vec Prop n → Prop → Set where
  prem : ∀ {n} {A : Prop} {Γ : Vec Prop n} →

         Elem A Γ →
         --------
         Γ ⊢ A
  
  ∧I : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →
  
       Γ ⊢ A →      Γ ⊢ B →
       ------------------
            Γ ⊢ A ∧ B

  ∧E₁ : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →
  
        Γ ⊢ A ∧ B →
        ---------
        Γ ⊢ A

  ∧E₂ : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →
  
        Γ ⊢ A ∧ B →
        ---------
        Γ ⊢ B

  ∨I₁ : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →

        Γ ⊢ A →
        ---------
        Γ ⊢ A ∨ B

  ∨I₂ : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →

        Γ ⊢ B →
        ---------
        Γ ⊢ A ∨ B

  ∨E : ∀ {n} {Γ : Vec Prop n} → {A B C : Prop} →

       (A ∷ Γ) ⊢ C →      (B ∷ Γ) ⊢ C →      Γ ⊢ A ∨ B →
       -----------------------------------------------
                            Γ ⊢ C

  ⊃I : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →

       (A ∷ Γ) ⊢ B →
       -----------
       Γ ⊢ A ⊃ B

  ⊃E : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →

       Γ ⊢ A ⊃ B →       Γ ⊢ A →
       -----------------------
                Γ ⊢ B

  RAA : ∀ {n} {Γ : Vec Prop n} → {A B : Prop} →

        (B ∷ Γ) ⊢ A →          (B ∷ Γ) ⊢ ¬ A →
        ------------------------------------
                      Γ ⊢ ¬ B

  DNE : ∀ {n} {Γ : Vec Prop n} → {A : Prop} →

        Γ ⊢ ¬ (¬ A) →
        -----------
        Γ ⊢ A

thin : {m n : Nat} {Γ : Vec Prop m} {Δ : Vec Prop n} {A : Prop} → {th : m ≤' n} →

       Γ ⊢ A →      Γ ⊑ Δ [ th ] →
       ----------------------------
               Δ ⊢ A

thin (prem el) th = prem (elem-thin el th)
thin (∧I sq sq₁) th = ∧I (thin sq th) (thin sq₁ th)
thin (∧E₁ sq) th = ∧E₁ (thin sq th)
thin (∧E₂ sq) th = ∧E₂ (thin sq th)
thin (∨I₁ sq) th = ∨I₁ (thin sq th)
thin (∨I₂ sq) th = ∨I₂ (thin sq th)
thin (⊃E sq sq₁) th = ⊃E (thin sq th) (thin sq₁ th)
thin (DNE sq) th = DNE (thin sq th)
-- things that add to the environment
thin (∨E sq₁ sq₂ sq₃) th = ∨E (thin sq₁ (ths th)) (thin sq₂ (ths th)) (thin sq₃ th)
thin (⊃I sq) th = ⊃I (thin sq (ths th))
thin (RAA sq₁ sq₂) th = RAA (thin sq₁ (ths th)) (thin sq₂ (ths th))

-- Assoc

∧-assoc1 : ∀ {A B C} → [ A ∧ (B ∧ C) ] ⊢ (A ∧ B) ∧ C
∧-assoc1 = ∧I
             (∧I
               (∧E₁ (prem here))
               (∧E₁ (∧E₂ (prem here))))
             (∧E₂ (∧E₂ (prem here)))

∧-assoc2 : ∀ {A B C} → [ (A ∧ B) ∧ C ] ⊢ A ∧ (B ∧ C)
∧-assoc2 = ∧I
             (∧E₁ (∧E₁ (prem here)))
             (∧I
               (∧E₂ (∧E₁ (prem here)))
               (∧E₂ (prem here)))

∨-assoc1 : ∀ {A B C} → [ A ∨ (B ∨ C) ] ⊢ (A ∨ B) ∨ C
∨-assoc1 = ∨E
             (∨I₁ (∨I₁ (prem here)))
             (∨E
               (∨I₁ (∨I₂ (prem here)))
               (∨I₂ (prem here))
               (prem here))
             (prem here)

∨-assoc2 : ∀ {A B C} → [ (A ∨ B) ∨ C ] ⊢ A ∨ (B ∨ C)
∨-assoc2 = ∨E
             (∨E
               (∨I₁ (prem here))
               (∨I₂ (∨I₁ (prem here)))
               (prem here))
             (∨I₂ (∨I₂ (prem here)))
             (prem here)

-- Comm

∧-comm : ∀ {A B} → [ A ∧ B ] ⊢ B ∧ A
∧-comm = ∧I (∧E₂ (prem here)) (∧E₁ (prem here))

∨-comm : ∀ {A B} → [ A ∨ B ] ⊢ B ∨ A
∨-comm = ∨E (∨I₂ (prem here)) (∨I₁ (prem here)) (prem here)

-- Absorb

∨-over-∧-absorb1 : ∀ {A B} → [ A ∨ (A ∧ B) ] ⊢ A
∨-over-∧-absorb1 = ∨E (prem here) (∧E₁ (prem here)) (prem here)

∨-over-∧-absorb2 : ∀ {A B} → [ A ] ⊢ A ∨ (A ∧ B)
∨-over-∧-absorb2 = ∨I₁ (prem here)

∧-over-∨-absorb1 : ∀ {A B} → [ A ∧ (A ∨ B) ] ⊢ A
∧-over-∨-absorb1 = ∧E₁ (prem here)

∧-over-∨-absorb2 : ∀ {A B} → [ A ] ⊢ A ∧ (A ∨ B)
∧-over-∨-absorb2 = ∧I (prem here) (∨I₁ (prem here))

-- Distrib

∨-over-∧-distrib1 : ∀ {A B C} → [ A ∨ (B ∧ C) ] ⊢ (A ∨ B) ∧ (A ∨ C)
∨-over-∧-distrib1 = ∧I
                      (∨E
                        (∨I₁ (prem here))
                        (∨I₂ (∧E₁ (prem here)))
                        (prem here))
                      (∨E
                        (∨I₁ (prem here))
                        (∨I₂ (∧E₂ (prem here)))
                        (prem here))

∨-over-∧-distrib2 : ∀ {A B C} → [ (A ∨ B) ∧ (A ∨ C) ] ⊢ A ∨ (B ∧ C)
∨-over-∧-distrib2 = ∨E
                      (∨I₁ (prem here))
                      (∨E
                        (∨I₁ (prem here))
                        (∨I₂ (∧I (prem (there here)) (prem here)))
                        (∧E₂ (prem (there here))))
                      (∧E₁ (prem here))

∧-over-∨-distrib1 : ∀ {A B C} → [ A ∧ (B ∨ C) ] ⊢ (A ∧ B) ∨ (A ∧ C)
∧-over-∨-distrib1 = ∨E
                      (∨I₁ (∧I
                             (∧E₁ (prem (there here)))
                             (prem here)))
                      (∨I₂ (∧I
                             (∧E₁ (prem (there here)))
                             (prem here)))
                      (∧E₂ (prem here))

∧-over-∨-distrib2 : ∀ {A B C} → [ (A ∧ B) ∨ (A ∧ C) ] ⊢ A ∧ (B ∨ C)
∧-over-∨-distrib2 = ∨E
                      (∧I
                        (∧E₁ (prem here))
                        (∨I₁
                          (∧E₂ (prem here))))
                      (∧I
                        (∧E₁ (prem here))
                        (∨I₂
                          (∧E₂ (prem here))))
                      (prem here)

-- lem

lem : ∀ {A} → [] ⊢ A ∨ (¬ A)
lem {A} = DNE (RAA {A = (¬ A)}
                (RAA {A = A ∨ (¬ A)}
                  (∨I₁ (prem here))
                  (prem (there here)))
                (RAA {A = A ∨ (¬ A)}
                  (∨I₂ (prem here))
                  (prem (there here))))

-- ex falso

ex-falso : ∀ {A B} → (A ∷ [ ¬ A ]) ⊢ B
ex-falso = DNE (RAA
                 (prem (there here))
                 (prem (there (there here))))

--

∨-restrict : ∀ {A B} → (¬ A ∷ A ∨ B ∷ []) ⊢ B
∨-restrict = ∨E
               (thin ex-falso (ths (ths (th' thz))))
               (prem here)
               (prem (there here))

-- modus tollens

modus-tollens : ∀ {A B} → (¬ B ∷ A ⊃ B ∷ []) ⊢ ¬ A
modus-tollens = RAA
                  (⊃E (prem (there (there here))) (prem here))
                  (prem (there here))

-- ⊃-∨ rules

⊃-to-∨ : ∀ {A B} → [ A ⊃ B ] ⊢ (¬ A) ∨ B
⊃-to-∨ {A} {B} = DNE (RAA {A = A}
                   (DNE (RAA {A = (¬ A) ∨ B}
                          (∨I₁ (prem here))
                          (prem (there here))))
                   (DNE (RAA {A = (¬ A) ∨ B}
                          (∨I₂ (⊃E
                                 (prem (there (there here)))
                                 (DNE (prem here))))
                          (prem (there here)))))


∨-to-⊃ : ∀ {A B} → [ (¬ A) ∨ B ] ⊢ A ⊃ B
∨-to-⊃ {A} {B} = ⊃I (DNE (RAA {A = A}
                           (prem (there here))
                           (∨E
                             (prem here)
                             (thin ex-falso (ths (ths (th' (th' thz)))))
                             (prem (there (there here))))))

-- Semantic Interpretation into the booleans

⟦_⟧𝒷 : Prop → (Nat → Bool) → Bool
⟦ var x ⟧𝒷 = λ f → f x
⟦ p ∧ q ⟧𝒷 = λ f → ⟦ p ⟧𝒷 f ∩ ⟦ q ⟧𝒷 f
⟦ p ∨ q ⟧𝒷 = λ f → ⟦ p ⟧𝒷 f ∪ ⟦ q ⟧𝒷 f
⟦ p ⊃ q ⟧𝒷 = λ f → ⟦ p ⟧𝒷 f ⇒ ⟦ q ⟧𝒷 f
⟦ ¬ p ⟧𝒷   = λ f → ~ (⟦ p ⟧𝒷 f)


_⊨_ : {n : Nat} → Vec Prop n → Prop → Set
Γ ⊨ A = (f : Nat → Bool) → (∀ {B} → Elem B Γ → ⟦ B ⟧𝒷 f ≡ true) → ⟦ A ⟧𝒷 f ≡ true

extendValidΓ : ∀ {n P f} {Γ : Vec Prop n} → (∀ {A} → Elem A Γ → ⟦ A ⟧𝒷 f ≡ true) → ⟦ P ⟧𝒷 f ≡ true → (∀ {B} → Elem B (P ∷ Γ) → ⟦ B ⟧𝒷 f ≡ true)
extendValidΓ as p here = p
extendValidΓ as p {B} (there el) = as el

-- Soundness Theorem
sysL-sound : ∀ {n} {Γ : Vec Prop n} {A : Prop} → Γ ⊢ A → Γ ⊨ A
sysL-sound (prem x) f p = p x
sysL-sound (∧I sq₁ sq₂) f p rewrite sysL-sound sq₁ f p | sysL-sound sq₂ f p = refl
sysL-sound (∧E₁ sq) f p = ∩-tt-l (sysL-sound sq f p)
sysL-sound (∧E₂ {A = A} sq) f p = ∩-tt-r {⟦ A ⟧𝒷 f} (sysL-sound sq f p)
sysL-sound (∨I₁ sq) f p rewrite sysL-sound sq f p = refl
sysL-sound (∨I₂ {A = A} sq) f p rewrite sysL-sound sq f p = ∪-r-tt-is-tt {⟦ A ⟧𝒷 f}
sysL-sound (∨E {A = A} {B} sq₁ sq₂ sq₃) f p with ∪-tt-evidence {⟦ A ⟧𝒷 f} {⟦ B ⟧𝒷 f} (sysL-sound sq₃ f p)
sysL-sound (∨E sq₁ sq₂ sq₃) f p | inl a = sysL-sound sq₁ f (extendValidΓ p a)
sysL-sound (∨E sq₁ sq₂ sq₃) f p | inr b = sysL-sound sq₂ f (extendValidΓ p b)
sysL-sound (⊃I {A = A} {B} sq) f p with bool-cases (⟦ A ⟧𝒷 f) | bool-cases (⟦ B ⟧𝒷 f)
sysL-sound (⊃I {A = A} {B} sq) f p | a | inl b-tt rewrite b-tt = refl
sysL-sound (⊃I {A = A} {B} sq) f p | inl a-tt | inr b-ff with ⟦ B ⟧𝒷 f | sysL-sound sq f (extendValidΓ p a-tt)
sysL-sound (⊃I {A = A} {B} sq) f p | inl a-tt | inr refl | .false | ()
sysL-sound (⊃I {A = A} {B} sq) f p | inr a-ff | inr b-ff rewrite a-ff | b-ff = refl
sysL-sound (⊃E {A = A} {B} sq₁ sq₂) f p with ⇒-tt-evidence {⟦ A ⟧𝒷 f} {⟦ B ⟧𝒷 f} (sysL-sound sq₁ f p)
sysL-sound (⊃E {A = A} {B} sq₁ sq₂) f p | inl b-tt = b-tt
sysL-sound (⊃E {A = A} {B} sq₁ sq₂) f p | inr (a-ff , _) with ⟦ A ⟧𝒷 f | sysL-sound sq₂ f p
sysL-sound (⊃E {A = A} {B} sq₁ sq₂) f p | inr (() , _) | .true | refl
sysL-sound (RAA {A = A} {B} sq₁ sq₂) f p with bool-cases (⟦ B ⟧𝒷 f)
sysL-sound (RAA {A = A} {B} sq₁ sq₂) f p | inl b-tt with ⟦ A ⟧𝒷 f | sysL-sound sq₁ f (extendValidΓ p b-tt) | sysL-sound sq₂ f (extendValidΓ p b-tt)
sysL-sound (RAA {A = A} {B} sq₁ sq₂) f p | inl b-tt | .true | refl | ()
sysL-sound (RAA {A = A} {B} sq₁ sq₂) f p | inr b-ff rewrite b-ff = refl
sysL-sound (DNE {A = A} sq) f p with sysL-sound sq f p
sysL-sound (DNE {A = A} sq) f p | a-tt rewrite ~~-elim {⟦ A ⟧𝒷 f} = a-tt
