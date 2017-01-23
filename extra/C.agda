module C where

-----------------------------------------------------------------------
-- Minimal Logic

-- Syntax
-- A ::= X | A → B

-- Rules:
-- Var axiom
-- →i
-- →e

-- Computationally:
-- variables, lambda expressions, and applications

-- We will assume additionally ∨ and ∧ for examples

open import Data.Sum
open import Data.Product

-- We can prove various things like:

id : {A : Set} → A → A
id a = a

mp : {A B : Set} → (A → B) → A → B
mp f a = f a

k : {A B : Set} → A → B → A
k a b = a

-----------------------------------------------------------------------
-- Intuitionistic Logic

-- add ⊥
-- add Ex Falso Quodlibet sequitur

-- Computationally, add an empty type

open import Data.Empty

EFQ : Set → Set
EFQ A = ⊥ → A

-- abort 
-- note: to write 𝓐 type \MCA etc.

𝓐'  : {A : Set} → EFQ A
𝓐' ()

𝓐 : {A : Set} → EFQ A
𝓐 p = ⊥-elim p

-- Define negation

¬ : Set → Set
¬ A = A → ⊥

-- Examples

contra : {A B : Set} → (A → B) → (¬ B → ¬ A)
contra f k a = k (f a)

or2fun : {A B : Set} → (¬ A ⊎ B) → (A → B)
or2fun (inj₁ k) a = ⊥-elim (k a)
or2fun (inj₂ b) a = b 

-----------------------------------------------------------------------
-- Classical Logic

-- add any of the following axioms to intuitionistic logic

PL⊥ EM DN : Set → Set
PL GEM : Set → Set → Set
PL⊥ A   = (¬ A → A) → A     -- Weak Peirce's Law
EM  A   = ¬ A ⊎ A           -- Excluded Middle
PL A B  = ((A → B) → A) → A -- Peirce's Law
GEM A B = (A → B) ⊎ A       -- Generalized Excluded Middle
DN A    = ¬ (¬ A) → A       -- Double Negation
  
-- Any of these gives some kind of classical logic but there are some
-- subtle differences

-- PL⊥ and EM are equivalent (as schemes)

EM→PL⊥ : {A : Set} → EM A → PL⊥ A
EM→PL⊥ (inj₁ k) f = f k
EM→PL⊥ (inj₂ a) f = a 

PL⊥→EM : {A : Set} → PL⊥ (¬ A ⊎ A) → EM A
PL⊥→EM f =  f (λ k → inj₁ (λ a → k (inj₂ a)))

-- GEM and PL are eqivalent (as schemes)

GEM→PL : {A B : Set} → GEM A B → PL A B
GEM→PL (inj₁ f) g = g f
GEM→PL (inj₂ a) g = a 

PL→GEM : {A B : Set} → PL ((A → B) ⊎ A) B → GEM A B
PL→GEM f = f (λ g → inj₁ (λ a → g (inj₂ a) ))

-- DN implies PL

DN→PL : {A : Set} → DN A → PL A ⊥
DN→PL f g = f (λ k → k (g k))

-- PL⊥+EFQ imply DN

PL⊥+EFQ→DN : {A : Set} → PL⊥ A → EFQ A → DN A
PL⊥+EFQ→DN f k kk = f (λ k' → k (kk k')) 

-- DN implies EFQ

DN→EFQ : {A : Set} → DN A → EFQ A
DN→EFQ f abs = f (λ k → abs)

-----------------------------------------------------------------------
-- Control operators

postulate
  𝓒 : {A : Set} → DN A

𝓚⊥ : {A : Set} → PL⊥ A
𝓚⊥ f = 𝓒 (λ c → c (f c))

𝓚 : {A B : Set} → PL A B
𝓚 f = 𝓒 (λ c → c (f (λ x → 𝓐 (c x))))

-- A → B is supposedly the same as ¬ A ∨ B

fun2or : {A B : Set} → (A → B) → (¬ A ⊎ B)
fun2or f = 𝓒 (λ k → k (inj₁ (λ a → k (inj₂ (f a)))))

-----------------------------------------------------------------------
-- Main observation:
--
-- Without EFQ we have three variants of classical logic:
-- 
--  * weak classical logic (with PL⊥ or EM)
--  * minimal classical logic (with PL or GEM)
--  * full classical logic (with DN)
-- Once we add EFQ the three variants collapse to one

-- Let's look more closely at EFQ, i.e., at the empty type ⊥ and at
-- the elimination rule ⊥ → A.

-- Computationally an expression is given type ⊥ because it never
-- returns (i.e., it is a jump to somewhere). There is a difference
-- though between jumping to the "top-level" and jumping to the middle
-- of an expression. When you jump to the middle of an expression it
-- is just a convenience as you can continue with a different path; it
-- doesn't indicate a global contradition. When you jump to the
-- top-level this is irrevocable. The computation terminates with an
-- "error", i.e., a contradition.

-- Logically ⊥ is the empty type, the proposition with no proof.
-- Absence of a top-level proof is a contradiction. Failure of an
-- intermediate step is milder; just try something else.

-----------------------------------------------------------------------
-- Minimal classical logic

-- Let us have two types:
-- ♯ to denote the result of jumping
-- ⊥ to denote contradition as before

-- We will not have any rules involving ⊥
-- If we want to get full classical logic, we add a rule ⊥ → ♯

data ♯ : Set where

-- All continuations have type A → ♯
-- Jumping to a continuation has type ♯
-- Once you capture a continuation you must immediately jump to a continuation !!!

postulate
  𝓒⁻ : {A : Set} → ((A → ♯) → ♯) → A

throw : {A B : Set} → (A → ♯) → A → B
throw k e = 𝓒⁻ (λ _ → k e)

𝓚⁻ : {A B : Set} → PL A B
𝓚⁻ f = 𝓒⁻ (λ c → c (f (λ a → throw c a)))

-- From Ron Garcia's notes

ex0 : {A : Set} → EM A 
ex0 = 𝓒⁻ (λ k → throw k (inj₁ (λ v → throw k (inj₂ v))))

ex1 : {A B C : Set} → (A → B ⊎ C) → (A → B) ⊎ (A → C)
ex1 f with ex0
... | inj₁ y = inj₁ (λ z → 𝓐 (y z))
... | inj₂ x with f x
... | inj₁ u = inj₁ (λ _ → u)
... | inj₂ w = inj₂ (λ _ → w) 

-- We do not validate EFQ or DN
-- If we wanted to do that we would need to add:

postulate
  tp : ⊥ → ♯

𝓒♯ : {A : Set} → DN A
𝓒♯ f = 𝓒⁻ (λ c → tp (f (λ a → throw c a)))

-----------------------------------------------------------------------

