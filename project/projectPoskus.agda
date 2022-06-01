

module projectPoskus where 
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
-- open import Data.List using (List; []; _∷_; length)


open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_;_%_; NonZero )
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_; curry; uncurry)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (Vec; []; _∷_)
open import Data.Bool    using (Bool; true; false)
open import Data.Fin     using (Fin;zero;suc;fromℕ;toℕ;fromℕ<;_-_;opposite; Fin′)
open import Data.Nat.DivMod using (m%n<n )

open import Function     using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≢_;_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b


¬_ : Set → Set
¬ A = A → ⊥

neki : ¬ (2 ≡ 4)
neki ()

dcong : ∀ {A : Set} {B : A → Set} (f : (x : A) → B x) {x y}
      → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f refl = refl

dcong₂ : ∀ {A : Set} {B : A → Set} {C : Set}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
       → f x₁ y₁ ≡ f x₂ y₂
dcong₂ f refl refl = refl



data Dec A : Set where
  yes : A → Dec A 
  no : (¬ A) → Dec A

  

record Ring : Set₁  where
  constructor RingCons
  infixl 7 _·_
  infixl 5 _+ᵣ_
  field
    M : Set

    
    -- identity element for multiplication (unicode with `\epsilon`)
    1ᵣ : M
    -- binary operation multiplication (unicode with `\cdot`)
    _·_     : M → M → M

    -- identity element for addition (unicode with `\epsilon`)
    e₊ : M
    -- binary operation addition
    _+ᵣ_     : M → M → M

    -ᵣ_ : M → M

    -ᵣ-left  : (m : M) → (-ᵣ m) +ᵣ m ≡ e₊
    -- nonzeroring
    1ᵣ≠e₊ :  ¬ (1ᵣ ≡ e₊)
    -- ring laws
    1ᵣ-left  : (m : M) → 1ᵣ · m ≡ m
    ·-assoc : (m₁ m₂ m₃ : M) → (m₁ · m₂) · m₃ ≡ m₁ · (m₂ · m₃)
    ·-comm : (m₁ m₂ : M) → m₁ · m₂ ≡  m₂ · m₁

    ω-left  : (m : M) → e₊ +ᵣ m ≡ m
    +-assoc : (m₁ m₂ m₃ : M) → (m₁ +ᵣ m₂) +ᵣ m₃ ≡ m₁ +ᵣ (m₂ +ᵣ m₃)
    +-comm : (m₁ m₂ : M) → m₁ +ᵣ m₂ ≡  m₂ +ᵣ m₁

    dist-l : (m₁ m₂ m₃ : M) → m₃ · (m₁ +ᵣ m₂) ≡ (m₃ · m₁) +ᵣ (m₃ · m₂)

    dec : (x y : M) → Dec(x ≡ y)
    -- no zero divisors 
    nzd : {x y : M}  → ¬ (x ≡ e₊) → ¬ (y ≡ e₊) → ¬ ((x · y) ≡ e₊)
 
open Ring

nz5 : NonZero 5
nz5 = record { nonZero = tt }

data Z₅ : Set where
  zero : Z₅
  suc  : (n : Z₅) → Z₅



_+z₅_ : (a : Fin 5) → (b : Fin 5) → Fin 5
_+z₅_ a b =  fromℕ<  (m%n<n ((((toℕ a) + (toℕ b)) % 5 ) ⦃ nz5 ⦄  ) 5)

+5-comm : (a b : Fin 5) →  a +z₅ b ≡ b +z₅ a
+5-comm zero zero = refl
+5-comm zero (suc b) = {!   !}
+5-comm (suc a) b = {!   !} 

-z₅ : Fin 5 → Fin 5
-z₅ zero = zero
-z₅ (suc m) = fromℕ<  (m%n<n ((((toℕ (opposite (suc m))) + 1) % 5 ) ⦃ nz5 ⦄  ) 5)

-ᵣ-left5 : (m : Fin 5) → (-z₅ m +z₅ m) ≡ zero
-ᵣ-left5 zero = refl
-ᵣ-left5 (suc zero) = refl
-ᵣ-left5 (suc (suc zero)) = refl
-ᵣ-left5 (suc (suc (suc zero))) = refl
-ᵣ-left5 (suc (suc (suc (suc zero)))) = refl



prf : ℕ
prf = (7 % 5) ⦃ nz5 ⦄
ℤ₅ : Ring
ℤ₅ = record { M = Fin 5;
    1ᵣ = suc zero ;
    _·_  = {!   !}  ;
    e₊ = zero ;
    _+ᵣ_ = _+z₅_    ;
    -ᵣ_ = -z₅ ;
    -ᵣ-left = -ᵣ-left5 ;
    1ᵣ-left  = {!   !} ;
    ·-assoc = {!   !} ;
    ·-comm = {!   !} ;
    ω-left  = {!   !} ;
    +-assoc = {!   !} ;
    +-comm = {!   !} ;
    dist-l = {!   !} ;
    dec = {!   !} ;
    nzd = {!   !} ;
    1ᵣ≠e₊ = {!   !}
                }



 