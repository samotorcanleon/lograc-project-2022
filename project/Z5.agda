

module nekiprobavam where 
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
open import Data.Fin     using (Fin;zero;suc;fromℕ;toℕ;fromℕ<;_-_)
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



data Z₅ : Set where
  zero : Z₅
  one  : Z₅
  two  : Z₅
  three  : Z₅
  four  : Z₅

_+₅_ : (a : Z₅) → (b : Z₅) → Z₅
zero +₅ b = b
one +₅ zero = one
one +₅ one = two
one +₅ two = three
one +₅ three = four
one +₅ four = zero
two +₅ zero = two
two +₅ one = three
two +₅ two = four
two +₅ three = zero
two +₅ four = one
three +₅ zero = three
three +₅ one = four
three +₅ two = zero
three +₅ three = one
three +₅ four = two
four +₅ zero = four
four +₅ one = zero
four +₅ two = one
four +₅ three = two
four +₅ four = three

+₅-comm : (a b : Z₅) → a +₅ b ≡ b +₅ a
+₅-comm zero zero = refl
+₅-comm zero one = refl
+₅-comm zero two = refl
+₅-comm zero three = refl
+₅-comm zero four = refl
+₅-comm one zero = refl
+₅-comm one one = refl
+₅-comm one two = refl
+₅-comm one three = refl
+₅-comm one four = refl
+₅-comm two zero = refl
+₅-comm two one = refl
+₅-comm two two = refl
+₅-comm two three = refl
+₅-comm two four = refl
+₅-comm three zero = refl
+₅-comm three one = refl
+₅-comm three two = refl
+₅-comm three three = refl
+₅-comm three four = refl
+₅-comm four zero = refl
+₅-comm four one = refl
+₅-comm four two = refl
+₅-comm four three = refl
+₅-comm four four = refl

+₅-assoc : (a b c : Z₅) → (a +₅ b) +₅ c ≡ a +₅ (b +₅ c)
+₅-assoc zero b c = refl
+₅-assoc one zero c = refl
+₅-assoc one one zero = refl
+₅-assoc one one one = refl
+₅-assoc one one two = refl
+₅-assoc one one three = refl
+₅-assoc one one four = refl
+₅-assoc one two zero = refl
+₅-assoc one two one = refl
+₅-assoc one two two = refl
+₅-assoc one two three = refl
+₅-assoc one two four = refl
+₅-assoc one three zero = refl
+₅-assoc one three one = refl
+₅-assoc one three two = refl
+₅-assoc one three three = refl
+₅-assoc one three four = refl
+₅-assoc one four zero = refl
+₅-assoc one four one = refl
+₅-assoc one four two = refl
+₅-assoc one four three = refl
+₅-assoc one four four = refl
+₅-assoc two zero c = refl
+₅-assoc two one zero = refl
+₅-assoc two one one = refl
+₅-assoc two one two = refl
+₅-assoc two one three = refl
+₅-assoc two one four = refl
+₅-assoc two two zero = refl
+₅-assoc two two one = refl
+₅-assoc two two two = refl
+₅-assoc two two three = refl
+₅-assoc two two four = refl
+₅-assoc two three zero = refl
+₅-assoc two three one = refl
+₅-assoc two three two = refl
+₅-assoc two three three = refl
+₅-assoc two three four = refl
+₅-assoc two four zero = refl
+₅-assoc two four one = refl
+₅-assoc two four two = refl
+₅-assoc two four three = refl
+₅-assoc two four four = refl
+₅-assoc three zero c = refl
+₅-assoc three one zero = refl
+₅-assoc three one one = refl
+₅-assoc three one two = refl
+₅-assoc three one three = refl
+₅-assoc three one four = refl
+₅-assoc three two zero = refl
+₅-assoc three two one = refl
+₅-assoc three two two = refl
+₅-assoc three two three = refl
+₅-assoc three two four = refl
+₅-assoc three three zero = refl
+₅-assoc three three one = refl
+₅-assoc three three two = refl
+₅-assoc three three three = refl
+₅-assoc three three four = refl
+₅-assoc three four zero = refl
+₅-assoc three four one = refl
+₅-assoc three four two = refl
+₅-assoc three four three = refl
+₅-assoc three four four = refl
+₅-assoc four zero c = refl
+₅-assoc four one zero = refl
+₅-assoc four one one = refl
+₅-assoc four one two = refl
+₅-assoc four one three = refl
+₅-assoc four one four = refl
+₅-assoc four two zero = refl
+₅-assoc four two one = refl
+₅-assoc four two two = refl
+₅-assoc four two three = refl
+₅-assoc four two four = refl
+₅-assoc four three zero = refl
+₅-assoc four three one = refl
+₅-assoc four three two = refl
+₅-assoc four three three = refl
+₅-assoc four three four = refl
+₅-assoc four four zero = refl
+₅-assoc four four one = refl
+₅-assoc four four two = refl
+₅-assoc four four three = refl
+₅-assoc four four four = refl

_·₅_ : (a : Z₅) → (b : Z₅) → Z₅
zero ·₅ b = zero
one ·₅ b = b
b ·₅ zero = zero
b ·₅ one = b
two ·₅ two = four
two ·₅ three = one
two ·₅ four = three
three ·₅ two = one
three ·₅ three = four
three ·₅ four = two
four ·₅ two = three
four ·₅ three = two
four ·₅ four = one

·₅-comm : (a b : Z₅) → a ·₅ b ≡ b ·₅ a
·₅-comm zero zero = refl
·₅-comm zero one = refl
·₅-comm zero two = refl
·₅-comm zero three = refl
·₅-comm zero four = refl
·₅-comm one zero = refl
·₅-comm one one = refl
·₅-comm one two = refl
·₅-comm one three = refl
·₅-comm one four = refl
·₅-comm two zero = refl
·₅-comm two one = refl
·₅-comm two two = refl
·₅-comm two three = refl
·₅-comm two four = refl
·₅-comm three zero = refl
·₅-comm three one = refl
·₅-comm three two = refl
·₅-comm three three = refl
·₅-comm three four = refl
·₅-comm four zero = refl
·₅-comm four one = refl
·₅-comm four two = refl
·₅-comm four three = refl
·₅-comm four four = refl

·₅-assoc : (a b c : Z₅) → (a ·₅ b) ·₅ c ≡ a ·₅ (b ·₅ c)
·₅-assoc zero b c = refl
·₅-assoc one zero c = refl
·₅-assoc one one zero = refl
·₅-assoc one one one = refl
·₅-assoc one one two = refl
·₅-assoc one one three = refl
·₅-assoc one one four = refl
·₅-assoc one two zero = refl
·₅-assoc one two one = refl
·₅-assoc one two two = refl
·₅-assoc one two three = refl
·₅-assoc one two four = refl
·₅-assoc one three zero = refl
·₅-assoc one three one = refl
·₅-assoc one three two = refl
·₅-assoc one three three = refl
·₅-assoc one three four = refl
·₅-assoc one four zero = refl
·₅-assoc one four one = refl
·₅-assoc one four two = refl
·₅-assoc one four three = refl
·₅-assoc one four four = refl
·₅-assoc two zero c = refl
·₅-assoc two one zero = refl
·₅-assoc two one one = refl
·₅-assoc two one two = refl
·₅-assoc two one three = refl
·₅-assoc two one four = refl
·₅-assoc two two zero = refl
·₅-assoc two two one = refl
·₅-assoc two two two = refl
·₅-assoc two two three = refl
·₅-assoc two two four = refl
·₅-assoc two three zero = refl
·₅-assoc two three one = refl
·₅-assoc two three two = refl
·₅-assoc two three three = refl
·₅-assoc two three four = refl
·₅-assoc two four zero = refl
·₅-assoc two four one = refl
·₅-assoc two four two = refl
·₅-assoc two four three = refl
·₅-assoc two four four = refl
·₅-assoc three zero c = refl
·₅-assoc three one zero = refl
·₅-assoc three one one = refl
·₅-assoc three one two = refl
·₅-assoc three one three = refl
·₅-assoc three one four = refl
·₅-assoc three two zero = refl
·₅-assoc three two one = refl
·₅-assoc three two two = refl
·₅-assoc three two three = refl
·₅-assoc three two four = refl
·₅-assoc three three zero = refl
·₅-assoc three three one = refl
·₅-assoc three three two = refl
·₅-assoc three three three = refl
·₅-assoc three three four = refl
·₅-assoc three four zero = refl
·₅-assoc three four one = refl
·₅-assoc three four two = refl
·₅-assoc three four three = refl
·₅-assoc three four four = refl
·₅-assoc four zero c = refl
·₅-assoc four one zero = refl
·₅-assoc four one one = refl
·₅-assoc four one two = refl
·₅-assoc four one three = refl
·₅-assoc four one four = refl
·₅-assoc four two zero = refl
·₅-assoc four two one = refl
·₅-assoc four two two = refl
·₅-assoc four two three = refl
·₅-assoc four two four = refl
·₅-assoc four three zero = refl
·₅-assoc four three one = refl
·₅-assoc four three two = refl
·₅-assoc four three three = refl
·₅-assoc four three four = refl
·₅-assoc four four zero = refl
·₅-assoc four four one = refl
·₅-assoc four four two = refl
·₅-assoc four four three = refl
·₅-assoc four four four = refl

-₅ : (a : Z₅) → Z₅
-₅ zero = zero
-₅ one = four
-₅ two = three
-₅ three = two
-₅ four = one

-₅-left : (a : Z₅) → (-₅ a) +₅ a ≡ zero
-₅-left zero = refl
-₅-left one = refl
-₅-left two = refl
-₅-left three = refl
-₅-left four = refl

one-left : (a : Z₅) → one ·₅ a ≡ a
one-left a = refl

zero-left : (a : Z₅) → zero +₅ a ≡ a
zero-left a = refl

one≠zero : ¬ (one ≡ zero)
one≠zero ()

dist-Z₅ : ( b c a : Z₅) → (a ·₅ (b +₅ c)) ≡ ((a ·₅ b) +₅ (a ·₅ c))
dist-Z₅ zero zero zero = refl
dist-Z₅ zero zero one = refl
dist-Z₅ zero zero two = refl
dist-Z₅ zero zero three = refl
dist-Z₅ zero zero four = refl
dist-Z₅ zero one zero = refl
dist-Z₅ zero one one = refl
dist-Z₅ zero one two = refl
dist-Z₅ zero one three = refl
dist-Z₅ zero one four = refl
dist-Z₅ zero two zero = refl
dist-Z₅ zero two one = refl
dist-Z₅ zero two two = refl
dist-Z₅ zero two three = refl
dist-Z₅ zero two four = refl
dist-Z₅ zero three zero = refl
dist-Z₅ zero three one = refl
dist-Z₅ zero three two = refl
dist-Z₅ zero three three = refl
dist-Z₅ zero three four = refl
dist-Z₅ zero four zero = refl
dist-Z₅ zero four one = refl
dist-Z₅ zero four two = refl
dist-Z₅ zero four three = refl
dist-Z₅ zero four four = refl
dist-Z₅ one zero zero = refl
dist-Z₅ one zero one = refl
dist-Z₅ one zero two = refl
dist-Z₅ one zero three = refl
dist-Z₅ one zero four = refl
dist-Z₅ one one zero = refl
dist-Z₅ one one one = refl
dist-Z₅ one one two = refl
dist-Z₅ one one three = refl
dist-Z₅ one one four = refl
dist-Z₅ one two zero = refl
dist-Z₅ one two one = refl
dist-Z₅ one two two = refl
dist-Z₅ one two three = refl
dist-Z₅ one two four = refl
dist-Z₅ one three zero = refl
dist-Z₅ one three one = refl
dist-Z₅ one three two = refl
dist-Z₅ one three three = refl
dist-Z₅ one three four = refl
dist-Z₅ one four zero = refl
dist-Z₅ one four one = refl
dist-Z₅ one four two = refl
dist-Z₅ one four three = refl
dist-Z₅ one four four = refl
dist-Z₅ two zero zero = refl
dist-Z₅ two zero one = refl
dist-Z₅ two zero two = refl
dist-Z₅ two zero three = refl
dist-Z₅ two zero four = refl
dist-Z₅ two one zero = refl
dist-Z₅ two one one = refl
dist-Z₅ two one two = refl
dist-Z₅ two one three = refl
dist-Z₅ two one four = refl
dist-Z₅ two two zero = refl
dist-Z₅ two two one = refl
dist-Z₅ two two two = refl
dist-Z₅ two two three = refl
dist-Z₅ two two four = refl
dist-Z₅ two three zero = refl
dist-Z₅ two three one = refl
dist-Z₅ two three two = refl
dist-Z₅ two three three = refl
dist-Z₅ two three four = refl
dist-Z₅ two four zero = refl
dist-Z₅ two four one = refl
dist-Z₅ two four two = refl
dist-Z₅ two four three = refl
dist-Z₅ two four four = refl
dist-Z₅ three zero zero = refl
dist-Z₅ three zero one = refl
dist-Z₅ three zero two = refl
dist-Z₅ three zero three = refl
dist-Z₅ three zero four = refl
dist-Z₅ three one zero = refl
dist-Z₅ three one one = refl
dist-Z₅ three one two = refl
dist-Z₅ three one three = refl
dist-Z₅ three one four = refl
dist-Z₅ three two zero = refl
dist-Z₅ three two one = refl
dist-Z₅ three two two = refl
dist-Z₅ three two three = refl
dist-Z₅ three two four = refl
dist-Z₅ three three zero = refl
dist-Z₅ three three one = refl
dist-Z₅ three three two = refl
dist-Z₅ three three three = refl
dist-Z₅ three three four = refl
dist-Z₅ three four zero = refl
dist-Z₅ three four one = refl
dist-Z₅ three four two = refl
dist-Z₅ three four three = refl
dist-Z₅ three four four = refl
dist-Z₅ four zero zero = refl
dist-Z₅ four zero one = refl
dist-Z₅ four zero two = refl
dist-Z₅ four zero three = refl
dist-Z₅ four zero four = refl
dist-Z₅ four one zero = refl
dist-Z₅ four one one = refl
dist-Z₅ four one two = refl
dist-Z₅ four one three = refl
dist-Z₅ four one four = refl
dist-Z₅ four two zero = refl
dist-Z₅ four two one = refl
dist-Z₅ four two two = refl
dist-Z₅ four two three = refl
dist-Z₅ four two four = refl
dist-Z₅ four three zero = refl
dist-Z₅ four three one = refl
dist-Z₅ four three two = refl
dist-Z₅ four three three = refl
dist-Z₅ four three four = refl
dist-Z₅ four four zero = refl
dist-Z₅ four four one = refl
dist-Z₅ four four two = refl
dist-Z₅ four four three = refl
dist-Z₅ four four four = refl

dec-Z₅ : (a b : Z₅) → Dec (a ≡ b)
dec-Z₅ zero zero = yes refl
dec-Z₅ zero one = no λ ()
dec-Z₅ zero two = no λ ()
dec-Z₅ zero three = no λ ()
dec-Z₅ zero four = no λ ()
dec-Z₅ one zero = no λ ()
dec-Z₅ one one = yes refl
dec-Z₅ one two = no λ ()
dec-Z₅ one three = no λ ()
dec-Z₅ one four = no λ ()
dec-Z₅ two zero = no λ ()
dec-Z₅ two one = no λ ()
dec-Z₅ two two = yes refl
dec-Z₅ two three = no λ ()
dec-Z₅ two four = no λ ()
dec-Z₅ three zero = no λ ()
dec-Z₅ three one = no λ ()
dec-Z₅ three two = no λ ()
dec-Z₅ three three = yes refl
dec-Z₅ three four = no λ ()
dec-Z₅ four zero = no λ ()
dec-Z₅ four one = no λ ()
dec-Z₅ four two = no λ ()
dec-Z₅ four three = no λ ()
dec-Z₅ four four = yes refl 

nzd-Z₅ : {a b : Z₅} → ¬ (a ≡ zero) → ¬ (b ≡ zero) → ¬ ((a ·₅ b) ≡ zero)
nzd-Z₅ {zero} {b} x y = x
nzd-Z₅ {one} {zero} x y = y
nzd-Z₅ {one} {one} x y = y
nzd-Z₅ {one} {two} x y = y
nzd-Z₅ {one} {three} x y = y
nzd-Z₅ {one} {four} x y = y
nzd-Z₅ {two} {zero} x y = y
nzd-Z₅ {two} {one} x y = x
nzd-Z₅ {two} {two} x y ()
nzd-Z₅ {two} {three} x y ()
nzd-Z₅ {two} {four} x y ()
nzd-Z₅ {three} {zero} x y = y
nzd-Z₅ {three} {one} x y = x
nzd-Z₅ {three} {two} x y ()
nzd-Z₅ {three} {three} x y ()
nzd-Z₅ {three} {four} x y ()
nzd-Z₅ {four} {zero} x y = y
nzd-Z₅ {four} {one} x y ()
nzd-Z₅ {four} {two} x y  ()
nzd-Z₅ {four} {three} x y  ()
nzd-Z₅ {four} {four} x y  ()

ℤ₅ : Ring
ℤ₅ = record { M = Z₅ ;
    1ᵣ = one ;
    _·_  = _·₅_  ;
    e₊ = zero ;
    _+ᵣ_ = _+₅_ ;
    -ᵣ_ = -₅ ;
    -ᵣ-left = -₅-left ;
    1ᵣ-left  = one-left ;
    ·-assoc = ·₅-assoc ;
    ·-comm = ·₅-comm ;
    ω-left  = zero-left ;
    +-assoc = +₅-assoc ;
    +-comm = +₅-comm ;
    dist-l = dist-Z₅ ;
    dec = dec-Z₅ ;
    nzd = nzd-Z₅ ;
    1ᵣ≠e₊ = one≠zero}

  