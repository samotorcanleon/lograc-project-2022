module asocposkus where 
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
-- open import Data.List using (List; []; _∷_; length)


open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_;_%_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_; curry; uncurry)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (Vec; []; _∷_)
open import Data.Bool    using (Bool; true; false)

open import Function     using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≢_;_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b


¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

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

x+a=0=x+b→a=b : {A : Ring} → (x a b : M A) → (_+ᵣ_ A) x a ≡ (e₊ A) →  (_+ᵣ_ A) x b ≡ (e₊ A) → a ≡ b 
x+a=0=x+b→a=b {A} x a b h k = hlp2 hlp1
  where 
    hlp1 :  ((A +ᵣ x) a ≡ (A +ᵣ x) b)
    hlp1 = trans h (sym k)
    hlp3 : (x : M A) →  a ≡ b → (A +ᵣ x) a ≡ (A +ᵣ x) b 
    hlp3 x p = cong₂ (_+ᵣ_ A) refl p
    hlp4 : (x a : M A) →   (A +ᵣ ((-ᵣ A) x)) ((A +ᵣ x) a) ≡  a
    hlp4 x a =  begin (A +ᵣ (-ᵣ A) x) ((A +ᵣ x) a)  ≡⟨ sym((+-assoc A) ((-ᵣ A) x) x a) ⟩ (A +ᵣ ((A +ᵣ ((-ᵣ A) x)) x) ) a ≡⟨ cong₂ (_+ᵣ_ A) ((-ᵣ-left A) x) refl ⟩ (A +ᵣ (e₊ A) ) a ≡⟨ ω-left A a ⟩ a ∎
    hlp2 : ((A +ᵣ x) a ≡ (A +ᵣ x) b) → a ≡ b 
    hlp2 p =  begin a  ≡⟨ sym (hlp4 x a) ⟩ (A +ᵣ ((-ᵣ A) x)) ((A +ᵣ x) a) ≡⟨ cong₂ (_+ᵣ_ A) refl hlp1 ⟩ (A +ᵣ ((-ᵣ A) x)) ((A +ᵣ x) b) ≡⟨ hlp4 x b ⟩ b  ∎
-- (hlp3 ((-ᵣ A) x) p)

a+x=0=b+x→a=b : {A : Ring} → (x a b : M A) → (_+ᵣ_ A) a x ≡ (e₊ A) →  (_+ᵣ_ A) b x ≡ (e₊ A) → a ≡ b 
a+x=0=b+x→a=b {A} x a b h k = x+a=0=x+b→a=b {A} x a b ((trans ((+-comm A) x a) h)) ((trans ((+-comm A) x b) k))
x+a=x+b→a+x=b+x : {A : Ring} → (x a b : M A) → (_+ᵣ_ A) x a ≡ (_+ᵣ_ A) x b →  (_+ᵣ_ A)  a x ≡ (_+ᵣ_ A) b x 
x+a=x+b→a+x=b+x {A} x a b h = trans (trans (+-comm A a x) h) (+-comm A x b)
a+x=b+x→x+a=x+b : {A : Ring} → (x a b : M A) → (_+ᵣ_ A) a x ≡ (_+ᵣ_ A) b x →  (_+ᵣ_ A)  x a ≡ (_+ᵣ_ A) x b 
a+x=b+x→x+a=x+b {A} x a b h = trans (trans (+-comm A x a) h) (+-comm A b x)
a+x=b+x→a=b : {A : Ring} → (x a b : M A) → (_+ᵣ_ A) a x ≡  (_+ᵣ_ A) b x  → a ≡ b 
a+x=b+x→a=b {A} x a b h = begin a  ≡⟨ sym (hlp4 x a) ⟩ (A +ᵣ ((-ᵣ A) x)) ((A +ᵣ x) a) ≡⟨ cong₂  (_+ᵣ_ A) refl (a+x=b+x→x+a=x+b {A}x a b h) ⟩ (A +ᵣ ((-ᵣ A) x)) ((A +ᵣ x) b) ≡⟨ hlp4 x b ⟩ b ∎
  where 
    hlp4 : (x a : M A) →   (A +ᵣ ((-ᵣ A) x)) ((A +ᵣ x) a) ≡  a
    hlp4 x a =  begin (A +ᵣ (-ᵣ A) x) ((A +ᵣ x) a)  ≡⟨ sym((+-assoc A) ((-ᵣ A) x) x a) ⟩ (A +ᵣ ((A +ᵣ ((-ᵣ A) x)) x) ) a ≡⟨ cong₂ (_+ᵣ_ A) ((-ᵣ-left A) x) refl ⟩ (A +ᵣ (e₊ A) ) a ≡⟨ ω-left A a ⟩ a ∎

x+a=x+b→a=b : {A : Ring} → (x a b : M A) → (_+ᵣ_ A) x a ≡  (_+ᵣ_ A) x b  → a ≡ b 
x+a=x+b→a=b {A} x a b h = a+x=b+x→a=b {A} x a b (x+a=x+b→a+x=b+x {A} x a b h )

≢e₊-irrelevant : ∀ {A} {a : M A} → (p q : ¬ (a ≡ (e₊ A))) → p ≡ q
≢e₊-irrelevant p q = fun-ext (λ r → ⊥-elim (p r))

data NonZeroPoly (A : Ring): Set where 
  ld : (a : M A)  → ¬ (a ≡ (e₊ A)) →  NonZeroPoly A
  _∷ₚ_ : (M A)  → NonZeroPoly A -> NonZeroPoly A

data Poly  (A : Ring): Set where 
  0ₚ : Poly A
  non0ₚ : NonZeroPoly A → Poly A


data sum-zero {A : Ring} :  (p q : NonZeroPoly A) → Set where 
  ld0 : (a b : M A) → (pa : ¬ (a ≡ (e₊ A))) → (pb : ¬ (b ≡ (e₊ A))) → ((_+ᵣ_ A) a b) ≡ (e₊ A) → sum-zero (ld a pa) (ld b pb)
  ∷0  : (a b : M A) → (p q : NonZeroPoly A) → ((_+ᵣ_ A) a b) ≡ (e₊ A) → sum-zero p q → sum-zero (a ∷ₚ p) (b ∷ₚ q)

-- data sum-zero-Poly {A : Ring}  :  (p q : Poly A) → Set where 
  -- 0ₚ-≡ : sum-zero-Poly 0ₚ 0ₚ
  -- n0ₚ-≡ : (p q : NonZeroPoly A) → (sum-zero p q) →  sum-zero-Poly  (non0ₚ p) (non0ₚ q)

data sum-nonzero {A : Ring} :  (p q : NonZeroPoly A) → Set where 
  ldld : (a b : M A) → (pab : ¬ ((_+ᵣ_ A) a b  ≡ (e₊ A))) → (pa : ¬ (a ≡ (e₊ A))) → (pb : ¬ (b ≡ (e₊ A))) → sum-nonzero (ld a pa) (ld b pb) 
  ∷ld  : (a b : M A) → (pb : ¬ (b ≡ (e₊ A))) → (p : NonZeroPoly A)  → sum-nonzero (a ∷ₚ p) (ld b pb) 
  ld∷  : (a b : M A) → (pa : ¬ (a ≡ (e₊ A))) → (q : NonZeroPoly A)  → sum-nonzero (ld a pa) (b ∷ₚ q)
  ∷∷rek  : (a b : M A)  → (p q : NonZeroPoly A) → sum-nonzero p q → sum-nonzero (a ∷ₚ p) (b ∷ₚ q)
  ∷∷lok  : (a b : M A)  → (p q : NonZeroPoly A) → (pab : ¬ ((_+ᵣ_ A) a b  ≡ (e₊ A))) → sum-nonzero (a ∷ₚ p) (b ∷ₚ q)

addp2 : {A : Ring} → (p q : NonZeroPoly A) → (NonZeroPoly A)  ⊎ (sum-zero p q)
addp2 {A} (ld ha pa) (ld hb pb) with ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A) )
... | yes x = inj₂ (ld0 ha hb pa pb x)
... | no x = inj₁ ( ld  ((_+ᵣ_ A) ha  hb) x)
addp2 {A} (ld ha pa) (hb ∷ₚ tb) = inj₁ (((_+ᵣ_ A) ha  hb) ∷ₚ tb)
addp2 {A} (ha ∷ₚ ta) (ld hb pb) = inj₁ (((_+ᵣ_ A) ha  hb) ∷ₚ ta)
addp2 {A} (ha ∷ₚ ta) (hb ∷ₚ tb) with (addp2 ta tb) | ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A) )
... | inj₁ x | res2 = inj₁( ((_+ᵣ_ A) ha  hb) ∷ₚ x)
... | inj₂ y | yes p = inj₂ (∷0 ha hb ta tb p y)
... | inj₂ y | no p = inj₁ (ld ((_+ᵣ_ A) ha  hb) p) 

-- ce ne gre dodaj da vrne nonzero ali pa dokaz da se vsi naprej sestejejo v 0
addp : {A : Ring} → (x y : NonZeroPoly A) → Maybe (NonZeroPoly A)
addp {A} (ld ha pa) (ld hb pb) with ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A) )
...     | yes p = nothing  --vsota je 0
...     | no p = just (ld ((_+ᵣ_ A) ha  hb) p) 
addp {A} (ld ha p) (hb ∷ₚ tb) = just (((_+ᵣ_ A) ha  hb) ∷ₚ tb)
addp (ha ∷ₚ ta) (ld b x) = addp (ld b x) (ha ∷ₚ ta)
addp {A} (ha ∷ₚ ta) (hb ∷ₚ tb) with (addp ta tb) 
...     | just res = just (((_+ᵣ_ A) ha  hb) ∷ₚ res)
...     | nothing with ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A))
...               | yes p = nothing
...               | no p = just (ld ((_+ᵣ_ A) ha  hb) p)

a+b=b+a=e : {A : Ring} → (a b : M A) → (A +ᵣ a) b ≡ e₊ A → (A +ᵣ b) a ≡ e₊ A
a+b=b+a=e {A} a b p = begin (A +ᵣ b) a   ≡⟨ (+-comm A) b a ⟩ (A +ᵣ a) b ≡⟨ p ⟩ e₊ A ∎
justnoth⊥ : {X : Set}{x : X} →  nothing ≡ just x → ⊥
justnoth⊥ ()

addp-comm : {A : Ring} → (p q : NonZeroPoly A) → addp p q ≡ addp q p 
addp-comm {A} (ld a x) (ld b y) with ( dec A ((A +ᵣ a) b) (e₊ A)) | inspect ( dec A ((A +ᵣ a) b) ) (e₊ A)
... | no p | [ eq ] with dec A ((A +ᵣ b) a) (e₊ A)
... | no p2 = cong just (dcong₂ ld ((+-comm A) a b) refl)
... | yes p2 with p (a+b=b+a=e {A} b a p2 )
... | ()
addp-comm {A} (ld a x) (ld b y) | yes p | [ eq ] with ( dec A ((A +ᵣ b) a) (e₊ A)) | inspect ( dec A ((A +ᵣ b) a) ) (e₊ A)
... | yes x₁ | [ eq₁ ] = refl
... | no p2 | [ eq₁ ] with ¬-elim p2 (a+b=b+a=e {A} a b p)
... | ()
addp-comm {A} (ld a x) (x₁ ∷ₚ q) = cong just refl
addp-comm {A} (x ∷ₚ p) (ld a x₁) = cong just refl
addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) with addp p q | inspect (addp p) q | addp q p | inspect (addp q) p
... | just x | [ eq ] | just y | [ eq2 ] = cong just (cong₂ _∷ₚ_ ((+-comm A) a b) (hlp (x=yjust  eq2 eq)))
  where 
    x=yjust : addp q p ≡ just y → addp p q ≡ just x → just x ≡ just y 
    x=yjust p1 p2 = begin just x   ≡⟨ sym p2 ⟩ addp p q ≡⟨ addp-comm p q ⟩ addp q p ≡⟨ p1 ⟩ just y ∎
    hlp : just x ≡ just y → x ≡ y 
    hlp refl = refl

... | just x₂ | [ eq ] | nothing | [ eq₁ ] with justnoth⊥ (trans (sym eq₁) (trans  (addp-comm q p) eq))
... | ()
addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | just x | [ eq₁ ] with justnoth⊥ (trans (sym  eq) (trans (addp-comm p q) eq₁))
... | ()
addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] with ( dec A ((A +ᵣ b) a) (e₊ A)) |  ( dec A ((A +ᵣ a) b) (e₊ A))
... | yes x | yes x₁ = refl
... | yes x | no y  with ¬-elim y (a+b=b+a=e {A} b a  x)
... | () 
addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] | no x | yes y with ¬-elim x (a+b=b+a=e {A}  a b  y)
... | ()
addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] | no x | no y = cong just (dcong₂ ld ((+-comm A) a b) refl)



_+ₚ_ : {A : Ring} → (a : Poly A )→ (b : Poly A) → Poly A
0ₚ +ₚ b = b
non0ₚ x +ₚ 0ₚ = non0ₚ x
non0ₚ x +ₚ non0ₚ y with addp x y 
... | just res = non0ₚ res
... | nothing = 0ₚ


+ₚ-comm :  {A : Ring} → (p q : Poly A ) → p +ₚ q ≡ q +ₚ p 
+ₚ-comm {A} 0ₚ 0ₚ = refl
+ₚ-comm {A} 0ₚ (non0ₚ x) = refl
+ₚ-comm {A} (non0ₚ x) 0ₚ = refl
+ₚ-comm {A} (non0ₚ p) (non0ₚ q) with addp p q | inspect (addp p) q | addp q p | inspect (addp q) p
... | just x | [ eq ] | just y | [ eq₁ ] = cong non0ₚ (hlp (x=yjust eq₁ eq))
  where 
    x=yjust : addp q p ≡ just y → addp p q ≡ just x → just x ≡ just y 
    x=yjust p1 p2 = begin just x   ≡⟨ sym p2 ⟩ addp p q ≡⟨ addp-comm p q ⟩ addp q p ≡⟨ p1 ⟩ just y ∎
    hlp : just x ≡ just y → x ≡ y 
    hlp refl = refl
... | just x | [ eq ] | nothing | [ eq₁ ] with justnoth⊥ (trans (sym eq₁) (trans (addp-comm q p) eq))
... | ()
+ₚ-comm {A} (non0ₚ p) (non0ₚ q) | nothing | [ eq ] | just y | [ eq₁ ] with justnoth⊥ (sym (trans (sym eq₁) (trans (addp-comm q p) eq)))
... | ()
+ₚ-comm {A} (non0ₚ p) (non0ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] = refl



+ₚ-asoc : {A : Ring} → (p q r : Poly A) → p +ₚ (q +ₚ r) ≡ (p +ₚ q) +ₚ r
+ₚ-asoc 0ₚ 0ₚ 0ₚ = refl
+ₚ-asoc 0ₚ 0ₚ (non0ₚ x) = refl
+ₚ-asoc 0ₚ (non0ₚ x) r = refl
+ₚ-asoc (non0ₚ x) 0ₚ r = refl
+ₚ-asoc (non0ₚ p) (non0ₚ q) 0ₚ = begin (non0ₚ p +ₚ (non0ₚ q +ₚ 0ₚ))   ≡⟨ refl ⟩ (0ₚ +ₚ (non0ₚ p +ₚ non0ₚ q)) ≡⟨ +ₚ-comm 0ₚ (non0ₚ p +ₚ non0ₚ q) ⟩ ((non0ₚ p +ₚ non0ₚ q) +ₚ 0ₚ) ∎
+ₚ-asoc {A} (non0ₚ (ld ha pa)) (non0ₚ (ld hb pb)) (non0ₚ (ld hc pc)) with dec A ((A +ᵣ hb) hc) (e₊ A) | addp {A} (ld hb pb) (ld hc pc) | inspect (addp {A} (ld hb pb)) (ld hc pc)|  dec A ((A +ᵣ ha) hb) (e₊ A) | addp {A} (ld ha pa) (ld hb pb) | inspect (addp {A} (ld ha pa)) (ld hb pb)
... | yes x | just x₁ | [ eq ] | yes x₂ | just x₃ | [ eq₁ ] with addp (ld ha pa) x₁ | inspect (addp (ld ha pa)) x₁ | addp x₃ (ld hc pc) | inspect (addp x₃) (ld hc pc) | dec A ((A +ᵣ ha) hb) (e₊ A) | dec A ((A +ᵣ hb) hc) (e₊ A)
... | just x₄ | [ eq₂ ] | just x₅ | [ eq₃ ] | no x₆ | no x₇ = {!   !}
... | just x₄ | [ eq₂ ] | nothing | [ eq₃ ] | d1 | d2 = {!   !}
... | nothing | [ eq₂ ] | just x₄ | [ eq₃ ] | d1 | d2 = {!   !}
... | nothing | [ eq₂ ] | nothing | [ eq₃ ] | d1 | d2 = refl
+ₚ-asoc {A} (non0ₚ (ld ha pa)) (non0ₚ (ld hb pb)) (non0ₚ (ld hc pc)) | yes x | just x₁ | [ eq ] | yes x₂ | nothing | [ eq₁ ] = {!   !}
+ₚ-asoc {A} (non0ₚ (ld ha pa)) (non0ₚ (ld hb pb)) (non0ₚ (ld hc pc)) | yes x | just x₁ | [ eq ] | no x₂ | r2 | [ eq₁ ] = {!   !}
+ₚ-asoc {A} (non0ₚ (ld ha pa)) (non0ₚ (ld hb pb)) (non0ₚ (ld hc pc)) | yes x | nothing | [ eq ] | d2 | r2 | [ eq₁ ] = {!   !}
+ₚ-asoc {A} (non0ₚ (ld ha pa)) (non0ₚ (ld hb pb)) (non0ₚ (ld hc pc)) | no x | r1 | [ eq ] | d2 | r2 | [ eq₁ ] = {!   !}

-- with addp (ld ha pa) x | inspect (addp (ld ha pa)) x | addp y (ld hc pc) | inspect (addp y) (ld hc pc) 



+ₚ-asoc {A} (non0ₚ (ld a x)) (non0ₚ (ld a₁ x₁)) (non0ₚ (x₂ ∷ₚ r)) = {!   !}
+ₚ-asoc {A} (non0ₚ (ld a x)) (non0ₚ (x₁ ∷ₚ q)) (non0ₚ r) = {!   !}
+ₚ-asoc {A} (non0ₚ (x ∷ₚ p)) (non0ₚ q) (non0ₚ r) = {!   !}

--  /////////////////////
∷ₚ-injh : {A : Ring} → ∀ {a b : M A} → ∀ {c d : NonZeroPoly A} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  a ≡ b 
∷ₚ-injh refl = refl
∷ₚ-injt : {A : Ring} → ∀ {a b : M A} → ∀ {c d : NonZeroPoly A} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  c ≡ d 
∷ₚ-injt refl = refl
ld-inj : {A : Ring} →  ∀ {a b : M A} → ∀ {c d} → (ld {A} a c) ≡ (ld b d) → a ≡ b
ld-inj refl = refl
∷ₚ-≡ : {A : Ring} → {a b : M A} → ∀ {c d : NonZeroPoly A} → a ≡ b → c ≡ d  → (a ∷ₚ c) ≡ (b ∷ₚ d)
∷ₚ-≡ {A} refl refl = refl 
ld-≡ : {A : Ring} → ∀ {a b : M A} → ∀ {c d} → a ≡ b → (ld {A} a c) ≡ (ld b d)
ld-≡ {A}{a}{b}{c}{d} p with (dec A) a (e₊ A)
ld-≡ {A} {.(e₊ A)} {.(e₊ A)} {c} {d} refl | yes refl = refl
ld-≡ {A} {a} {.a} {c} {d} refl | no x = refl
-- ≢e₊-irrelevant : ∀ {A} {a : M A} → (p q : ¬ (a ≡ (e₊ A))) → p ≡ q
-- ≢e₊-irrelevant p q = fun-ext (λ r → ⊥-elim (p r))

