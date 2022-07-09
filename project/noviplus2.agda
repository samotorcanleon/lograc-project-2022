module noviplus2 where
open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_) renaming (_+_ to _+ⁿ_; _*_ to _*ⁿ_)
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
  infix 9 -_
  infixl 7 _·_
  infixl 5 _+_
  field
    M : Set

    -- identity element for multiplication (unicode with `\epsilon`)
    𝟙 : M
    -- binary operation multiplication (unicode with `\cdot`)
    _·_     : M → M → M

    -- identity element for addition (unicode with `\epsilon`)
    𝟘 : M
    -- binary operation addition
    _+_     : M → M → M

    -_ : M → M

    -left  : (m : M) → (- m) + m ≡ 𝟘
    -- nonzeroring
    𝟙≠𝟘 :  ¬ (𝟙 ≡ 𝟘)
    -- ring laws
    𝟙-left  : (m : M) → 𝟙 · m ≡ m
    ·-assoc : (m₁ m₂ m₃ : M) → (m₁ · m₂) · m₃ ≡ m₁ · (m₂ · m₃)
    ·-comm : (m₁ m₂ : M) → m₁ · m₂ ≡  m₂ · m₁

    ω-left  : (m : M) → 𝟘 + m ≡ m
    +-assoc : (m₁ m₂ m₃ : M) → (m₁ + m₂) + m₃ ≡ m₁ + (m₂ + m₃)
    +-comm : (m₁ m₂ : M) → m₁ + m₂ ≡  m₂ + m₁

    dist-l : (m₁ m₂ m₃ : M) → m₃ · (m₁ + m₂) ≡ (m₃ · m₁) + (m₃ · m₂)

    dec : (x y : M) → Dec(x ≡ y)
    -- no zero divisors
    nzd : {x y : M}  → ¬ (x ≡ 𝟘) → ¬ (y ≡ 𝟘) → ¬ ((x · y) ≡ 𝟘)

module RingProofs {A : Ring} where

  open Ring A

  
  x+a=0=x+b→a=b :  (x a b : M ) →  x + a ≡ 𝟘 →  x + b ≡ 𝟘 → a ≡ b 
  x+a=0=x+b→a=b  x a b h k = hlp2 hlp1
    where 
      hlp1 :  x + a ≡  x + b
      hlp1 = trans h (sym k)
      hlp3 : (x : M ) →  a ≡ b →  x + a ≡ x + b 
      hlp3 x p = cong₂ _+_ refl p
      hlp4 : (x a : M ) →  (- x) + (x + a) ≡  a
      hlp4 x a =  begin   (- x) + (x + a)  
                                          ≡⟨ sym((+-assoc ) (- x) x a) ⟩
                          ((- x) + x) + a 
                                          ≡⟨ cong₂ (_+_) (-left x) refl ⟩ 
                          𝟘 + a 
                                          ≡⟨ ω-left  a ⟩
                          a ∎
      hlp2 : x + a ≡ x + b → a ≡ b 
      hlp2 p =  begin a  
                                ≡⟨ sym (hlp4 x a) ⟩
                (- x) + (x + a) 
                                ≡⟨ cong₂ (_+_) refl hlp1 ⟩ 
                ((- x)) + (x + b) 
                                ≡⟨ hlp4 x b ⟩ 
                b  ∎


  a=b→x+a=x+b :   (x a b : M ) →  a ≡ b →  x + a ≡ x + b 
  a=b→x+a=x+b  x a b p = cong₂ (_+_ ) refl p
  a=b→a+x=b+x :   (x a b : M ) →  a ≡ b →  a + x ≡ b + x 
  a=b→a+x=b+x  x a b p = cong₂ (_+_) p refl

  a+x=0=b+x→a=b :  (x a b : M) →  a + x ≡ 𝟘 →   b + x ≡ 𝟘 → a ≡ b 
  a+x=0=b+x→a=b  x a b h k = x+a=0=x+b→a=b  x a b ((trans (+-comm  x a) h)) ((trans ((+-comm ) x b) k))
  x+a=x+b→a+x=b+x :  (x a b : M ) →  x + a ≡  x + b →    a + x ≡  b + x 
  x+a=x+b→a+x=b+x  x a b h = trans (trans (+-comm a x) h) (+-comm  x b)
  a+x=b+x→x+a=x+b :  (x a b : M ) →  a + x ≡ b + x →   x + a ≡  x + b 
  a+x=b+x→x+a=x+b  x a b h = trans (trans (+-comm  x a) h) (+-comm  b x)
  a+x=b+x→a=b :  (x a b : M ) → a + x ≡   b + x  → a ≡ b 
  a+x=b+x→a=b  x a b h = begin a  ≡⟨ sym (hlp4 x a) ⟩ ( (- x)) + ( x + a) ≡⟨ cong₂  (_+_ ) refl (a+x=b+x→x+a=x+b x a b h) ⟩ ( (- x))+ ( x + b) ≡⟨ hlp4 x b ⟩ b ∎
    where 
      hlp4 : (x a : M ) →   ( (- x)) + (x + a) ≡  a
      hlp4 x a =  begin (- x) + (x + a)  ≡⟨ sym((+-assoc ) (- x) x a) ⟩ ((- x) + x) + a ≡⟨ cong₂ (_+_) ((-left ) x) refl ⟩ 𝟘 + a ≡⟨ ω-left  a ⟩ a ∎

  x+a=x+b→a=b : (x a b : M) → x + a ≡  x + b  → a ≡ b 
  x+a=x+b→a=b  x a b h = a+x=b+x→a=b  x a b (x+a=x+b→a+x=b+x  x a b h )

  x+a=x→a=0 :   (x a : M ) → x + a ≡ x → a ≡ 𝟘
  x+a=x→a=0  x a p with a=b→x+a=x+b  (- x) (x + a) x p  
  ... | res = begin a  ≡⟨ sym ((ω-left )a) ⟩ 𝟘 + a ≡⟨ cong₂ (_+_ ) (sym ((-left ) x)) refl ⟩ ((- x) + x) + a ≡⟨ ((+-assoc ) (- x) x a) ⟩  (- x) + (x + a) ≡⟨ trans res ((-left ) x) ⟩ 𝟘 ∎ 

  a+x=x→a=0 :  (x a : M ) → a + x ≡ x → a ≡ 𝟘
  a+x=x→a=0  x a p = x+a=x→a=0  x a (trans ((+-comm) x a)  p)

-- ≢e₊-irrelevant : ∀ {A} {a : M A} → (p q : ¬ (a ≡ (e₊ A))) → p ≡ q
-- ≢e₊-irrelevant p q = fun-ext (λ r → ⊥-elim (p r))

-- data NonZeroPoly (A : Ring): Set where 
--   ld : (a : M A)  → ¬ (a ≡ (e₊ A)) →  NonZeroPoly A
--   _∷ₚ_ : (M A)  → NonZeroPoly A -> NonZeroPoly A

-- data Poly  (A : Ring): Set where 
--   0ₚ : Poly A
--   non0ₚ : NonZeroPoly A → Poly A


-- data sum-zero {A : Ring} :  (p q : NonZeroPoly A) → Set where 
--   ld0 : (a b : M A) → (pa : ¬ (a ≡ (e₊ A))) → (pb : ¬ (b ≡ (e₊ A))) → ((_+ᵣ_ A) a b) ≡ (e₊ A) → sum-zero (ld a pa) (ld b pb)
--   ∷0  : (a b : M A) → (p q : NonZeroPoly A) → ((_+ᵣ_ A) a b) ≡ (e₊ A) → sum-zero p q → sum-zero (a ∷ₚ p) (b ∷ₚ q)

-- -- data sum-zero-Poly {A : Ring}  :  (p q : Poly A) → Set where 
--   -- 0ₚ-≡ : sum-zero-Poly 0ₚ 0ₚ
--   -- n0ₚ-≡ : (p q : NonZeroPoly A) → (sum-zero p q) →  sum-zero-Poly  (non0ₚ p) (non0ₚ q)

-- data sum-nonzero {A : Ring} :  (p q : NonZeroPoly A) → Set where 
--   ldld : (a b : M A) → (pab : ¬ ((_+ᵣ_ A) a b  ≡ (e₊ A))) → (pa : ¬ (a ≡ (e₊ A))) → (pb : ¬ (b ≡ (e₊ A))) → sum-nonzero (ld a pa) (ld b pb) 
--   ∷ld  : (a b : M A) → (pb : ¬ (b ≡ (e₊ A))) → (p : NonZeroPoly A)  → sum-nonzero (a ∷ₚ p) (ld b pb) 
--   ld∷  : (a b : M A) → (pa : ¬ (a ≡ (e₊ A))) → (q : NonZeroPoly A)  → sum-nonzero (ld a pa) (b ∷ₚ q)
--   ∷∷rek  : (a b : M A)  → (p q : NonZeroPoly A) → sum-nonzero p q → sum-nonzero (a ∷ₚ p) (b ∷ₚ q)
--   ∷∷lok  : (a b : M A)  → (p q : NonZeroPoly A) → (pab : ¬ ((_+ᵣ_ A) a b  ≡ (e₊ A))) → sum-nonzero (a ∷ₚ p) (b ∷ₚ q)

-- addp2 : {A : Ring} → (p q : NonZeroPoly A) → (NonZeroPoly A)  ⊎ (sum-zero p q)
-- addp2 {A} (ld ha pa) (ld hb pb) with ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A) )
-- ... | yes x = inj₂ (ld0 ha hb pa pb x)
-- ... | no x = inj₁ ( ld  ((_+ᵣ_ A) ha  hb) x)
-- addp2 {A} (ld ha pa) (hb ∷ₚ tb) = inj₁ (((_+ᵣ_ A) ha  hb) ∷ₚ tb)
-- addp2 {A} (ha ∷ₚ ta) (ld hb pb) = inj₁ (((_+ᵣ_ A) ha  hb) ∷ₚ ta)
-- addp2 {A} (ha ∷ₚ ta) (hb ∷ₚ tb) with (addp2 ta tb) | ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A) )
-- ... | inj₁ x | res2 = inj₁( ((_+ᵣ_ A) ha  hb) ∷ₚ x)
-- ... | inj₂ y | yes p = inj₂ (∷0 ha hb ta tb p y)
-- ... | inj₂ y | no p = inj₁ (ld ((_+ᵣ_ A) ha  hb) p) 

-- -- ce ne gre dodaj da vrne nonzero ali pa dokaz da se vsi naprej sestejejo v 0
-- addp : {A : Ring} → (x y : NonZeroPoly A) → Maybe (NonZeroPoly A)
-- addp {A} (ld ha pa) (ld hb pb) with ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A) )
-- ...     | yes p = nothing  --vsota je 0
-- ...     | no p = just (ld ((_+ᵣ_ A) ha  hb) p) 
-- addp {A} (ld ha p) (hb ∷ₚ tb) = just (((_+ᵣ_ A) ha  hb) ∷ₚ tb)
-- addp (ha ∷ₚ ta) (ld b x) = addp (ld b x) (ha ∷ₚ ta)
-- addp {A} (ha ∷ₚ ta) (hb ∷ₚ tb) with (addp ta tb) 
-- ...     | just res = just (((_+ᵣ_ A) ha  hb) ∷ₚ res)
-- ...     | nothing with ((dec A) ((_+ᵣ_ A) ha  hb) (e₊ A))
-- ...               | yes p = nothing
-- ...               | no p = just (ld ((_+ᵣ_ A) ha  hb) p)

-- a+b=b+a=e : {A : Ring} → (a b : M A) → (A +ᵣ a) b ≡ e₊ A → (A +ᵣ b) a ≡ e₊ A
-- a+b=b+a=e {A} a b p = begin (A +ᵣ b) a   ≡⟨ (+-comm A) b a ⟩ (A +ᵣ a) b ≡⟨ p ⟩ e₊ A ∎
-- justnoth⊥ : {X : Set}{x : X} →  nothing ≡ just x → ⊥
-- justnoth⊥ ()


-- addp-comm : {A : Ring} → (p q : NonZeroPoly A) → addp p q ≡ addp q p 
-- addp-comm {A} (ld a x) (ld b y) with ( dec A ((A +ᵣ a) b) (e₊ A)) | inspect ( dec A ((A +ᵣ a) b) ) (e₊ A)
-- ... | no p | [ eq ] with dec A ((A +ᵣ b) a) (e₊ A)
-- ... | no p2 =  cong just (dcong₂ ld (((+-comm A) a b)) refl) --cong just (dcong₂ ld ((+-comm A) a b) refl)
-- ... | yes p2 with p (a+b=b+a=e {A} b a p2 )
-- ... | ()
-- addp-comm {A} (ld a x) (ld b y) | yes p | [ eq ] with ( dec A ((A +ᵣ b) a) (e₊ A)) | inspect ( dec A ((A +ᵣ b) a) ) (e₊ A)
-- ... | yes x₁ | [ eq₁ ] = refl
-- ... | no p2 | [ eq₁ ] with ¬-elim p2 (a+b=b+a=e {A} a b p)
-- ... | ()
-- addp-comm {A} (ld a x) (x₁ ∷ₚ q) = cong just refl
-- addp-comm {A} (x ∷ₚ p) (ld a x₁) = cong just refl
-- addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) with addp p q | inspect (addp p) q | addp q p | inspect (addp q) p
-- ... | just x | [ eq ] | just y | [ eq2 ] = cong just (cong₂ _∷ₚ_ ((+-comm A) a b) (hlp (x=yjust  eq2 eq)))
--   where 
--     x=yjust : addp q p ≡ just y → addp p q ≡ just x → just x ≡ just y 
--     x=yjust p1 p2 = begin just x   ≡⟨ sym p2 ⟩ addp p q ≡⟨ addp-comm p q ⟩ addp q p ≡⟨ p1 ⟩ just y ∎
--     hlp : just x ≡ just y → x ≡ y 
--     hlp refl = refl

-- ... | just x₂ | [ eq ] | nothing | [ eq₁ ] with justnoth⊥ (trans (sym eq₁) (trans  (addp-comm q p) eq))
-- ... | ()
-- addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | just x | [ eq₁ ] with justnoth⊥ (trans (sym  eq) (trans (addp-comm p q) eq₁))
-- ... | ()
-- addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] with ( dec A ((A +ᵣ b) a) (e₊ A)) |  ( dec A ((A +ᵣ a) b) (e₊ A))
-- ... | yes x | yes x₁ = refl
-- ... | yes x | no y  with ¬-elim y (a+b=b+a=e {A} b a  x)
-- ... | () 
-- addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] | no x | yes y with ¬-elim x (a+b=b+a=e {A}  a b  y)
-- ... | ()
-- addp-comm {A} (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] | no x | no y = cong just (dcong₂ ld ((+-comm A) a b) refl)



-- _+ₚ_ : {A : Ring} → (a : Poly A )→ (b : Poly A) → Poly A
-- 0ₚ +ₚ b = b
-- non0ₚ x +ₚ 0ₚ = non0ₚ x
-- non0ₚ x +ₚ non0ₚ y with addp x y 
-- ... | just res = non0ₚ res
-- ... | nothing = 0ₚ


-- +ₚ-comm :  {A : Ring} → (p q : Poly A ) → p +ₚ q ≡ q +ₚ p 
-- +ₚ-comm {A} 0ₚ 0ₚ = refl
-- +ₚ-comm {A} 0ₚ (non0ₚ x) = refl
-- +ₚ-comm {A} (non0ₚ x) 0ₚ = refl
-- +ₚ-comm {A} (non0ₚ p) (non0ₚ q) with addp p q | inspect (addp p) q | addp q p | inspect (addp q) p
-- ... | just x | [ eq ] | just y | [ eq₁ ] = cong non0ₚ (hlp (x=yjust eq₁ eq))
--   where 
--     x=yjust : addp q p ≡ just y → addp p q ≡ just x → just x ≡ just y 
--     x=yjust p1 p2 = begin just x   ≡⟨ sym p2 ⟩ addp p q ≡⟨ addp-comm p q ⟩ addp q p ≡⟨ p1 ⟩ just y ∎
--     hlp : just x ≡ just y → x ≡ y 
--     hlp refl = refl
-- ... | just x | [ eq ] | nothing | [ eq₁ ] with justnoth⊥ (trans (sym eq₁) (trans (addp-comm q p) eq))
-- ... | ()
-- +ₚ-comm {A} (non0ₚ p) (non0ₚ q) | nothing | [ eq ] | just y | [ eq₁ ] with justnoth⊥ (sym (trans (sym eq₁) (trans (addp-comm q p) eq)))
-- ... | ()
-- +ₚ-comm {A} (non0ₚ p) (non0ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] = refl




-- --  /////////////////////
-- ∷ₚ-injh : {A : Ring} → ∀ {a b : M A} → ∀ {c d : NonZeroPoly A} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  a ≡ b 
-- ∷ₚ-injh refl = refl
-- ∷ₚ-injt : {A : Ring} → ∀ {a b : M A} → ∀ {c d : NonZeroPoly A} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  c ≡ d 
-- ∷ₚ-injt refl = refl
-- ld-inj : {A : Ring} →  ∀ {a b : M A} → ∀ {c d} → (ld {A} a c) ≡ (ld b d) → a ≡ b
-- ld-inj refl = refl
-- ∷ₚ-≡ : {A : Ring} → {a b : M A} → ∀ {c d : NonZeroPoly A} → a ≡ b → c ≡ d  → (a ∷ₚ c) ≡ (b ∷ₚ d)
-- ∷ₚ-≡ {A} refl refl = refl 
-- ld-≡ : {A : Ring} → ∀ {a b : M A} → ∀ {c d} → a ≡ b → (ld {A} a c) ≡ (ld b d)
-- ld-≡ {A}{a}{b}{c}{d} p with (dec A) a (e₊ A)
-- ld-≡ {A} {.(e₊ A)} {.(e₊ A)} {c} {d} refl | yes refl = refl
-- ld-≡ {A} {a} {.a} {c} {d} refl | no x = refl
-- -- ≢e₊-irrelevant : ∀ {A} {a : M A} → (p q : ¬ (a ≡ (e₊ A))) → p ≡ q
-- -- ≢e₊-irrelevant p q = fun-ext (λ r → ⊥-elim (p r))



-- ldtl⊥ : {A : Ring} →  (p q : NonZeroPoly A) → addp p q  ≡  just p → ⊥
-- ldtl⊥ {A} (ld a x) (ld a₁ x₁) r with dec A ((A +ᵣ a) a₁) (e₊ A)
-- ... | no x₂ with x₁ (x+a=x→a=0{A} a a₁ (ld-inj (just-injective r)))
-- ... | ()
-- ldtl⊥ {A} (x ∷ₚ p) (ld a x₁) r  with ¬-elim x₁ (a+x=x→a=0 {A} x a (∷ₚ-injh (just-injective r)) )
-- ... | ()
-- ldtl⊥ {A} (x ∷ₚ p) (x₁ ∷ₚ q) r with addp p q | inspect (addp p ) q  
-- ... | just x₂ | [ eq ] with   (∷ₚ-injt (just-injective r))
-- ... | res rewrite res with ldtl⊥ p q eq 
-- ... | () 

-- ldtl⊥ {A} (x ∷ₚ p) (x₁ ∷ₚ q) r | nothing | [ eq ] with dec A ((A +ᵣ x) x₁) (e₊ A)
-- ldtl⊥ {A} (x ∷ₚ p) (x₁ ∷ₚ q) () | nothing | [ eq ] | yes x₂
-- ... | no x₂ with just-injective r 
-- ... | () 

-- ldtl⊥sym : {A : Ring} →  (p q : NonZeroPoly A) → addp q p  ≡  just p → ⊥
-- ldtl⊥sym p q r with ldtl⊥ p q (trans (addp-comm p q) r)
-- ... | ()


-- addpinj : {A : Ring} → (p q r : NonZeroPoly A) → addp q p ≡ addp r p  → q ≡ r 
-- addpinj {A} (ld a pa) (ld b pb) (ld c pc) h with (dec A) ((A +ᵣ b) a) (e₊ A)  | (dec A) ((A +ᵣ c) a) (e₊ A) 
-- ... | yes x | yes x₁ = dcong₂ ld (a+x=0=b+x→a=b {A} a b c x x₁) refl
-- ... | no x | no x₁ = dcong₂ ld (a+x=b+x→a=b {A} a b c (ld-inj hlp)) refl
--   where
--     hlp :  (ld ((A +ᵣ b) a) x) ≡  (ld ((A +ᵣ c) a) x₁)
--     hlp = just-injective h
    
-- addpinj {A} (ld a pa) (ld b pb) (c ∷ₚ tc) h with dec A ((A +ᵣ b) a) (e₊ A)
-- addpinj {A} (ld a pa) (ld b pb) (c ∷ₚ tc) () | yes x
-- addpinj {A} (ld a pa) (ld b pb) (c ∷ₚ tc) () | no x
-- addpinj {A} (ld a pa) (b ∷ₚ tb) (ld c pc) h with dec A ((A +ᵣ c) a) (e₊ A) 
-- addpinj {A} (ld a pa) (b ∷ₚ tb) (ld c pc) () | yes x₁
-- addpinj {A} (ld a pa) (b ∷ₚ tb) (ld c pc) () | no x₁
-- addpinj {A} (ld a pa) (b ∷ₚ tb) (c ∷ₚ tc) h = ∷ₚ-≡ headeq tleq
--   where 
--     headeq :  b  ≡ c
--     headeq  = x+a=x+b→a=b {A} a b c (∷ₚ-injh (just-injective h))
--     tleq : tb  ≡ tc 
--     tleq  = ∷ₚ-injt (just-injective h)
-- addpinj {A} (a ∷ₚ ta) (ld b pb) (ld c pc) h = ld-≡ (a+x=b+x→a=b {A} a b c (∷ₚ-injh (just-injective h)))
-- addpinj {A} (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) h with addp tc ta | inspect (addp tc) ta
-- ... | just tc+ta | [ eq ] with (∷ₚ-injt(just-injective h))
-- ... | res rewrite res with ldtl⊥sym  tc+ta tc eq
-- ... | ()
-- addpinj {A} (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) h | nothing | [ eq ] with dec A ((A +ᵣ hc) a) (e₊ A)
-- addpinj {A} (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) () | nothing | [ eq ] | yes x
-- addpinj {A} (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) () | nothing | [ eq ] | no x
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) h with addp tb ta | inspect (addp tb) ta
-- ... | just tb+ta | [ eq ] with (∷ₚ-injt(just-injective h))
-- ... | res rewrite res  with ldtl⊥sym  ta tb eq 
-- ... | ()
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) h | nothing | [ eq ] with dec A ((A +ᵣ b) a) (e₊ A) 
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) () | nothing | [ eq ] | yes x
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) () | nothing | [ eq ] | no x
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) h with addp tb ta | inspect (addp tb) ta | addp tc ta | inspect (addp tc) ta  
-- ... | just x | [ eq ] | just y | [ eq₁ ] = ∷ₚ-≡ hlp2 hlp
--   where 
--     hlp2 : b ≡ c 
--     hlp2 = a+x=b+x→a=b {A}a b c (∷ₚ-injh (just-injective h))
--     hlp3 : x ≡ y 
--     hlp3 = (∷ₚ-injt (just-injective h))
--     hlp4 : x ≡ y → just x ≡ just y
--     hlp4 refl = refl
--     hlp : tb ≡ tc 
--     hlp = addpinj ta tb tc (trans eq (trans (hlp4 hlp3)(sym eq₁)) )
-- ... | just x | [ eq ] | nothing | [ eq₁ ] with dec A  ((A +ᵣ c) a) (e₊ A)
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | just x | [ eq ] | nothing | [ eq₁ ] | yes x₁
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | just x | [ eq ] | nothing | [ eq₁ ] | no x₁
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) h | nothing | [ eq ] | just x | [ eq₁ ] with dec A  ((A +ᵣ b) a) (e₊ A)
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | nothing | [ eq ] | just x | [ eq₁ ] | yes x₁
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | nothing | [ eq ] | just x | [ eq₁ ] | no x₁
-- addpinj {A} (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) h | nothing | [ eq ] | nothing | [ eq₁ ] with dec A ((A +ᵣ b) a) (e₊ A) | dec A ((A +ᵣ c) a) (e₊ A)
-- ... | yes x | yes x₁ = ∷ₚ-≡ hlp2 (sym hlp)
--   where   
--     hlp2 : b ≡ c 
--     hlp2 = a+x=0=b+x→a=b {A}a b c x x₁
--     hlp : tc ≡ tb 
--     hlp = addpinj ta tc tb (trans eq₁  (sym eq))
-- ... | no x | no x₁ = ∷ₚ-≡ hlp2 (sym hlp)
--   where   
--     hlp2 : b ≡ c 
--     hlp2 = (a+x=b+x→a=b {A} a b c  (ld-inj (just-injective  h)))
--     hlp : tc ≡ tb 
--     hlp = addpinj ta tc tb (trans eq₁  (sym eq))
  




-- n0→n0 : {A : Ring} → (a : M A) → ¬ (a ≡ e₊ A) → ¬ ((-ᵣ A) a ≡ e₊ A) 
-- n0→n0 {A} a = contraposition (hlphlp {A} a)
--   where 
--     hlphlp : {A : Ring} → (a : M A) → ((-ᵣ A) a ≡ e₊ A) → (a ≡ e₊ A) 
--     hlphlp {A} a p = trans (sym (trans((a=b→a+x=b+x {A} a ((-ᵣ A) a) (e₊ A) p)) ((ω-left A) a)))  ((-ᵣ-left A) a)

-- -ₚh : {A : Ring} → (p : NonZeroPoly A) → ( NonZeroPoly A)
-- -ₚh {A} (ld a x) = ld ((-ᵣ_ A) a)  (n0→n0 {A} a x)
-- -ₚh {A} (x ∷ₚ p) = ((-ᵣ_ A) x) ∷ₚ (-ₚh p)

-- -ₚ : {A : Ring} → (p : Poly A) → ( Poly A)
-- -ₚ {A} 0ₚ = 0ₚ
-- -ₚ {A} (non0ₚ p) = non0ₚ (-ₚh p)


-- -ₚh-empt : {A : Ring}→ (p : NonZeroPoly A) → addp (-ₚh p) p ≡ nothing
-- -ₚh-empt {A} (ld a x) with dec A ((A +ᵣ (-ᵣ A) a) a) (e₊ A)
-- ... | yes x₁ = refl
-- ... | no x₁ with ¬-elim  x₁ ((-ᵣ-left A) a) 
-- ... | () 
-- -ₚh-empt {A} (x ∷ₚ p) with -ₚh-empt p  | addp (-ₚh p) p | inspect (addp (-ₚh p)) p
-- ... | h | nothing | [ i ] with dec A ((A +ᵣ (-ᵣ A) x) x) (e₊ A)
-- ... | yes x₁ = refl
-- ... | no x₁ with ¬-elim  x₁ ((-ᵣ-left A) x) 
-- ... | ()
-- -ₚh-empt {A} (x ∷ₚ p) | h | just x₁ | [ i ] with justnoth⊥ (trans (sym h) i)
-- ... | ()

-- -ₚ-left  : {A : Ring}→ (p : Poly A) → (-ₚ p) +ₚ p ≡ 0ₚ
-- -ₚ-left {A} 0ₚ = refl
-- -ₚ-left {A} (non0ₚ x) with addp (-ₚh x) x | inspect (addp (-ₚh x)) x
-- ... | just p | [ i ] with justnoth⊥ (sym(trans (sym i) (-ₚh-empt x )) )
-- ... | ()
-- -ₚ-left {A} (non0ₚ x)  | nothing | [ i ] = refl

 


-- +ₚ-asoc : {A : Ring} → (p q r : Poly A) → p +ₚ (q +ₚ r) ≡ (p +ₚ q) +ₚ r
-- +ₚ-asoc 0ₚ 0ₚ 0ₚ = refl
-- +ₚ-asoc 0ₚ 0ₚ (non0ₚ x) = refl
-- +ₚ-asoc 0ₚ (non0ₚ x) r = refl
-- +ₚ-asoc (non0ₚ x) 0ₚ r = refl
-- +ₚ-asoc (non0ₚ p) (non0ₚ q) 0ₚ = begin (non0ₚ p +ₚ (non0ₚ q +ₚ 0ₚ))   ≡⟨ refl ⟩ (0ₚ +ₚ (non0ₚ p +ₚ non0ₚ q)) ≡⟨ +ₚ-comm 0ₚ (non0ₚ p +ₚ non0ₚ q) ⟩ ((non0ₚ p +ₚ non0ₚ q) +ₚ 0ₚ) ∎
-- +ₚ-asoc {A} (non0ₚ p) (non0ₚ q) (non0ₚ r) with addp q r | inspect (addp q) r | addp p q | inspect (addp p) q
-- ... | just q+r | [ eq ] | just p+q | [ eq₁ ]  with addp p q+r | inspect (addp p) q+r | addp p+q r | inspect (addp p+q) r 
-- ... | just p+q$+r | [ eq₂ ] | just p+$q+r | [ eq₃ ] = {!   !}
-- ... | just x₁ | [ eq₂ ] | nothing | [ eq₃ ] = {!   !}
-- ... | nothing | [ eq₂ ] | a2 | [ eq₃ ] = {!   !}
-- +ₚ-asoc {A} (non0ₚ p) (non0ₚ q) (non0ₚ r) | just x | [ eq ] | nothing | [ eq₁ ] = {!   !}
-- +ₚ-asoc {A} (non0ₚ p) (non0ₚ q) (non0ₚ r) | nothing | [ eq ] | just y | [ eq₁ ]  with addp y r | inspect (addp y) r 
-- ... | just x | [ eq₂ ] = {!  !}
-- ... | nothing | [ eq₂ ] with addpinj r   q y (trans eq (sym eq₂))
-- ... | res rewrite res with ldtl⊥sym y p  eq₁
-- ... | ()
-- +ₚ-asoc {A} (non0ₚ p) (non0ₚ q) (non0ₚ r) | nothing | [ eq ] | nothing | [ eq₁ ] = cong non0ₚ (addpinj q p r (trans ( trans eq₁ (sym eq) ) (addp-comm q r)))
--   where 
--     hlp2 : (addp p q ≡ nothing) → (addp q r ≡ nothing) → addp p q ≡ addp r q 
--     hlp2 h k = trans h (sym (trans (addp-comm r q) k))

--     -- addpinj : {A : Ring} → (p q r : NonZeroPoly A) → addp q p ≡ addp r p  → q ≡ r 
 