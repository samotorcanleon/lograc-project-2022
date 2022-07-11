module noviplus2 where
open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Maybe.Properties using (just-injective)
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

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

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
      hlp4 : (x a : M ) →  - x + (x + a) ≡  a
      hlp4 x a =  begin   - x + (x + a)  
                                          ≡⟨ sym((+-assoc ) (- x) x a) ⟩
                          - x + x + a 
                                          ≡⟨ cong₂ (_+_) (-left x) refl ⟩ 
                          𝟘 + a 
                                          ≡⟨ ω-left  a ⟩
                          a ∎
      hlp2 : x + a ≡ x + b → a ≡ b 
      hlp2 p =  begin a  
                                ≡⟨ sym (hlp4 x a) ⟩
                - x + (x + a) 
                                ≡⟨ cong₂ (_+_) refl hlp1 ⟩ 
                - x + (x + b) 
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
  a+x=b+x→a=b  x a b h = begin  a  
                                                  ≡⟨ sym (hlp4 x a) ⟩
                                - x + ( x + a) 
                                                  ≡⟨ cong₂  (_+_ ) refl (a+x=b+x→x+a=x+b x a b h) ⟩
                                - x + ( x + b) 
                                                  ≡⟨ hlp4 x b ⟩
                                b ∎
    where 
      hlp4 : (x a : M ) → - x + (x + a) ≡  a
      hlp4 x a =  begin - x + (x + a)   
                                        ≡⟨ sym((+-assoc ) (- x) x a) ⟩
                        - x + x + a     
                                        ≡⟨ cong₂ (_+_) ((-left ) x) refl ⟩
                        𝟘 + a 
                                        ≡⟨ ω-left  a ⟩
                        a ∎

  x+a=x+b→a=b : (x a b : M) → x + a ≡  x + b  → a ≡ b 
  x+a=x+b→a=b  x a b h = a+x=b+x→a=b  x a b (x+a=x+b→a+x=b+x  x a b h )

  x+a=x→a=0 :   (x a : M ) → x + a ≡ x → a ≡ 𝟘
  x+a=x→a=0  x a p with a=b→x+a=x+b  (- x) (x + a) x p  
  ... | res = begin a  
                                    ≡⟨ sym ((ω-left ) a) ⟩
                    𝟘 + a 
                                    ≡⟨ cong₂ (_+_ ) (sym ((-left ) x)) refl ⟩
                    - x + x + a 
                                    ≡⟨ ((+-assoc ) (- x) x a) ⟩
                    - x + (x + a) 
                                    ≡⟨ trans res ((-left ) x) ⟩
                    𝟘 ∎ 

  a+x=x→a=0 :  (x a : M ) → a + x ≡ x → a ≡ 𝟘
  a+x=x→a=0  x a p = x+a=x→a=0  x a (trans ((+-comm) x a)  p)

  a+b=b+a=e : (a b : M ) → a + b ≡ 𝟘 → b + a ≡ 𝟘
  a+b=b+a=e a b p = begin b + a  
                                ≡⟨ (+-comm ) b a ⟩
                          a + b 
                                ≡⟨ p ⟩
                          𝟘 ∎

  n0→n0 : (a : M) → ¬ (a ≡ 𝟘) → ¬ (- a ≡ 𝟘) 
  n0→n0 a = contraposition (hlphlp a)
    where 
      hlphlp :  (a : M) → (- a ≡ 𝟘) → (a ≡ 𝟘) 
      hlphlp  a p = trans (sym (trans (a=b→a+x=b+x a (- a) 𝟘 p) ((ω-left ) a))) ((-left ) a)


module _ (A : Ring) where
  open Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ)

  data NonZeroPoly : Set where
    ld : (a : M)  → ¬ (a ≡ 𝟘ᵣ) →  NonZeroPoly
    _∷ₚ_ : M  → NonZeroPoly -> NonZeroPoly

  data Poly : Set where
    𝟘ₚ : Poly
    non𝟘ₚ : NonZeroPoly → Poly


module _ (A : Ring) where
  open Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ; _+_ to _+ᵣ_; _·_ to _·ᵣ_; -_ to -ᵣ_; 𝟙≠𝟘 to 𝟙ᵣ≠𝟘ᵣ; 𝟙-left to 𝟙ᵣ-left; ·-comm to ·ᵣ-comm)
  open RingProofs {A}

    --///////////////////////// ADDITION DEFINITION /////////////////////////
  addp : (x y : NonZeroPoly A) → Maybe (NonZeroPoly A)
  addp (ld ha pa) (ld hb pb) with (dec (ha +ᵣ hb) 𝟘ᵣ)
  ...     | yes p = nothing  --vsota je 𝟘
  ...     | no p = just (ld (ha +ᵣ hb) p)
  addp (ld ha p) (hb ∷ₚ tb) = just ((ha +ᵣ hb) ∷ₚ tb)
  addp (ha ∷ₚ ta) (ld b x) = addp (ld b x) (ha ∷ₚ ta)
  addp (ha ∷ₚ ta) (hb ∷ₚ tb) with (addp ta tb)
  ...     | just res = just ((ha +ᵣ hb) ∷ₚ res)
  ...     | nothing with (dec (ha +ᵣ hb) (𝟘ᵣ))
  ...               | yes p = nothing
  ...               | no p = just (ld (ha +ᵣ hb) p)

  _+ₚ_ : (a : Poly A ) → (b : Poly A) → Poly A
  𝟘ₚ +ₚ b = b
  non𝟘ₚ x +ₚ 𝟘ₚ = non𝟘ₚ x
  non𝟘ₚ x +ₚ non𝟘ₚ y with (addp x y)
  ... | just res = non𝟘ₚ res
  ... | nothing = 𝟘ₚ


  justnoth⊥ : {X : Set}{x : X} →  nothing ≡ just x → ⊥
  justnoth⊥ ()

  -- ////////////// COMUTATIVITY PROOF /////////////////////
  addp-comm :  (p q : NonZeroPoly A) → addp p q ≡ addp q p 
  addp-comm (ld a x) (ld b y) with ( dec  (a +ᵣ b) 𝟘ᵣ) | inspect ( dec (a +ᵣ b) ) 𝟘ᵣ
  ... | no p | [ eq ] with dec  (b +ᵣ a) 𝟘ᵣ
  ... | no p2 =  cong just (dcong₂ ld (((+-comm ) a b)) refl) 
  ... | yes p2 with p (a+b=b+a=e b a p2 )
  ... | ()
  addp-comm (ld a x) (ld b y) | yes p | [ eq ] with ( dec  (b +ᵣ a) 𝟘ᵣ) | inspect ( dec (b +ᵣ a) ) 𝟘ᵣ
  ... | yes x₁ | [ eq₁ ] = refl
  ... | no p2 | [ eq₁ ] with ¬-elim p2 (a+b=b+a=e a b p)
  ... | ()
  addp-comm  (ld a x) (x₁ ∷ₚ q) = cong just refl
  addp-comm  (x ∷ₚ p) (ld a x₁) = cong just refl
  addp-comm  (a ∷ₚ p) (b ∷ₚ q) with addp p q | inspect (addp p) q | addp q p | inspect (addp q) p
  ... | just x | [ eq ] | just y | [ eq2 ] = cong just (cong₂ _∷ₚ_ ((+-comm ) a b) (hlp (x=yjust  eq2 eq)))
    where 
      x=yjust : addp q p ≡ just y → addp p q ≡ just x → just x ≡ just y 
      x=yjust p1 p2 = begin just x  
                                      ≡⟨ sym p2 ⟩
                            addp p q 
                                      ≡⟨ addp-comm p q ⟩
                            addp q p 
                                      ≡⟨ p1 ⟩
                            just y ∎
      hlp : just x ≡ just y → x ≡ y 
      hlp refl = refl

  ... | just x₂ | [ eq ] | nothing | [ eq₁ ] with justnoth⊥ (trans (sym eq₁) (trans  (addp-comm q p) eq))
  ... | ()
  addp-comm  (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | just x | [ eq₁ ] with justnoth⊥ (trans (sym  eq) (trans (addp-comm p q) eq₁))
  ... | ()
  addp-comm  (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] with ( dec (b +ᵣ a) 𝟘ᵣ) | ( dec (a +ᵣ b) 𝟘ᵣ)
  ... | yes x | yes x₁ = refl
  ... | yes x | no y  with ¬-elim y (a+b=b+a=e b a x)
  ... | () 
  addp-comm  (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] | no x | yes y with ¬-elim x (a+b=b+a=e   a b  y)
  ... | ()
  addp-comm  (a ∷ₚ p) (b ∷ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] | no x | no y = cong just (dcong₂ ld ((+-comm) a b) refl)




  +ₚ-comm : (p q : Poly A ) → p +ₚ q ≡ q +ₚ p 
  +ₚ-comm 𝟘ₚ 𝟘ₚ = refl
  +ₚ-comm  𝟘ₚ (non𝟘ₚ x) = refl
  +ₚ-comm  (non𝟘ₚ x) 𝟘ₚ = refl
  +ₚ-comm  (non𝟘ₚ p) (non𝟘ₚ q) with addp p q | inspect (addp p) q | addp q p | inspect (addp q) p
  ... | just x | [ eq ] | just y | [ eq₁ ] = cong non𝟘ₚ (hlp (x=yjust eq₁ eq))
    where 
      x=yjust : addp q p ≡ just y → addp p q ≡ just x → just x ≡ just y 
      x=yjust p1 p2 = begin just x   
                                      ≡⟨ sym p2 ⟩
                            addp p q 
                                      ≡⟨ addp-comm p q ⟩
                            addp q p 
                                      ≡⟨ p1 ⟩
                            just y ∎
      hlp : just x ≡ just y → x ≡ y 
      hlp refl = refl
  ... | just x | [ eq ] | nothing | [ eq₁ ] with justnoth⊥ (trans (sym eq₁) (trans (addp-comm q p) eq))
  ... | ()
  +ₚ-comm  (non𝟘ₚ p) (non𝟘ₚ q) | nothing | [ eq ] | just y | [ eq₁ ] with justnoth⊥ (sym (trans (sym eq₁) (trans (addp-comm q p) eq)))
  ... | ()
  +ₚ-comm  (non𝟘ₚ p) (non𝟘ₚ q) | nothing | [ eq ] | nothing | [ eq₁ ] = refl




  --  /////////////////////   helper fuctions ///////
  ∷ₚ-injh :  ∀ {a b : M } → ∀ {c d : NonZeroPoly A} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  a ≡ b 
  ∷ₚ-injh refl = refl
  ∷ₚ-injt :  ∀ {a b : M } → ∀ {c d : NonZeroPoly A} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  c ≡ d 
  ∷ₚ-injt refl = refl
  ld-inj :   ∀ {a b : M } → ∀ {c d} → (ld {A} a c) ≡ (ld b d) → a ≡ b
  ld-inj refl = refl
  ∷ₚ-≡ :  {a b : M } → ∀ {c d : NonZeroPoly A} → a ≡ b → c ≡ d  → (a ∷ₚ c) ≡ (b ∷ₚ d)
  ∷ₚ-≡  refl refl = refl 
  ld-≡ :  ∀ {a b : M } → ∀ {c d} → a ≡ b → (ld {A} a c) ≡ (ld b d)
  ld-≡ {a}{b}{c}{d} p with (dec) a (𝟘ᵣ)
  ld-≡  {𝟘ᵣ} {𝟘ᵣ} {c} {d} refl | yes refl = refl
  ld-≡  {a} {a} {c} {d} refl | no x = refl



  ldtl⊥ :  (p q : NonZeroPoly A) → addp p q  ≡  just p → ⊥
  ldtl⊥  (ld a x) (ld a₁ x₁) r with dec  (a +ᵣ a₁) 𝟘ᵣ
  ... | no x₂ with x₁ (x+a=x→a=0  a a₁ (ld-inj (just-injective r)))
  ... | ()
  ldtl⊥ (x ∷ₚ p) (ld a x₁) r  with ¬-elim x₁ (a+x=x→a=0 x a (∷ₚ-injh (just-injective r)) )
  ... | ()
  ldtl⊥ (x ∷ₚ p) (x₁ ∷ₚ q) r with addp p q | inspect (addp p ) q  
  ... | just x₂ | [ eq ] with   (∷ₚ-injt (just-injective r))
  ... | res rewrite res with ldtl⊥ p q eq 
  ... | () 
  ldtl⊥  (x ∷ₚ p) (x₁ ∷ₚ q) r | nothing | [ eq ] with dec  (x +ᵣ  x₁) 𝟘ᵣ
  ldtl⊥  (x ∷ₚ p) (x₁ ∷ₚ q) () | nothing | [ eq ] | yes x₂
  ... | no x₂ with just-injective r 
  ... | () 

  ldtl⊥sym :  (p q : NonZeroPoly A) → addp q p  ≡  just p → ⊥
  ldtl⊥sym p q r with ldtl⊥ p q (trans (addp-comm p q) r)
  ... | ()


  addpinj : (p q r : NonZeroPoly A) → addp q p ≡ addp r p  → q ≡ r 
  addpinj  (ld a pa) (ld b pb) (ld c pc) h with (dec ) (b +ᵣ  a) 𝟘ᵣ  | (dec ) (c +ᵣ  a) 𝟘ᵣ 
  ... | yes x | yes x₁ = dcong₂ ld (a+x=0=b+x→a=b  a b c x x₁) refl
  ... | no x | no x₁ = dcong₂ ld (a+x=b+x→a=b  a b c (ld-inj hlp)) refl
    where
      hlp :  (ld (b +ᵣ a) x) ≡  (ld (c +ᵣ a) x₁)
      hlp = just-injective h
      
  addpinj  (ld a pa) (ld b pb) (c ∷ₚ tc) h with dec  (b +ᵣ  a) 𝟘ᵣ
  addpinj  (ld a pa) (ld b pb) (c ∷ₚ tc) () | yes x
  addpinj  (ld a pa) (ld b pb) (c ∷ₚ tc) () | no x
  addpinj  (ld a pa) (b ∷ₚ tb) (ld c pc) h with dec  (c +ᵣ  a) (𝟘ᵣ) 
  addpinj  (ld a pa) (b ∷ₚ tb) (ld c pc) () | yes x₁
  addpinj  (ld a pa) (b ∷ₚ tb) (ld c pc) () | no x₁
  addpinj  (ld a pa) (b ∷ₚ tb) (c ∷ₚ tc) h = ∷ₚ-≡ headeq tleq
    where 
      headeq :  b  ≡ c
      headeq  = x+a=x+b→a=b a b c (∷ₚ-injh (just-injective h))
      tleq : tb  ≡ tc 
      tleq  = ∷ₚ-injt (just-injective h)
  addpinj  (a ∷ₚ ta) (ld b pb) (ld c pc) h = ld-≡ (a+x=b+x→a=b  a b c (∷ₚ-injh (just-injective h)))
  addpinj  (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) h with addp tc ta | inspect (addp tc) ta
  ... | just tc+ta | [ eq ] with (∷ₚ-injt(just-injective h))
  ... | res rewrite res with ldtl⊥sym  tc+ta tc eq
  ... | ()
  addpinj  (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) h | nothing | [ eq ] with dec  (hc +ᵣ a) (𝟘ᵣ)
  addpinj  (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) () | nothing | [ eq ] | yes x
  addpinj  (a ∷ₚ ta) (ld b pb) (hc ∷ₚ tc) () | nothing | [ eq ] | no x
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) h with addp tb ta | inspect (addp tb) ta
  ... | just tb+ta | [ eq ] with (∷ₚ-injt(just-injective h))
  ... | res rewrite res  with ldtl⊥sym  ta tb eq 
  ... | ()
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) h | nothing | [ eq ] with dec  (b +ᵣ a) (𝟘ᵣ) 
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) () | nothing | [ eq ] | yes x
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (ld c pc) () | nothing | [ eq ] | no x
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) h with addp tb ta | inspect (addp tb) ta | addp tc ta | inspect (addp tc) ta  
  ... | just x | [ eq ] | just y | [ eq₁ ] = ∷ₚ-≡ hlp2 hlp
    where 
      hlp2 : b ≡ c 
      hlp2 = a+x=b+x→a=b a b c (∷ₚ-injh (just-injective h))
      hlp3 : x ≡ y 
      hlp3 = (∷ₚ-injt (just-injective h))
      hlp4 : x ≡ y → just x ≡ just y
      hlp4 refl = refl
      hlp : tb ≡ tc 
      hlp = addpinj ta tb tc (trans eq (trans (hlp4 hlp3)(sym eq₁)) )
  ... | just x | [ eq ] | nothing | [ eq₁ ] with dec   (c +ᵣ a) (𝟘ᵣ)
  addpinj (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | just x | [ eq ] | nothing | [ eq₁ ] | yes x₁
  addpinj (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | just x | [ eq ] | nothing | [ eq₁ ] | no x₁
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) h | nothing | [ eq ] | just x | [ eq₁ ] with dec   (b +ᵣ a) (𝟘ᵣ)
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | nothing | [ eq ] | just x | [ eq₁ ] | yes x₁
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) () | nothing | [ eq ] | just x | [ eq₁ ] | no x₁
  addpinj  (a ∷ₚ ta) (b ∷ₚ tb) (c ∷ₚ tc) h | nothing | [ eq ] | nothing | [ eq₁ ] with dec  (b +ᵣ a) (𝟘ᵣ) | dec (c +ᵣ a) (𝟘ᵣ)
  ... | yes x | yes x₁ = ∷ₚ-≡ hlp2 (sym hlp)
    where   
      hlp2 : b ≡ c 
      hlp2 = a+x=0=b+x→a=b a b c x x₁
      hlp : tc ≡ tb 
      hlp = addpinj ta tc tb (trans eq₁  (sym eq))
  ... | no x | no x₁ = ∷ₚ-≡ hlp2 (sym hlp)
    where   
      hlp2 : b ≡ c 
      hlp2 = (a+x=b+x→a=b a b c  (ld-inj (just-injective  h)))
      hlp : tc ≡ tb 
      hlp = addpinj ta tc tb (trans eq₁  (sym eq))
  





  -ₚh :  (p : NonZeroPoly A) → ( NonZeroPoly A)
  -ₚh  (ld a x) = ld (-ᵣ a)  (n0→n0  a x)
  -ₚh  (x ∷ₚ p) = (-ᵣ x) ∷ₚ (-ₚh p)

  -ₚ :  (p : Poly A) → ( Poly A)
  -ₚ  𝟘ₚ = 𝟘ₚ
  -ₚ  (non𝟘ₚ p) = non𝟘ₚ (-ₚh p)


  -ₚh-empt :  (p : NonZeroPoly A) → addp (-ₚh p) p ≡ nothing
  -ₚh-empt  (ld a x) with dec  ( (-ᵣ a) +ᵣ a) (𝟘ᵣ)
  ... | yes x₁ = refl
  ... | no x₁ with ¬-elim  x₁ ((-left ) a) 
  ... | () 
  -ₚh-empt  (x ∷ₚ p) with -ₚh-empt p  | addp (-ₚh p) p | inspect (addp (-ₚh p)) p
  ... | h | nothing | [ i ] with dec ( (-ᵣ x) +ᵣ x) (𝟘ᵣ)
  ... | yes x₁ = refl
  ... | no x₁ with ¬-elim  x₁ ((-left ) x) 
  ... | ()
  -ₚh-empt  (x ∷ₚ p) | h | just x₁ | [ i ] with justnoth⊥ (trans (sym h) i)
  ... | ()

  -ₚ-left  :  (p : Poly A) → (-ₚ p) +ₚ p ≡ 𝟘ₚ
  -ₚ-left  𝟘ₚ = refl
  -ₚ-left  (non𝟘ₚ x) with addp (-ₚh x) x | inspect (addp (-ₚh x)) x
  ... | just p | [ i ] with justnoth⊥ (sym(trans (sym i) (-ₚh-empt x )) )
  ... | ()
  -ₚ-left  (non𝟘ₚ x)  | nothing | [ i ] = refl

 
 