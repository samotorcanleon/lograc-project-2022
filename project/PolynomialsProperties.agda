open import Ring
import RingProperties
import Polynomials

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_) renaming (_+_ to _+ⁿ_; _*_ to _*ⁿ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

module PolynomialsProperties (A : Ring) where

  open Ring.Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ; _+_ to _+ᵣ_; _·_ to _·ᵣ_; -_ to -ᵣ_ ;𝟙≠𝟘 to 𝟙ᵣ≠𝟘ᵣ; 𝟙-left to 𝟙ᵣ-left; ·-comm to ·ᵣ-comm)
  open RingProperties {A}

  open Polynomials A

  dcong : ∀ {A : Set} {B : A → Set} (f : (x : A) → B x) {x y}
        → (p : x ≡ y) → subst B p (f x) ≡ f y
  dcong f refl = refl

  dcong₂ : ∀ {A : Set} {B : A → Set} {C : Set}
          (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
        → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
        → f x₁ y₁ ≡ f x₂ y₂
  dcong₂ f refl refl = refl
  justnoth⊥ : {X : Set}{x : X} →  nothing ≡ just x → ⊥
  justnoth⊥ ()
  ¬-elim : ∀ {A : Set}
    → ¬ A
    → A
      ---
    → ⊥
  ¬-elim ¬x x = ¬x x


-- ////////////  ADDITION - commutativity ////////////
  addp-comm :  (p q : NonZeroPoly ) → addp p q ≡ addp q p 
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




  +ₚ-comm : (p q : Poly ) → p +ₚ q ≡ q +ₚ p 
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



-- ////////////  ADDITION - associativity ////////////
  -- write an apology here
  postulate +ₚ-asoc : (p q r : Poly ) → p +ₚ (q +ₚ r) ≡ (p +ₚ q) +ₚ r
  -- associativity turned out to complex to prove because of big number of cases to consider
  -- still we proved a property "(addp q p ≡ addp r p) → q ≡ r" which covers a lot of these cases 
  -- (in case someone would consider tackling the associativity proof ;) )

  ∷ₚ-injh :  ∀ {a b : M } → ∀ {c d : NonZeroPoly} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  a ≡ b 
  ∷ₚ-injh refl = refl

  ∷ₚ-injt :  ∀ {a b : M } → ∀ {c d : NonZeroPoly} → (a ∷ₚ c) ≡ (b ∷ₚ d) →  c ≡ d 
  ∷ₚ-injt refl = refl

  ld-inj :   ∀ {a b : M } → ∀ {c d} → (ld  a c) ≡ (ld b d) → a ≡ b
  ld-inj refl = refl

  ∷ₚ-≡ :  {a b : M } → ∀ {c d : NonZeroPoly} → a ≡ b → c ≡ d  → (a ∷ₚ c) ≡ (b ∷ₚ d)
  ∷ₚ-≡  refl refl = refl 

  ld-≡ :  ∀ {a b : M } → ∀ {c d} → a ≡ b → (ld  a c) ≡ (ld b d)
  ld-≡ {a}{b}{c}{d} p with (dec) a (𝟘ᵣ)
  ld-≡  {𝟘ᵣ} {𝟘ᵣ} {c} {d} refl | yes refl = refl
  ld-≡  {a} {a} {c} {d} refl | no x = refl

  ldtl⊥ :  (p q : NonZeroPoly) → addp p q  ≡  just p → ⊥
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

  ldtl⊥sym :  (p q : NonZeroPoly) → addp q p  ≡  just p → ⊥
  ldtl⊥sym p q r with ldtl⊥ p q (trans (addp-comm p q) r)
  ... | ()

  addpinj : (p q r : NonZeroPoly) → addp q p ≡ addp r p  → q ≡ r 
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


-- ////////////  left inverse for addition ////////////
  -ₚh-empt :  (p : NonZeroPoly) → addp (-ₚh p) p ≡ nothing
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

  -ₚ-left  :  (p : Poly) → (-ₚ p) +ₚ p ≡ 𝟘ₚ
  -ₚ-left  𝟘ₚ = refl
  -ₚ-left  (non𝟘ₚ x) with addp (-ₚh x) x | inspect (addp (-ₚh x)) x
  ... | just p | [ i ] with justnoth⊥ (sym(trans (sym i) (-ₚh-empt x )) )
  ... | ()
  -ₚ-left  (non𝟘ₚ x)  | nothing | [ i ] = refl

-- ////////////  constant polynomial is left unit for addition ////////////
  𝟘ₚ-left  : (p : Poly) → 𝟘ₚ +ₚ p ≡ p
  𝟘ₚ-left p = refl

-- ////////////  DEGREE proofs ////////////

  -- multiplication by constant doesn't change degree
  kmul-deg : (a : M) → (p : NonZeroPoly) → (x : ¬ (a ≡ 𝟘ᵣ)) → degreehlp (kmul a p x) ≡ degreehlp p
  kmul-deg a (ld a₁ x₁) x = refl
  kmul-deg a (x₁ ∷ₚ p) x = cong suc (kmul-deg a p x)

  ·ₖₒₙₛₜ-degree : (a : M) → (p : Poly) → ¬ (a ≡ 𝟘ᵣ) →  degree (·ₖₒₙₛₜ a p) ≡ (degree p)
  ·ₖₒₙₛₜ-degree a 𝟘ₚ x = refl
  ·ₖₒₙₛₜ-degree a (non𝟘ₚ h) pr with dec a 𝟘ᵣ
  ...                                 | yes x with (pr x)
  ...                                          | ()
  ·ₖₒₙₛₜ-degree a (non𝟘ₚ p) pr      | no x = kmul-deg a p pr

  -- multiplication by x increases degree by 1  (NONZERO POLYNOMIALS)
  x·ₚ-deg : (a : NonZeroPoly) → degree (x·ₚ (non𝟘ₚ a)) ≡ 1 +ⁿ (degree (non𝟘ₚ a))
  x·ₚ-deg (ld a x) = refl
  x·ₚ-deg (x ∷ₚ a) = cong suc refl

-- ////////////  MULTIPLICATION - commutativity  ////////////
-- Tip for future agda conqerers: always call all induction steps in the outer most with abstraction otherwise
-- agda will shove her termination checking problems and surprise you with them when you least expect

  merge :  (hb : M) → (tb : NonZeroPoly ) → (pb : ¬ (hb ≡ (𝟘ᵣ))) → (non𝟘ₚ (hb ∷ₚ tb) ≡ non𝟘ₚ (ld hb pb) +ₚ (x·ₚ (non𝟘ₚ tb)))
  merge h t p = cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (𝟘-right h)) refl)

  𝟘ₚ-multi : (p : Poly ) → ·ₚ p 𝟘ₚ ≡ 𝟘ₚ
  𝟘ₚ-multi 𝟘ₚ = refl
  𝟘ₚ-multi (non𝟘ₚ (ld a x)) = refl
  𝟘ₚ-multi (non𝟘ₚ (x ∷ₚ tx)) = sym (begin 𝟘ₚ  ≡⟨ refl ⟩ x·ₚ 𝟘ₚ ≡⟨ cong  x·ₚ (sym (𝟘ₚ-multi (non𝟘ₚ tx))) ⟩ x·ₚ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) ∎)

  m𝟘𝟘 : (k : M) → (·ₖₒₙₛₜ  k 𝟘ₚ) ≡ 𝟘ₚ
  m𝟘𝟘 k with dec k (𝟘ᵣ)
  ... | yes x = refl
  ... | no x = refl

  -- 1ₚ is a multiplication unit
  kmulres : (p : NonZeroPoly ) → kmul 𝟙ᵣ p 𝟙ᵣ≠𝟘ᵣ ≡ p
  kmulres (ld a x) = dcong₂ ld (𝟙ᵣ-left a) refl
  kmulres (x ∷ₚ p) = cong₂ _∷ₚ_ (𝟙ᵣ-left x) (kmulres p)

  1ₚ-left  : (p : Poly ) → (·ₚ 1ₚ p) ≡ p
  1ₚ-left 𝟘ₚ = m𝟘𝟘 𝟙ᵣ
  1ₚ-left (non𝟘ₚ x) with (dec 𝟙ᵣ 𝟘ᵣ)
  1ₚ-left (non𝟘ₚ (ld a x)) | no t = cong non𝟘ₚ (dcong₂ ld (𝟙ᵣ-left a) refl)
  1ₚ-left (non𝟘ₚ (x ∷ₚ x₁)) | no t = cong non𝟘ₚ (cong₂ _∷ₚ_ (𝟙ᵣ-left x) (kmulres x₁))
  ... | yes t with 𝟙ᵣ≠𝟘ᵣ
  ...             | je with je t
  ...                   | ()

  𝟘ᵣ!=𝟘ᵣ→⊥ : ¬ ( 𝟘ᵣ +ᵣ 𝟘ᵣ ≡ 𝟘ᵣ) → ⊥
  𝟘ᵣ!=𝟘ᵣ→⊥ p with ω-left 𝟘ᵣ
  ... | res with p res
  ... | ()

  split∷ₚ : (p q : Poly ) → (x·ₚ (p +ₚ q )) ≡ ((x·ₚ p) +ₚ (x·ₚ q))
  split∷ₚ 𝟘ₚ 𝟘ₚ = refl
  split∷ₚ 𝟘ₚ (non𝟘ₚ x) = refl
  split∷ₚ (non𝟘ₚ x) 𝟘ₚ = refl
  split∷ₚ (non𝟘ₚ x) (non𝟘ₚ y) with addp x y
  ... | just x+y = cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (ω-left 𝟘ᵣ)) refl)
  ... | nothing with dec ( 𝟘ᵣ +ᵣ 𝟘ᵣ) 𝟘ᵣ
  ... | yes x₁ = refl
  ... | no 𝟘ᵣ!=𝟘ᵣ with 𝟘ᵣ!=𝟘ᵣ→⊥ 𝟘ᵣ!=𝟘ᵣ
  ... | ()


  rearrange1 : (a b c d : Poly ) → (a +ₚ c) +ₚ (b +ₚ d) ≡ a +ₚ ((b +ₚ c) +ₚ d)
  rearrange1 a b c d = begin (a +ₚ c) +ₚ (b +ₚ d) 
                                    ≡⟨ sym (+ₚ-asoc a c (b +ₚ d)) ⟩
                              a +ₚ (c +ₚ (b +ₚ d)) 
                                    ≡⟨ cong₂ _+ₚ_ {a} {a} {(c +ₚ (b +ₚ d))} {((c +ₚ b) +ₚ d)} refl (+ₚ-asoc c b d) ⟩
                              a +ₚ ((c +ₚ b) +ₚ d) 
                                    ≡⟨ cong₂ _+ₚ_ {a} {a} {((c +ₚ b) +ₚ d)} {((b +ₚ c) +ₚ d)} refl (cong₂ _+ₚ_ {(c +ₚ b) } {(b +ₚ c) } {d} {d} (+ₚ-comm c b) refl) ⟩
                              a +ₚ ((b +ₚ c) +ₚ d)
                              ∎

  rearrange2 : (a b c d : Poly ) → (a +ₚ b) +ₚ (c +ₚ d) ≡  a +ₚ ((b +ₚ c) +ₚ d)
  rearrange2 a b c d = begin (a +ₚ b) +ₚ (c +ₚ d)
                                    ≡⟨ sym (+ₚ-asoc a b (c +ₚ d)) ⟩
                              a +ₚ (b +ₚ (c +ₚ d)) 
                                    ≡⟨ cong₂ _+ₚ_ {a} {a} {(b +ₚ (c +ₚ d))} {((b +ₚ c) +ₚ d)} refl (+ₚ-asoc b c d) ⟩
                              a +ₚ ((b +ₚ c) +ₚ d)
                              ∎

  e𝟘=e𝟘 :  𝟘ᵣ ≡ 𝟘ᵣ
  e𝟘=e𝟘  = refl

  b=e:ab=e : (a b : M) →  b ≡ 𝟘ᵣ →  a ·ᵣ b ≡ 𝟘ᵣ
  b=e:ab=e a b p =  begin a ·ᵣ b 
                                ≡⟨ cong₂ (_·ᵣ_) refl p ⟩
                          a ·ᵣ 𝟘ᵣ 
                                ≡⟨ 𝟘-multi a ⟩
                          𝟘ᵣ 
                          ∎

  a=e:ab=e : (a b : M) →  a ≡ 𝟘ᵣ →  a ·ᵣ b  ≡ 𝟘ᵣ
  a=e:ab=e a b p = trans (·ᵣ-comm a b) (b=e:ab=e b a p)


  --multiplication commutativity
  ·ₚ-commhlp : (p q : NonZeroPoly ) → (·ₚ (non𝟘ₚ p)  (non𝟘ₚ q)) ≡ (·ₚ (non𝟘ₚ q) (non𝟘ₚ p))
  ·ₚ-commhlp (ld a pa) (ld b pb) with  (dec a 𝟘ᵣ) | dec b 𝟘ᵣ
  ... | yes x₁ | yes x₂ = refl
  ... | yes x₁ | no x₂ with pa x₁
  ...                   | ()
  ·ₚ-commhlp (ld a pa) (ld b pb) | no x₁ | yes x₂ with pb x₂
  ...                                                | ()
  ·ₚ-commhlp (ld a pa) (ld b pb) | no da | no db = cong non𝟘ₚ (dcong₂ ld (·ᵣ-comm a b) refl)

  ·ₚ-commhlp (ld a pa) (hb ∷ₚ tb) with  (dec a 𝟘ᵣ) | dec hb 𝟘ᵣ | inspect (dec a) 𝟘ᵣ
  ... | yes x | reshb | [ eq ] with (pa x)
  ...                  | ()
  ·ₚ-commhlp (ld a pa) (hb ∷ₚ tb) | no x | yes x₁ | [ eq ] rewrite eq = begin non𝟘ₚ (kmul a (hb ∷ₚ tb) x)  
                                                                                    ≡⟨ cong non𝟘ₚ (cong₂ _∷ₚ_ (cong₂ (_·ᵣ_) refl x₁) refl) ⟩
                                                                            non𝟘ₚ ((a ·ᵣ 𝟘ᵣ) ∷ₚ (kmul a tb pa)) 
                                                                                    ≡⟨ cong non𝟘ₚ (cong₂ _∷ₚ_ (𝟘-multi a) refl) ⟩
                                                                            x·ₚ (non𝟘ₚ (kmul a tb pa)) 
                                                                                    ≡⟨ cong x·ₚ help ⟩ -- auxiliary
                                                                            x·ₚ ((·ₖₒₙₛₜ a (non𝟘ₚ tb))) 
                                                                                    ≡⟨ refl ⟩
                                                                            x·ₚ (·ₚ (non𝟘ₚ (ld a pa)) (non𝟘ₚ tb)) 
                                                                                    ≡⟨ cong x·ₚ (·ₚ-commhlp  (ld a pa) tb) ⟩
                                                                            x·ₚ (·ₚ (non𝟘ₚ tb) (non𝟘ₚ (ld a pa))) 
                                                                            ∎
        where
          help : non𝟘ₚ (kmul a tb pa) ≡ (·ₖₒₙₛₜ a (non𝟘ₚ tb))
          help with (dec a 𝟘ᵣ) | inspect (dec a) 𝟘ᵣ
          ... | no x | [ eq ] rewrite eq = cong non𝟘ₚ refl

  ·ₚ-commhlp (ld a pa) (hb ∷ₚ tb) | no x | no x₁ | [ eq ] rewrite eq = sym (begin (non𝟘ₚ (ld (hb ·ᵣ a) (nzd x₁ pa))) +ₚ x·ₚ (·ₚ (non𝟘ₚ tb) (non𝟘ₚ (ld a pa)))
                                                                                        ≡⟨ cong₂ _+ₚ_ {(non𝟘ₚ (ld (hb ·ᵣ a) (nzd x₁ pa)))} {(non𝟘ₚ (ld (a ·ᵣ hb) (nzd pa x₁)))}
                                                                                         {x·ₚ (·ₚ (non𝟘ₚ tb) (non𝟘ₚ (ld a pa)))} {x·ₚ (·ₚ (non𝟘ₚ (ld a pa))  (non𝟘ₚ tb))} 
                                                                                         (cong non𝟘ₚ (dcong₂ ld (·ᵣ-comm hb a) refl)) (cong x·ₚ (sym switch_konst)) ⟩
                                                                                  (non𝟘ₚ (ld (a ·ᵣ hb) (nzd pa x₁))) +ₚ x·ₚ (·ₚ (non𝟘ₚ (ld a pa)) (non𝟘ₚ tb))
                                                                                        ≡⟨ sym split_product ⟩
                                                                                  non𝟘ₚ ((a ·ᵣ hb) ∷ₚ kmul a tb x)
                                                                                  ∎)

          where
            switch_konst :  ·ₖₒₙₛₜ a (non𝟘ₚ tb) ≡ ·ₚ (non𝟘ₚ tb) (non𝟘ₚ (ld a pa))
            switch_konst = begin  ·ₖₒₙₛₜ a (non𝟘ₚ tb) 
                                        ≡⟨ refl ⟩
                                  ·ₚ (non𝟘ₚ (ld a pa)) (non𝟘ₚ tb) 
                                        ≡⟨ ·ₚ-commhlp (ld a pa)  tb ⟩
                                  ·ₚ (non𝟘ₚ tb) (non𝟘ₚ (ld a pa)) 
                                  ∎

            split_product : non𝟘ₚ ((a ·ᵣ hb) ∷ₚ kmul a tb x) ≡ (non𝟘ₚ (ld (a ·ᵣ hb) (nzd pa x₁)) +ₚ x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ tb)))
            split_product with dec a 𝟘ᵣ | inspect (dec a) 𝟘ᵣ
            ... | no x | [ eq ] rewrite eq = cong non𝟘ₚ (cong₂ _∷ₚ_ (sym ((𝟘-right (a ·ᵣ hb)))) refl)

  
  ·ₚ-commhlp (a ∷ₚ ta) (ld b pb) with dec b 𝟘ᵣ | dec a 𝟘ᵣ | (·ₚ-commhlp ta (ld b pb))
  ... | no b!=e | yes a=e | commtab = begin x·ₚ (·ₚ (non𝟘ₚ ta) (non𝟘ₚ (ld b pb))) 
                                                  ≡⟨ cong x·ₚ commtab ⟩
                                            x·ₚ (non𝟘ₚ (kmul b ta b!=e)) 
                                                  ≡⟨ refl ⟩
                                            non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b ta b!=e) 
                                                  ≡⟨ cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (𝟘-multi b)) refl) ⟩
                                            non𝟘ₚ ((b ·ᵣ 𝟘ᵣ) ∷ₚ kmul b ta b!=e) 
                                                  ≡⟨ cong non𝟘ₚ (cong₂ _∷ₚ_ (cong₂ (_·ᵣ_) refl (sym a=e)) refl ) ⟩
                                            non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b ta b!=e) 
                                            ∎
  ... | no b!=e | no a!=e | commtab =  begin  non𝟘ₚ (ld (a ·ᵣ b) (nzd a!=e pb)) +ₚ x·ₚ (·ₚ (non𝟘ₚ ta) (non𝟘ₚ (ld b pb)))
                                                    ≡⟨ cong₂ _+ₚ_ {non𝟘ₚ (ld (a ·ᵣ b) (nzd a!=e pb))} {non𝟘ₚ (ld (b ·ᵣ a) (nzd pb a!=e))}
                                                     {x·ₚ (·ₚ (non𝟘ₚ ta) (non𝟘ₚ (ld b pb)))} {x·ₚ (non𝟘ₚ (kmul b ta b!=e))}
                                                     (cong non𝟘ₚ (dcong₂ ld (·ᵣ-comm a b) refl)) (cong x·ₚ commtab) ⟩
                                              non𝟘ₚ (ld (b ·ᵣ a) (nzd pb a!=e)) +ₚ x·ₚ (non𝟘ₚ (kmul b ta b!=e))  
                                                    ≡⟨ sym split_product ⟩
                                              non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b ta b!=e) 
                                              ∎
                                         where
                                          split_product : non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b ta pb) ≡ non𝟘ₚ (ld (b ·ᵣ a) (nzd pb a!=e)) +ₚ x·ₚ (non𝟘ₚ (kmul b ta b!=e) )
                                          split_product with inspect (dec b) 𝟘ᵣ
                                          ... | [ eq ] rewrite eq =  cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (𝟘-right (b ·ᵣ a))) refl)
  ... | yes x | r2 | commtab with pb x
  ... | ()
  ·ₚ-commhlp (a ∷ₚ x) (b ∷ₚ y) with dec a 𝟘ᵣ | dec b 𝟘ᵣ | inspect (dec b) 𝟘ᵣ | ·ₚ-commhlp x y | ·ₚ-commhlp x (b ∷ₚ y) | ·ₚ-commhlp (a ∷ₚ x) y | ·ₚ-commhlp x y 
  ... | yes x₁ | yes x₂ | [ eqbe ] | commxy | commxby | commyax | commxey = cong x·ₚ (begin ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) 
                                                                                                  ≡⟨ cong₂ ·ₚ {(non𝟘ₚ x)} {(non𝟘ₚ x)} {(non𝟘ₚ (b ∷ₚ y))} {(non𝟘ₚ (𝟘ᵣ ∷ₚ y))} refl (cong non𝟘ₚ (cong₂ _∷ₚ_ x₂ refl)) ⟩
                                                                                            ·ₚ (non𝟘ₚ x) (non𝟘ₚ (𝟘ᵣ ∷ₚ y)) 
                                                                                                  ≡⟨ trans (sym helppls) help22 ⟩
                                                                                            ·ₚ (non𝟘ₚ (𝟘ᵣ ∷ₚ x)) (non𝟘ₚ y) 
                                                                                                  ≡⟨ help ⟩
                                                                                            ·ₚ (non𝟘ₚ y) (non𝟘ₚ ((𝟘ᵣ) ∷ₚ x))  
                                                                                                  ≡⟨ sym (cong₂ ·ₚ {(non𝟘ₚ y)} {(non𝟘ₚ y)} {(non𝟘ₚ (a ∷ₚ x))} {(non𝟘ₚ (𝟘ᵣ ∷ₚ x))} refl (cong non𝟘ₚ (cong₂ _∷ₚ_ x₁ refl))) ⟩
                                                                                            ·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)) 
                                                                                            ∎)

              where
                helppls : ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) ≡ ·ₚ (non𝟘ₚ x) (non𝟘ₚ (𝟘ᵣ ∷ₚ y))
                helppls =  cong₂ ·ₚ {(non𝟘ₚ x)} {(non𝟘ₚ x)} {(non𝟘ₚ (b ∷ₚ y))} {(non𝟘ₚ (𝟘ᵣ ∷ₚ y))} refl (cong non𝟘ₚ (cong₂ _∷ₚ_ x₂ refl))

                help22 : ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) ≡ (·ₖₒₙₛₜ 𝟘ᵣ (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))
                help22  with  dec 𝟘ᵣ 𝟘ᵣ | inspect (dec 𝟘ᵣ) 𝟘ᵣ
                ... | yes e𝟘=e𝟘 | [ eq ] rewrite eq = begin ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) 
                                                                  ≡⟨ commxby ⟩
                                                             x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)) 
                                                                  ≡⟨ cong x·ₚ (sym commxy) ⟩
                                                             x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))  
                                                             ∎

                ... | no e!=e | [ eq ] with ¬-elim e!=e e𝟘=e𝟘
                ... | ()


                help : (·ₖₒₙₛₜ 𝟘ᵣ (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)) ≡ ·ₚ (non𝟘ₚ y) (non𝟘ₚ (𝟘ᵣ ∷ₚ x))
                help with dec 𝟘ᵣ 𝟘ᵣ | inspect (dec 𝟘ᵣ) 𝟘ᵣ
                ... | yes p | [ eq ]  = begin x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)) 
                                                    ≡⟨ refl ⟩
                                              𝟘ₚ +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)) 
                                                    ≡⟨ morehelp ⟩
                                              (·ₖₒₙₛₜ 𝟘ᵣ (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)) 
                                                    ≡⟨⟩
                                              ·ₚ (non𝟘ₚ ((𝟘ᵣ) ∷ₚ x)) (non𝟘ₚ y) 
                                                    ≡⟨ ·ₚ-commhlp  (𝟘ᵣ ∷ₚ x)  y ⟩
                                              ·ₚ (non𝟘ₚ y) (non𝟘ₚ (𝟘ᵣ ∷ₚ x)) 
                                              ∎
                          where
                            morehelp : x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)) ≡ ((·ₖₒₙₛₜ 𝟘ᵣ (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))
                            morehelp with dec 𝟘ᵣ 𝟘ᵣ
                            ... | yes x = cong x·ₚ refl

                ... | no p | [ eq ] with ¬-elim p e𝟘=e𝟘
                ... | ()
                
  ... | yes a=e | no b!=e  | [ eqbe ] | commxy | commxby | commyax  | commxey =  begin  x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y))) 
                                                                                              ≡⟨ cong x·ₚ commxby ⟩
                                                                                        x·ₚ (non𝟘ₚ (kmul b x b!=e) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))) 
                                                                                              ≡⟨ cong x·ₚ (cong₂ _+ₚ_ {non𝟘ₚ (kmul b x b!=e)} {non𝟘ₚ (kmul b x b!=e)}
                                                                                                {x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))} {x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))}
                                                                                                refl (cong x·ₚ (sym commxy))) ⟩
                                                                                        x·ₚ (non𝟘ₚ (kmul b x b!=e) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))  
                                                                                              ≡⟨ split∷ₚ (non𝟘ₚ (kmul b x b!=e)) (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))) ⟩
                                                                                        non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x b!=e) +ₚ x·ₚ( x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))
                                                                                              ≡⟨ cong₂ _+ₚ_ {non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x b!=e)} {non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b x b!=e)}
                                                                                                {x·ₚ( x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))} {x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)))}
                                                                                                (cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (b=e:ab=e b a a=e)) refl)) (cong x·ₚ commyax) ⟩
        -- ·ₚ (non𝟘ₚ y) (non𝟘ₚ (𝟘ᵣ ∷ₚ x)) ≡
        -- ·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x))
                                                                                        non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b x b!=e) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x))) 
                                                                                        ∎

  ... | no a!=e | yes b=e  | [ eqbe ] | commxy | commxby | commyax | commxey = begin non𝟘ₚ ((a ·ᵣ b) ∷ₚ kmul a y a!=e) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)))
                                                                                          ≡⟨ cong₂ _+ₚ_ {non𝟘ₚ ((a ·ᵣ b) ∷ₚ kmul a y a!=e)} {non𝟘ₚ ( (𝟘ᵣ) ∷ₚ kmul a y a!=e)}
                                                                                          {x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)))} {x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)))}
                                                                                          (cong non𝟘ₚ (cong₂ _∷ₚ_ ( b=e:ab=e a b b=e ) refl)) (cong x·ₚ commxby) ⟩
                                                                                      non𝟘ₚ ((𝟘ᵣ) ∷ₚ kmul a y a!=e) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))) 
                                                                                          ≡⟨ refl ⟩
                                                                                      x·ₚ (non𝟘ₚ (kmul a y a!=e)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))) 
                                                                                          ≡⟨ sym (split∷ₚ ((non𝟘ₚ (kmul a y a!=e))) ((x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))))) ⟩
                                                                                      x·ₚ ((non𝟘ₚ (kmul a y a!=e)) +ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))))
                                                                                          ≡⟨ cong x·ₚ (cong₂ _+ₚ_ {non𝟘ₚ (kmul a y a!=e)} {non𝟘ₚ (kmul a y a!=e)} 
                                                                                            {x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))}{x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))} refl (cong x·ₚ (sym commxy))) ⟩
                                                                                      x·ₚ ((non𝟘ₚ (kmul a y a!=e)) +ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))) 
                                                                                          ≡⟨ cong x·ₚ commyax ⟩
                                                                                      x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)))
                                                                                      ∎

  ... | no x₁ | no x₂  | [ eqbe ] | commxy | commxby | commyax | commxey =  begin non𝟘ₚ ((a ·ᵣ b) ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)))
                                                                                        ≡⟨ cong₂ _+ₚ_ {non𝟘ₚ ((a ·ᵣ b) ∷ₚ kmul a y x₁)} {non𝟘ₚ ((a ·ᵣ b) ∷ₚ kmul a y x₁)} 
                                                                                          {x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)))} {x·ₚ ((·ₖₒₙₛₜ b (non𝟘ₚ x)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))}
                                                                                          refl ((cong x·ₚ (reduction1))) ⟩
                                                                                  non𝟘ₚ ((a ·ᵣ b) ∷ₚ kmul a y x₁) +ₚ x·ₚ ((·ₖₒₙₛₜ b (non𝟘ₚ x)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))) 
                                                                                        ≡⟨ split x y a b x₁ x₂ ⟩
                                                                                  ((non𝟘ₚ (ld ((a ·ᵣ b)) (nzd x₁ x₂))) +ₚ (non𝟘ₚ  (𝟘ᵣ ∷ₚ kmul a y x₁))) +ₚ ((x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x))) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))) 
                                                                                        ≡⟨ rearrange2 (non𝟘ₚ (ld ((a ·ᵣ b)) (nzd x₁ x₂))) (non𝟘ₚ (𝟘ᵣ ∷ₚ kmul a y x₁))
                                                                                          (x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x))) (x·ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))) ⟩
                                                                                  ((non𝟘ₚ (ld ((a ·ᵣ b)) (nzd x₁ x₂))) +ₚ (((non𝟘ₚ  ((𝟘ᵣ) ∷ₚ kmul a y x₁)) +ₚ (x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x)))) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))))) 
                                                                                        ≡⟨ cong₂ _+ₚ_ {non𝟘ₚ (ld ((a ·ᵣ b)) (nzd x₁ x₂))} {non𝟘ₚ (ld ((b ·ᵣ a)) (nzd x₂ x₁))} 
                                                                                          {((non𝟘ₚ (𝟘ᵣ ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x))) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))))} 
                                                                                          {((x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x x₂)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))))} 
                                                                                          (cong non𝟘ₚ (dcong₂ ld (·ᵣ-comm a b) refl)) final_comp ⟩
                                                                                  (non𝟘ₚ (ld ((b ·ᵣ a)) (nzd x₂ x₁))) +ₚ (((x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y))) +ₚ (non𝟘ₚ  ((𝟘ᵣ) ∷ₚ kmul b x x₂))) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)))) 
                                                                                        ≡⟨ sym (rearrange1 (non𝟘ₚ (ld ((b ·ᵣ a)) (nzd x₂ x₁))) (x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y))) (non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x x₂)) (x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))))) ⟩
                                                                                  ((non𝟘ₚ (ld ((b ·ᵣ a)) (nzd x₂ x₁))) +ₚ (non𝟘ₚ  (𝟘ᵣ ∷ₚ kmul b x x₂))) +ₚ ((x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y))) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)))) 
                                                                                        ≡⟨ sym (split y x b a x₂ x₁) ⟩
                                                                                  non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b x x₂) +ₚ x·ₚ ((·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))) 
                                                                                        ≡⟨ cong₂ _+ₚ_ {non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b x x₂)} {non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b x x₂)} {x·ₚ ((·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)))} 
                                                                                          {x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)))} refl (cong x·ₚ (sym (reduction2))) ⟩
                                                                                  non𝟘ₚ ((b ·ᵣ a) ∷ₚ kmul b x x₂) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x))) 
                                                                                  ∎
              where
                kmul_konst : (u : NonZeroPoly) → (i : M) → (pi : ¬ (i ≡ 𝟘ᵣ)) → non𝟘ₚ (kmul i u pi) ≡ (·ₖₒₙₛₜ i (non𝟘ₚ u))
                kmul_konst u i pi with dec i 𝟘ᵣ | inspect (dec i) 𝟘ᵣ
                ... | no x | [ eq ]  = cong non𝟘ₚ refl
                ... | yes x | [ eq ] with pi x
                ... | ()



                reduction1 :  ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) ≡ (·ₖₒₙₛₜ b (non𝟘ₚ x)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))
                reduction1 with dec b 𝟘ᵣ | inspect (dec b) 𝟘ᵣ
                ... | no pb | [ eq ] = begin  ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) 
                                                    ≡⟨ hlp ⟩
                                              ·ₚ (non𝟘ₚ (b ∷ₚ y)) (non𝟘ₚ x) 
                                                    ≡⟨ cong₂ _+ₚ_ {(·ₖₒₙₛₜ b (non𝟘ₚ x))} {non𝟘ₚ (kmul b x pb)} {x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))} 
                                                      {x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))} (sym (kmul_konst x b pb)) (cong x·ₚ (sym commxy )) ⟩
                                              non𝟘ₚ (kmul b x pb) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))
                                              ∎
                                    where
                                      hlp : ·ₚ (non𝟘ₚ x) (non𝟘ₚ (b ∷ₚ y)) ≡ (·ₖₒₙₛₜ b (non𝟘ₚ x)) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))
                                      hlp rewrite eq = commxby
                ... | yes pb | [ eq ]  with x₂ pb
                ... | ()

                reduction2 : ·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)) ≡ (·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))
                reduction2 with dec a 𝟘ᵣ | inspect (dec a) 𝟘ᵣ
                ... | no pa | [ eq ] = begin  ·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)) 
                                                    ≡⟨ hlp ⟩
                                              ·ₚ (non𝟘ₚ (a ∷ₚ x)) (non𝟘ₚ y) 
                                                    ≡⟨ cong₂ _+ₚ_ {(·ₖₒₙₛₜ a (non𝟘ₚ y))} {non𝟘ₚ (kmul a y pa)} {x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))}
                                                     {x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))} (sym (kmul_konst y a pa)) (cong x·ₚ ( commxy )) ⟩
                                              non𝟘ₚ (kmul a y pa) +ₚ x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x))
                                              ∎
                                    where
                                      hlp : ·ₚ (non𝟘ₚ y) (non𝟘ₚ (a ∷ₚ x)) ≡ ((·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))
                                      hlp rewrite eq = sym commyax
                ... | yes pa | [ eq ]  with x₁ pa
                ... | ()

                split : (u : NonZeroPoly ) → (v : NonZeroPoly ) → (i : M) → (j : M) → (pi : ¬ (i ≡ (𝟘ᵣ))) → (pj : ¬ (j ≡ (𝟘ᵣ))) → 
                        (non𝟘ₚ ((i ·ᵣ j) ∷ₚ kmul i v pi) +ₚ x·ₚ ((·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))) ≡ (non𝟘ₚ (((i ·ᵣ j) +ᵣ 𝟘ᵣ) ∷ₚ kmul i v pi) +ₚ (x·ₚ (·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))))
                split u v i j pi pj = cong₂ _+ₚ_ {non𝟘ₚ ((i ·ᵣ j) ∷ₚ kmul i v pi)} {non𝟘ₚ (((i ·ᵣ j) +ᵣ 𝟘ᵣ) ∷ₚ kmul i v pi)} {x·ₚ ((·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))} {x·ₚ (·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))}
                                      (merge ((i ·ᵣ j)) (kmul i v pi) (nzd pi pj)) (split∷ₚ  (·ₖₒₙₛₜ j (non𝟘ₚ u)) (x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v))))


                xmul_𝟘ᵣ : (u : NonZeroPoly ) → non𝟘ₚ (𝟘ᵣ ∷ₚ u) ≡ x·ₚ (non𝟘ₚ u)
                xmul_𝟘ᵣ u = refl

                midelement_switch1 : non𝟘ₚ (𝟘ᵣ ∷ₚ kmul a y x₁) ≡ x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y))
                midelement_switch1 with dec a 𝟘ᵣ
                ... | no pa = refl
                ... | yes pa with x₁ pa
                ... | ()

                midelement_switch2 : x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x)) ≡ non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x x₂)
                midelement_switch2 with dec b 𝟘ᵣ
                ... | no pb = refl
                ... | yes pb with x₂ pb
                ... | ()

                final_comp : (non𝟘ₚ (𝟘ᵣ ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x))) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y))) ≡ (x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x x₂)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)))
                final_comp = cong₂ _+ₚ_ {non𝟘ₚ (𝟘ᵣ ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x))} {x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y)) +ₚ non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x x₂)} {x·ₚ (x·ₚ (·ₚ (non𝟘ₚ x) (non𝟘ₚ y)))} {x·ₚ (x·ₚ (·ₚ (non𝟘ₚ y) (non𝟘ₚ x)))}
                              (cong₂ _+ₚ_ {non𝟘ₚ (𝟘ᵣ ∷ₚ kmul a y x₁)} {x·ₚ (·ₖₒₙₛₜ a (non𝟘ₚ y))} {x·ₚ (·ₖₒₙₛₜ b (non𝟘ₚ x))} {non𝟘ₚ (𝟘ᵣ ∷ₚ kmul b x x₂)} midelement_switch1 midelement_switch2) (cong x·ₚ (cong x·ₚ (·ₚ-commhlp x y)))



  ·ₚ-comm : (a : Poly)→ (b : Poly) → (·ₚ a b) ≡ (·ₚ b a)
  ·ₚ-comm 𝟘ₚ 𝟘ₚ = refl
  ·ₚ-comm 𝟘ₚ (non𝟘ₚ (ld a x)) = refl
  ·ₚ-comm 𝟘ₚ (non𝟘ₚ (x ∷ₚ tx)) = begin ·ₚ 𝟘ₚ (non𝟘ₚ (x ∷ₚ tx)) 
                                            ≡⟨⟩ 
                                      𝟘ₚ 
                                            ≡⟨⟩ 
                                      x·ₚ 𝟘ₚ 
                                            ≡⟨ cong x·ₚ (sym (𝟘ₚ-multi (non𝟘ₚ tx)) ) ⟩
                                      x·ₚ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) 
                                      ∎
  ·ₚ-comm (non𝟘ₚ (ld a x)) 𝟘ₚ = refl
  ·ₚ-comm (non𝟘ₚ (x ∷ₚ tx)) 𝟘ₚ = sym (begin  𝟘ₚ 
                                                  ≡⟨ refl ⟩ 
                                            x·ₚ 𝟘ₚ 
                                                  ≡⟨ cong x·ₚ (sym (𝟘ₚ-multi (non𝟘ₚ tx)))⟩
                                            x·ₚ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) 
                                            ∎)
  ·ₚ-comm (non𝟘ₚ x) (non𝟘ₚ y) = ·ₚ-commhlp x y