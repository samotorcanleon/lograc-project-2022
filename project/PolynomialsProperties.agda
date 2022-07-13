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




  -- write an apology here
  postulate +ₚ-asoc : (p q r : Poly ) → p +ₚ (q +ₚ r) ≡ (p +ₚ q) +ₚ r