module project where
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

  --///////////////////////// PROOFS FOR RING /////////////////////////
  -- multiplication with zero
  𝟘-multi : (a : M)  → a · 𝟘 ≡ 𝟘
  𝟘-multi a = sym  (begin   𝟘
                                   ≡⟨ sym (-left (a · 𝟘)) ⟩
                            - (a · 𝟘) + a · 𝟘
                                   ≡⟨ cong ((- (a · 𝟘)) +_) (help a) ⟩
                            - (a · 𝟘) + (a · 𝟘 + a · 𝟘)
                                   ≡⟨ sym (+-assoc _ _ _) ⟩
                            - (a · 𝟘) + a · 𝟘 + a · 𝟘
                                   ≡⟨ cong₂ _+_ ( -left (a · 𝟘 ) ) refl ⟩
                            𝟘 + a · 𝟘
                                   ≡⟨ ω-left (a · 𝟘) ⟩
                            a · 𝟘 ∎)
    where
      help : (a : M) → a · 𝟘 ≡ a · 𝟘 + a · 𝟘
      help a = begin
                     (a · 𝟘)
                        ≡⟨ cong ((_·_) a) (sym ((ω-left) 𝟘)) ⟩
                     a · (𝟘 + 𝟘)
                        ≡⟨ dist-l _ _ _ ⟩
                     a · 𝟘 + a · 𝟘
                   ∎


  -- zero is unit for addition (right)
  𝟘-right : (a : M) → a + 𝟘 ≡ a
  𝟘-right a = begin a + 𝟘 ≡⟨ +-comm a 𝟘 ⟩ 𝟘 + a ≡⟨ ω-left a ⟩ a ∎

  -- two proofs for non-zero a are equivalent
  ≢𝟘-irrelevant : ∀ {a : M} → (p q : ¬ (a ≡ 𝟘)) → p ≡ q
  ≢𝟘-irrelevant p q = fun-ext (λ r → ⊥-elim (p r))

--///////////////////////// POLYNOMIAL DEFINITION /////////////////////////
module _ (A : Ring) where
  open Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ)

  data NonZeroPoly : Set where
    ld : (a : M)  → ¬ (a ≡ 𝟘ᵣ) →  NonZeroPoly
    _∷ₚ_ : M  → NonZeroPoly -> NonZeroPoly

  data Poly : Set where
    𝟘ₚ : Poly
    non𝟘ₚ : NonZeroPoly → Poly

module _ (A : Ring) where
  open Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ; _+_ to _+ᵣ_; _·_ to _·ᵣ_; 𝟙≠𝟘 to 𝟙ᵣ≠𝟘ᵣ; 𝟙-left to 𝟙ᵣ-left; ·-comm to ·ᵣ-comm)
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


  --///////////////////////// PROOFS FOR ADDITION /////////////////////////
  -- write an apology here
  postulate +ₚ-asoc : (p q r : Poly A) → p +ₚ (q +ₚ r) ≡ (p +ₚ q) +ₚ r

  +ₚ-comm : (a : Poly A) → (b : Poly A) → ( a +ₚ b) ≡ ( b +ₚ a)
  +ₚ-comm = {!   !}

  --///////////////////////// MULTIPLICATION DEFINITION /////////////////////////
  kmul : (a : M) → (x : NonZeroPoly A) → ¬ (a ≡ 𝟘ᵣ) → (NonZeroPoly A)
  kmul a (hx ∷ₚ tx) pa = (a ·ᵣ hx) ∷ₚ (kmul a tx pa)
  kmul a (ld hx p) pa = ld (a ·ᵣ hx) (nzd pa p)

  ·ₖₒₙₛₜ : (a : M) → (p : Poly A) -> Poly A
  ·ₖₒₙₛₜ a 𝟘ₚ = 𝟘ₚ
  ·ₖₒₙₛₜ a (non𝟘ₚ x) with dec a 𝟘ᵣ
  ... | yes x₁ = 𝟘ₚ
  ... | no p¬𝟘 = non𝟘ₚ (kmul a x p¬𝟘)

  x·ₚ : (a : Poly A) → Poly A
  x·ₚ 𝟘ₚ = 𝟘ₚ
  x·ₚ (non𝟘ₚ x) = non𝟘ₚ (𝟘ᵣ ∷ₚ x)

  ·ₚ : (a : Poly A) → (b : Poly A) → Poly A
  ·ₚ 𝟘ₚ b = 𝟘ₚ
  ·ₚ (non𝟘ₚ (ld hx p))  b = ·ₖₒₙₛₜ hx b
  ·ₚ (non𝟘ₚ (hx ∷ₚ tx))  b = ·ₖₒₙₛₜ hx b +ₚ x·ₚ (·ₚ (non𝟘ₚ tx)  b)



--   --///////////////////////// CONSTANT ONE AND ZERO POLYNOMIALS /////////////////////////
  1ₚ : Poly A
  1ₚ = non𝟘ₚ (ld 𝟙ᵣ 𝟙ᵣ≠𝟘ᵣ)

  𝟘ₚ-left  : (p : Poly A) → 𝟘ₚ +ₚ p ≡ p
  𝟘ₚ-left p = refl

  Oₚ : (A : Ring) → Poly A
  Oₚ a = 𝟘ₚ

--   --///////////////////////// PROOFS FOR MULTIPLICATION /////////////////////////

  merge :  (hb : M) → (tb : NonZeroPoly A) → (pb : ¬ (hb ≡ (𝟘ᵣ))) → (non𝟘ₚ (hb ∷ₚ tb) ≡ non𝟘ₚ (ld hb pb) +ₚ (x·ₚ (non𝟘ₚ tb)))
  merge h t p = cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (𝟘-right h)) refl)

  𝟘ₚ-multi : (p : Poly A) → ·ₚ p 𝟘ₚ ≡ 𝟘ₚ
  𝟘ₚ-multi 𝟘ₚ = refl
  𝟘ₚ-multi (non𝟘ₚ (ld a x)) = refl
  𝟘ₚ-multi (non𝟘ₚ (x ∷ₚ tx)) = sym (begin 𝟘ₚ  ≡⟨ refl ⟩ x·ₚ 𝟘ₚ ≡⟨ cong  x·ₚ (sym (𝟘ₚ-multi (non𝟘ₚ tx))) ⟩ x·ₚ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) ∎)
  -- begin x·ₚ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) ≡⟨ {! cong   !} ⟩ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) ≡⟨ {!   !} ⟩ 𝟘ₚ ∎
  -- begin x·ₚ (·ₚ (non𝟘ₚ tx) 𝟘ₚ) ≡⟨ {!   !} ⟩ {!   !} ≡⟨ {!   !} ⟩ 𝟘ₚ ∎


  m𝟘𝟘 : (k : M) → (·ₖₒₙₛₜ  k (Oₚ A)) ≡ (Oₚ A)
  m𝟘𝟘 k with dec k (𝟘ᵣ)
  ... | yes x = refl
  ... | no x = refl

  -- 1ₚ is a multiplication unit
  kmulres : (p : NonZeroPoly A) → kmul 𝟙ᵣ p 𝟙ᵣ≠𝟘ᵣ ≡ p
  kmulres (ld a x) = dcong₂ ld (𝟙ᵣ-left a) refl
  kmulres (x ∷ₚ p) = cong₂ _∷ₚ_ (𝟙ᵣ-left x) (kmulres p)

  1ₚ-left  : (p : Poly A) → (·ₚ 1ₚ p) ≡ p
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

  split∷ₚ : (p q : Poly A) → (x·ₚ (p +ₚ q )) ≡ ((x·ₚ p) +ₚ (x·ₚ q))
  split∷ₚ 𝟘ₚ 𝟘ₚ = refl
  split∷ₚ 𝟘ₚ (non𝟘ₚ x) = refl
  split∷ₚ (non𝟘ₚ x) 𝟘ₚ = refl
  split∷ₚ (non𝟘ₚ x) (non𝟘ₚ y) with addp x y
  ... | just x+y = cong non𝟘ₚ (cong₂ _∷ₚ_ (sym (ω-left 𝟘ᵣ)) refl)
  ... | nothing with dec ( 𝟘ᵣ +ᵣ 𝟘ᵣ) 𝟘ᵣ
  ... | yes x₁ = refl
  ... | no 𝟘ᵣ!=𝟘ᵣ with 𝟘ᵣ!=𝟘ᵣ→⊥ 𝟘ᵣ!=𝟘ᵣ
  ... | ()


  rearrange1 : (a b c d : Poly A) → (a +ₚ c) +ₚ (b +ₚ d) ≡ a +ₚ ((b +ₚ c) +ₚ d)
  rearrange1 a b c d = begin (a +ₚ c) +ₚ (b +ₚ d) 
                                    ≡⟨ sym (+ₚ-asoc a c (b +ₚ d)) ⟩
                              a +ₚ (c +ₚ (b +ₚ d)) 
                                    ≡⟨ cong₂ _+ₚ_ {a} {a} {(c +ₚ (b +ₚ d))} {((c +ₚ b) +ₚ d)} refl (+ₚ-asoc c b d) ⟩
                              a +ₚ ((c +ₚ b) +ₚ d) 
                                    ≡⟨ cong₂ _+ₚ_ {a} {a} {((c +ₚ b) +ₚ d)} {((b +ₚ c) +ₚ d)} refl (cong₂ _+ₚ_ {(c +ₚ b) } {(b +ₚ c) } {d} {d} (+ₚ-comm c b) refl) ⟩
                              a +ₚ ((b +ₚ c) +ₚ d)
                              ∎

  rearrange2 : (a b c d : Poly A) → (a +ₚ b) +ₚ (c +ₚ d) ≡  a +ₚ ((b +ₚ c) +ₚ d)
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
  -- {-# TERMINATING #-}
  ·ₚ-commhlp : (p : NonZeroPoly A)→ (q : NonZeroPoly A) → (·ₚ (non𝟘ₚ p)  (non𝟘ₚ q)) ≡ (·ₚ (non𝟘ₚ q) (non𝟘ₚ p))
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
                kmul_konst : (u : NonZeroPoly A) → (i : M) → (pi : ¬ (i ≡ 𝟘ᵣ)) → non𝟘ₚ (kmul i u pi) ≡ (·ₖₒₙₛₜ i (non𝟘ₚ u))
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

                split : (u : NonZeroPoly A) → (v : NonZeroPoly A) → (i : M) → (j : M) → (pi : ¬ (i ≡ (𝟘ᵣ))) → (pj : ¬ (j ≡ (𝟘ᵣ))) → 
                        (non𝟘ₚ ((i ·ᵣ j) ∷ₚ kmul i v pi) +ₚ x·ₚ ((·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))) ≡ (non𝟘ₚ (((i ·ᵣ j) +ᵣ 𝟘ᵣ) ∷ₚ kmul i v pi) +ₚ (x·ₚ (·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))))
                split u v i j pi pj = cong₂ _+ₚ_ {non𝟘ₚ ((i ·ᵣ j) ∷ₚ kmul i v pi)} {non𝟘ₚ (((i ·ᵣ j) +ᵣ 𝟘ᵣ) ∷ₚ kmul i v pi)} {x·ₚ ((·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))} {x·ₚ (·ₖₒₙₛₜ j (non𝟘ₚ u)) +ₚ x·ₚ (x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v)))}
                                      (merge ((i ·ᵣ j)) (kmul i v pi) (nzd pi pj)) (split∷ₚ  (·ₖₒₙₛₜ j (non𝟘ₚ u)) (x·ₚ (·ₚ (non𝟘ₚ u) (non𝟘ₚ v))))


                xmul_𝟘ᵣ : (u : NonZeroPoly A) → non𝟘ₚ (𝟘ᵣ ∷ₚ u) ≡ x·ₚ (non𝟘ₚ u)
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



  ·ₚ-comm : (a : Poly A)→ (b : Poly A) → (·ₚ a b) ≡ (·ₚ b a)
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


  --///////////////////////// DEGREE DEFINITION /////////////////////////
  degreehlp : NonZeroPoly A → ℕ
  degreehlp (ld a x) = 0
  degreehlp (x ∷ₚ p) = 1 +ⁿ degreehlp p

  degree : Poly A → ℕ
  degree 𝟘ₚ = 0
  degree (non𝟘ₚ x) = degreehlp x

 --///////////////////////// PROOFS FOR DEGREE /////////////////////////

  -- multiplication by constant doesn't change degree
  kmul-deg : (a : M) → (p : NonZeroPoly A) → (x : ¬ (a ≡ 𝟘ᵣ)) → degreehlp (kmul a p x) ≡ degreehlp p
  kmul-deg a (ld a₁ x₁) x = refl
  kmul-deg a (x₁ ∷ₚ p) x = cong suc (kmul-deg a p x)

  ·ₖₒₙₛₜ-degree : (a : M) → (p : Poly A) → ¬ (a ≡ 𝟘ᵣ) →  degree (·ₖₒₙₛₜ a p) ≡ (degree p)
  ·ₖₒₙₛₜ-degree a 𝟘ₚ x = refl
  ·ₖₒₙₛₜ-degree a (non𝟘ₚ h) pr with dec a 𝟘ᵣ
  ...                                 | yes x with (pr x)
  ...                                          | ()
  ·ₖₒₙₛₜ-degree a (non𝟘ₚ p) pr      | no x = kmul-deg a p pr

  -- multiplication by x increases degree by 1  (NONZERO POLYNOMIALS)
  x·ₚ-deg : (a : NonZeroPoly A) → degree (x·ₚ (non𝟘ₚ a)) ≡ 1 +ⁿ (degree (non𝟘ₚ a))
  x·ₚ-deg (ld a x) = refl
  x·ₚ-deg (x ∷ₚ a) = cong suc refl

module testZ2 where

  data Num : Set where
    zeroN : Num
    oneN : Num

  _+m_ : (a : Num) → (b : Num) → Num
  zeroN +m b = b
  oneN +m zeroN = oneN
  oneN +m oneN = zeroN
  _*m_ : (a : Num) → (b : Num) → Num
  zeroN *m b = zeroN
  oneN *m b = b

  -rm_ : (a : Num)  → Num
  -rm zeroN = zeroN
  -rm oneN = oneN

  -rml : (m : Num) → (-rm m) +m m ≡ zeroN
  -rml zeroN = refl
  -rml oneN = refl
  -rl  : (m : Num) → (-rm m) +m m ≡ zeroN
  -rl zeroN = refl
  -rl oneN = refl

  -asl : (m : Num) → oneN *m m ≡ m
  -asl zeroN = refl
  -asl oneN = refl
  -asoc : (m₁ m₂ m₃ : Num) → (m₁ *m m₂) *m m₃ ≡ m₁ *m (m₂ *m m₃)
  -asoc zeroN b c = refl
  -asoc oneN b c = refl
  -comm : (m₁ m₂ : Num) → m₁ *m m₂ ≡  m₂ *m m₁
  -comm zeroN zeroN = refl
  -comm zeroN oneN = refl
  -comm oneN zeroN = refl
  -comm oneN oneN = refl
  -wlm : (m : Num) → zeroN +m m ≡ m
  -wlm a = refl
  -a+m : (m₁ m₂ m₃ : Num) → (m₁ +m m₂) +m m₃ ≡ m₁ +m (m₂ +m m₃)
  -a+m zeroN b c = refl
  -a+m oneN zeroN c = refl
  -a+m oneN oneN zeroN = refl
  -a+m oneN oneN oneN = refl
  -+cm : (m₁ m₂ : Num) → m₁ +m m₂ ≡  m₂ +m m₁
  -+cm zeroN zeroN = refl
  -+cm zeroN oneN = refl
  -+cm oneN zeroN = refl
  -+cm oneN oneN = refl
  -dm : (m₁ m₂ m₃ : Num) → m₃ *m (m₁ +m m₂) ≡ (m₃ *m m₁) +m (m₃ *m m₂)
  -dm a b zeroN = refl
  -dm a b oneN = refl
  -decm : (x y : Num) → Dec(x ≡ y)
  -decm zeroN zeroN = yes refl
  -decm zeroN oneN = no λ ()
  -decm oneN zeroN = no λ ()
  -decm oneN oneN = yes refl
  -nzdm : {x y : Num}  → ¬ (x ≡ zeroN) → ¬ (y ≡ zeroN) → ¬ ((x *m y) ≡ zeroN)
  -nzdm {zeroN} {zeroN} a b = b
  -nzdm {zeroN} {oneN} a b = a
  -nzdm {oneN} {y} a b = b

  -1ni𝟘 : ¬ (oneN ≡ zeroN)
  -1ni𝟘 ()

  ring2 : Ring
  ring2 = record { M = Num
      ; 𝟙 = oneN ;
      _·_  = _*m_  ;
      𝟘 = zeroN;
      _+_ = _+m_    ;
      -_ = -rm_ ;
      -left = -rl ;
      𝟙-left  = -asl ;
      ·-assoc = -asoc ;
      ·-comm = -comm ;
      ω-left  = -wlm ;
      +-assoc = -a+m ;
      +-comm = -+cm ;
      dist-l = -dm ;
      dec = -decm ;
      nzd = -nzdm ;
      𝟙≠𝟘 = -1ni𝟘
                  }
  -- t1_p : Poly ring2
  -- t1_p = 𝟘ₚ
  -- t1_q : Poly ring2
  -- t1_q = 𝟘ₚ
  -- test1 : (t1_p +ₚ t1_q) ≡ 𝟘ₚ
  -- test1 = refl
  -- --  testi za  +ₚ
  -- hlp : ¬ (oneN ≡ zeroN)
  -- hlp ()


  -- t2_p : Poly ring2
  -- t2_p = non𝟘ₚ (zeroN ∷ₚ (oneN ∷ₚ (oneN ∷ₚ (ld oneN   hlp ))))
  -- t2_q : Poly ring2
  -- t2_q = non𝟘ₚ (zeroN ∷ₚ (zeroN ∷ₚ (oneN ∷ₚ (ld oneN hlp))))
  -- test2 : (t2_p +ₚ t2_q) ≡ non𝟘ₚ (zeroN ∷ₚ (ld oneN hlp))
  -- test2 = refl

  -- --  testi za  ·ₚ
  -- t4_p : Poly ring2
  -- t4_p = non𝟘ₚ (ld oneN  hlp )
  -- t4_q : Poly ring2
  -- t4_q = non𝟘ₚ (ld oneN hlp )
  -- test4 : (·ₚ t4_p  t4_q) ≡ t4_p
  -- test4 = refl

  -- t3_p : Poly ring2
  -- t3_p = non𝟘ₚ (zeroN ∷ₚ (oneN ∷ₚ (oneN ∷ₚ (ld oneN  hlp ))))
  -- t3_q : Poly ring2
  -- t3_q = non𝟘ₚ (zeroN ∷ₚ (zeroN ∷ₚ (oneN ∷ₚ (ld oneN hlp ))))
  -- test3 : (·ₚ t3_p  t3_q) ≡ non𝟘ₚ (zeroN ∷ₚ(zeroN ∷ₚ(zeroN ∷ₚ(oneN ∷ₚ(zeroN ∷ₚ(zeroN ∷ₚ (ld oneN hlp)))))))
  -- test3 = refl
