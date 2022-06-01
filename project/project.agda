module project where 
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
-- open import Data.List using (List; []; _∷_; length)


open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
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

--///////////////////////// PROOFS FOR RING /////////////////////////
-- multiplication with zero
e₊-multi : (A : Ring) → (a : M A) → ((_·_ A) a (e₊ A)) ≡ (e₊ A)
e₊-multi (A) a = sym  (begin   (e₊ A) ≡⟨ sym ((-ᵣ-left A) ((_·_ A) a (e₊ A))) ⟩ 
                                                    (_+ᵣ_ A) ((-ᵣ_ A) ((_·_ A) a (e₊ A))) ((_·_ A) a (e₊ A)) 
                                    ≡⟨ cong (A +ᵣ (-ᵣ A) ((A · a) (e₊ A))) (help a) ⟩ 
                                                    (_+ᵣ_ A) ((-ᵣ_ A) ((_·_ A) a (e₊ A))) ((_+ᵣ_ A) ((_·_ A) a (e₊ A)) ((_·_ A) a (e₊ A)))
                                    ≡⟨ sym ((+-assoc A)  ((-ᵣ_ A) ((_·_ A) a (e₊ A))) ((_·_ A) a (e₊ A)) ((_·_ A) a (e₊ A))) ⟩ 
                                                    (_+ᵣ_ A) ((_+ᵣ_ A) ((-ᵣ_ A) ((_·_ A) a (e₊ A)))  ((_·_ A) a (e₊ A))) ((_·_ A) a (e₊ A))
                                    ≡⟨ cong₂ (_+ᵣ_ A) ((-ᵣ-left A) ((_·_ A) a (e₊ A))) refl ⟩ (_+ᵣ_ A) (e₊ A) ((_·_ A) a (e₊ A))
                                    ≡⟨ (ω-left A) ((_·_ A) a (e₊ A)) ⟩ ((_·_ A) a (e₊ A)) ∎) 

  where help : (a : M A) → ((_·_ A) a (e₊ A)) ≡ ((_+ᵣ_ A)  ((_·_ A) a (e₊ A)) ((_·_ A) a (e₊ A)))
        help a = begin ((_·_ A) a (e₊ A)) ≡⟨ cong ((_·_ A) a) (sym ((ω-left A) (e₊ A))) ⟩ ((_·_ A) a ((_+ᵣ_ A) (e₊ A) (e₊ A))) 
                                          ≡⟨ (dist-l A) ((e₊ A)) ((e₊ A)) a ⟩ ((_+ᵣ_ A)  ((_·_ A) a (e₊ A)) ((_·_ A) a (e₊ A))) 
                                          ∎


-- zero is unit for addition (right) 
e₊-right : {A : Ring} → (a : M A) → ((_+ᵣ_ A) a (e₊ A)) ≡ a 
e₊-right {A} a = begin ((_+ᵣ_ A) a (e₊ A)) ≡⟨ (+-comm A) a (e₊ A) ⟩ ((_+ᵣ_ A) (e₊ A) a) ≡⟨ (ω-left A) a ⟩ a ∎

-- two proofs for non-zero a are equivalent
≢e₊-irrelevant : ∀ {A} {a : M A} → (p q : ¬ (a ≡ (e₊ A))) → p ≡ q
≢e₊-irrelevant p q = fun-ext (λ r → ⊥-elim (p r))

--///////////////////////// POLYNOMIAL DEFINITION /////////////////////////
data NonZeroPoly (A : Ring): Set where 
  ld : (a : M A)  → ¬ (a ≡ (e₊ A)) →  NonZeroPoly A
  _∷ₚ_ : (M A)  → NonZeroPoly A -> NonZeroPoly A

data Poly  (A : Ring): Set where 
  0ₚ : Poly A
  non0ₚ : NonZeroPoly A → Poly A

--///////////////////////// ADDITION DEFINITION /////////////////////////
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

_+ₚ_ : {A : Ring} → (a : Poly A )→ (b : Poly A) → Poly A
0ₚ +ₚ b = b
non0ₚ x +ₚ 0ₚ = non0ₚ x
non0ₚ x +ₚ non0ₚ y with (addp x y)
... | just res = non0ₚ res
... | nothing = 0ₚ





--///////////////////////// PROOFS FOR ADDITION /////////////////////////
+ₚ-asoc : {A : Ring} → (p q r : Poly A) → p +ₚ (q +ₚ r) ≡ (p +ₚ q) +ₚ r
+ₚ-asoc = {!   !}

+ₚ-comm : {A : Ring} → (a : Poly A) → (b : Poly A) → ( a +ₚ b) ≡ ( b +ₚ a)
+ₚ-comm = {!   !}

--///////////////////////// MULTIPLICATION DEFINITION /////////////////////////
kmul : {A : Ring} → (a : M A) → (x : NonZeroPoly A) → ¬ (a ≡ (e₊ A)) → (NonZeroPoly A)
kmul {A} a (hx ∷ₚ tx) pa = ((_·_ A) a hx) ∷ₚ (kmul a tx pa)
kmul {A} a (ld hx p) pa = ld ((_·_ A) a hx) ((nzd A) pa p)

·ₖₒₙₛₜ : {A : Ring} → (a : M A) → (p : Poly A) -> Poly A
·ₖₒₙₛₜ {A} a 0ₚ = 0ₚ
·ₖₒₙₛₜ {A} a (non0ₚ x) with (dec A) a (e₊ A) 
... | yes x₁ = 0ₚ
... | no p¬e₊ = non0ₚ (kmul a x p¬e₊)

x·ₚ : {A : Ring} → (a : Poly A) → Poly A
x·ₚ 0ₚ = 0ₚ
x·ₚ {A} (non0ₚ x) = non0ₚ ((e₊ A) ∷ₚ x)

·ₚ : {A : Ring} → (a : Poly A)→ (b : Poly A) → Poly A 
·ₚ 0ₚ b = 0ₚ 
·ₚ {A} (non0ₚ (ld hx p))  b = ·ₖₒₙₛₜ hx b
-- ·ₚ {A} b (non0ₚ (ld hx p))  = ·ₖₒₙₛₜ hx b
·ₚ (non0ₚ (hx ∷ₚ tx))  b = (·ₖₒₙₛₜ hx b) +ₚ (x·ₚ (·ₚ (non0ₚ tx)  b))



--///////////////////////// CONSTANT ONE AND ZERO POLYNOMIALS /////////////////////////
1ₚ : {A : Ring} → Poly A
1ₚ {A} = non0ₚ (ld (1ᵣ A) (1ᵣ≠e₊ A))
-- ω-left  : (m : M) → e₊ +ᵣ m ≡ m
0ₚ-left  : {A : Ring} → (p : Poly A) → 0ₚ +ₚ p ≡ p
0ₚ-left p = refl

Oₚ : (A : Ring) → Poly A 
Oₚ  a = 0ₚ

--///////////////////////// PROOFS FOR MULTIPLICATION /////////////////////////

merge :  {A : Ring} → (hb : M A) → (tb : NonZeroPoly A) → (pb : ¬ (hb ≡ (e₊ A))) → (non0ₚ (hb ∷ₚ tb) ≡ non0ₚ (ld hb pb) +ₚ (x·ₚ (non0ₚ tb)))
merge {A} h t p = cong non0ₚ (cong₂ _∷ₚ_ (sym (e₊-right {A} h)) refl)

0ₚ-multi : {A : Ring} → (p : Poly A) → ·ₚ p 0ₚ ≡ 0ₚ
0ₚ-multi {A} 0ₚ = refl
0ₚ-multi {A} (non0ₚ (ld a x)) = refl
0ₚ-multi {A} (non0ₚ (x ∷ₚ tx)) = sym (begin 0ₚ  ≡⟨ refl ⟩ x·ₚ 0ₚ ≡⟨ cong  x·ₚ (sym (0ₚ-multi (non0ₚ tx))) ⟩ x·ₚ (·ₚ (non0ₚ tx) 0ₚ) ∎)
-- begin x·ₚ (·ₚ (non0ₚ tx) 0ₚ) ≡⟨ {! cong   !} ⟩ (·ₚ (non0ₚ tx) 0ₚ) ≡⟨ {!   !} ⟩ 0ₚ ∎
-- begin x·ₚ (·ₚ (non0ₚ tx) 0ₚ) ≡⟨ {!   !} ⟩ {!   !} ≡⟨ {!   !} ⟩ 0ₚ ∎


m00 : {A : Ring}  → (k : M A) → (·ₖₒₙₛₜ  k (Oₚ A)) ≡ (Oₚ A)
m00 {A} k with (dec A) k (e₊ A) 
... | yes x = refl
... | no x = refl

-- 1ₚ is a multiplication unit
kmulres : (A : Ring) →  (p : NonZeroPoly A) → kmul (1ᵣ A) p (1ᵣ≠e₊ A) ≡ p 
kmulres A (ld a x) = dcong₂ ld ((1ᵣ-left A) a) refl
kmulres A (x ∷ₚ p) = cong₂ _∷ₚ_ (((1ᵣ-left A) x)) (kmulres A p)

1ₚ-left  : {A : Ring}  →  (p : Poly A) → (·ₚ 1ₚ  p) ≡ p
1ₚ-left {A} 0ₚ = m00 (1ᵣ A)
1ₚ-left {A} (non0ₚ x) with (dec A (1ᵣ A) (e₊ A)) 
1ₚ-left {A} (non0ₚ (ld a x)) | no t = cong non0ₚ (dcong₂ ld ((1ᵣ-left A) a) refl)
1ₚ-left {A} (non0ₚ (x ∷ₚ x₁)) | no t = cong non0ₚ (cong₂ _∷ₚ_  ((1ᵣ-left A) x) (kmulres A x₁))
... | yes t with (1ᵣ≠e₊ A)
...             | je with je t 
...                   | ()

e₊!=e₊→⊥ : {A : Ring} → ¬ ((A +ᵣ e₊ A) (e₊ A) ≡ e₊ A) → ⊥
e₊!=e₊→⊥ {A} p with  (ω-left A) (e₊ A) 
... | res with p res 
... | () 

split∷ₚ : {A : Ring} → (p q : Poly A) → (x·ₚ (p +ₚ q )) ≡ ((x·ₚ p) +ₚ (x·ₚ q)) 
split∷ₚ {A} 0ₚ 0ₚ = refl
split∷ₚ {A} 0ₚ (non0ₚ x) = refl
split∷ₚ {A} (non0ₚ x) 0ₚ = refl
split∷ₚ {A} (non0ₚ x) (non0ₚ y) with addp x y
... | just x+y = cong non0ₚ (cong₂ _∷ₚ_ (sym ((ω-left A) (e₊ A))) refl)
... | nothing with dec A ((A +ᵣ e₊ A) (e₊ A)) (e₊ A)
... | yes x₁ = refl
... | no e₊!=e₊ with e₊!=e₊→⊥ {A} e₊!=e₊
... | ()


rearrange1 : {A : Ring} → (a b c d : Poly A) → (a +ₚ c) +ₚ (b +ₚ d) ≡ a +ₚ ((b +ₚ c) +ₚ d)
rearrange1 {A} a b c d = begin (a +ₚ c) +ₚ (b +ₚ d) ≡⟨ sym (+ₚ-asoc a c (b +ₚ d)) ⟩ 
                                a +ₚ (c +ₚ (b +ₚ d)) ≡⟨ cong₂ _+ₚ_ {a} {a} {(c +ₚ (b +ₚ d))} {((c +ₚ b) +ₚ d)} refl (+ₚ-asoc c b d) ⟩
                                a +ₚ ((c +ₚ b) +ₚ d) ≡⟨ cong₂ _+ₚ_ {a} {a} {((c +ₚ b) +ₚ d)} {((b +ₚ c) +ₚ d)} refl (cong₂ _+ₚ_ {(c +ₚ b) } {(b +ₚ c) } {d} {d} (+ₚ-comm c b) refl) ⟩ 
                                  (a +ₚ ((b +ₚ c) +ₚ d))∎

rearrange2 : {A : Ring} → (a b c d : Poly A) → (a +ₚ b) +ₚ (c +ₚ d) ≡  a +ₚ ((b +ₚ c) +ₚ d)
rearrange2 {A} a b c d = begin (a +ₚ b) +ₚ (c +ₚ d) ≡⟨ sym (+ₚ-asoc a b (c +ₚ d)) ⟩ 
                                a +ₚ (b +ₚ (c +ₚ d)) ≡⟨ cong₂ _+ₚ_ {a} {a} {(b +ₚ (c +ₚ d))} {((b +ₚ c) +ₚ d)} refl (+ₚ-asoc b c d) ⟩
                                (a +ₚ ((b +ₚ c) +ₚ d)) ∎

e0=e0 : {A : Ring} →  e₊ A ≡ e₊ A
e0=e0  = refl

b=e:ab=e : {A : Ring} → (a b : M A) →  b ≡ (e₊ A) →  (A · a) b ≡ e₊ A
b=e:ab=e {A} a b p =  begin (A · a) b ≡⟨ cong₂ (_·_ A) refl p ⟩ (A · a) (e₊ A) ≡⟨ e₊-multi A a ⟩ e₊ A ∎

a=e:ab=e : {A : Ring} → (a b : M A) →  a ≡ (e₊ A) →  (A · a) b ≡ e₊ A
a=e:ab=e {A} a b p = trans ((·-comm A) a b ) (b=e:ab=e {A} b a p)


--multiplication commutativity
-- {-# TERMINATING #-}
·ₚ-commhlp : {A : Ring} → (p : NonZeroPoly A)→ (q : NonZeroPoly A) → (·ₚ (non0ₚ p)  (non0ₚ q)) ≡ (·ₚ (non0ₚ q) (non0ₚ p))
·ₚ-commhlp {A} (ld a pa) (ld b pb) with  (dec A a (e₊ A)) | dec A b (e₊ A)
... | yes x₁ | yes x₂ = refl
... | yes x₁ | no x₂ with pa x₁ 
...                   | ()
·ₚ-commhlp {A} (ld a pa) (ld b pb) | no x₁ | yes x₂ with pb x₂
...                                                | ()
·ₚ-commhlp {A} (ld a pa) (ld b pb) | no da | no db = cong non0ₚ (dcong₂ ld ((·-comm A) a b) refl)

·ₚ-commhlp {A} (ld a pa) (hb ∷ₚ tb) with  (dec A a (e₊ A)) | dec A hb (e₊ A) | inspect (dec A a) (e₊ A) 
... | yes x | reshb | [ eq ] with (pa x)
...                  | ()
·ₚ-commhlp {A} (ld a pa) (hb ∷ₚ tb) | no x | yes x₁ | [ eq ] rewrite eq = begin non0ₚ (kmul a (hb ∷ₚ tb) x)  ≡⟨ cong non0ₚ (cong₂ _∷ₚ_ (cong₂ (_·_ A) refl x₁) refl) ⟩ 
                                                    non0ₚ (((_·_ A) a (e₊ A)) ∷ₚ (kmul a tb pa)) ≡⟨ cong non0ₚ (cong₂ _∷ₚ_ (e₊-multi A a) refl) ⟩
                                                    x·ₚ (non0ₚ (kmul a tb pa)) ≡⟨ cong x·ₚ help ⟩ -- auxiliary
                                                    x·ₚ ((·ₖₒₙₛₜ a (non0ₚ tb))) ≡⟨ refl ⟩
                                                    x·ₚ (·ₚ (non0ₚ (ld a pa)) (non0ₚ tb)) ≡⟨ cong x·ₚ (·ₚ-commhlp  (ld a pa) tb) ⟩  
                                                    x·ₚ (·ₚ (non0ₚ tb) (non0ₚ (ld a pa))) ∎
      where 
        help : non0ₚ (kmul a tb pa) ≡ (·ₖₒₙₛₜ a (non0ₚ tb))
        help with (dec A a (e₊ A)) | (inspect (dec A a) (e₊ A)) 
        ... | no x | [ eq ] rewrite eq = cong non0ₚ refl
        
·ₚ-commhlp {A} (ld a pa) (hb ∷ₚ tb) | no x | no x₁ | [ eq ] rewrite eq = sym (begin  (non0ₚ (ld ((A · hb) a) (nzd A x₁ pa))) +ₚ x·ₚ (·ₚ (non0ₚ tb) (non0ₚ (ld a pa))) 
                                                                    ≡⟨ cong₂ _+ₚ_ {(non0ₚ (ld ((A · hb) a) (nzd A x₁ pa)))} {(non0ₚ (ld ((A · a) hb) (nzd A pa x₁)))} {x·ₚ (·ₚ (non0ₚ tb) (non0ₚ (ld a pa)))} {x·ₚ (·ₚ (non0ₚ (ld a pa))  (non0ₚ tb))} (cong non0ₚ (dcong₂ ld ((·-comm A) hb a) refl)) (cong x·ₚ (sym switch_konst)) ⟩
                                                                    ((non0ₚ (ld ((A · a) hb) (nzd A pa x₁))) +ₚ x·ₚ (·ₚ (non0ₚ (ld a pa))  (non0ₚ tb))) ≡⟨ sym split_product ⟩
                                                                    non0ₚ ((A · a) hb ∷ₚ kmul a tb x)
                                                                    ∎ )
                                                                    
        where
          switch_konst :  ·ₖₒₙₛₜ a (non0ₚ tb) ≡ ·ₚ (non0ₚ tb) (non0ₚ (ld a pa))
          switch_konst = begin ·ₖₒₙₛₜ a (non0ₚ tb) ≡⟨ refl ⟩ ·ₚ (non0ₚ (ld a pa)) (non0ₚ tb) ≡⟨ ·ₚ-commhlp  (ld a pa)  tb ⟩ ·ₚ (non0ₚ tb) (non0ₚ (ld a pa)) ∎

          split_product : non0ₚ ((A · a) hb ∷ₚ kmul a tb x) ≡ (non0ₚ (ld ((A · a) hb) (nzd A pa x₁)) +ₚ x·ₚ (·ₖₒₙₛₜ a (non0ₚ tb)))
          split_product with dec A a (e₊ A) | inspect (dec A a) (e₊ A)
          ... | no x | [ eq ] rewrite eq = cong non0ₚ (cong₂ _∷ₚ_ (sym ((e₊-right {A} ( (A · a) hb)))) refl)

-- begin ? ≡⟨ ? ⟩ ? ∎
·ₚ-commhlp {A} (a ∷ₚ ta) (ld b pb) with (dec A) b (e₊ A) | (dec A) a (e₊ A) | (·ₚ-commhlp ta (ld b pb))
... | no b!=e | yes a=e | commtab = begin x·ₚ (·ₚ (non0ₚ ta) (non0ₚ (ld b pb))) ≡⟨ cong x·ₚ commtab ⟩ 
                                    x·ₚ (non0ₚ (kmul b ta b!=e)) ≡⟨ refl ⟩ 
                                    non0ₚ ((e₊ A) ∷ₚ kmul b ta b!=e) ≡⟨ cong non0ₚ (cong₂ _∷ₚ_ (sym (e₊-multi A b )) refl) ⟩ 
                                    non0ₚ ((A · b) (e₊ A) ∷ₚ kmul b ta b!=e) ≡⟨ cong non0ₚ (cong₂ _∷ₚ_ (cong₂ (_·_ A) refl (sym a=e)) refl ) ⟩ 
                                    non0ₚ ((A · b) a ∷ₚ kmul b ta b!=e) ∎
... | no b!=e | no a!=e | commtab =  begin (non0ₚ (ld ((A · a) b) (nzd A a!=e pb)) +ₚ x·ₚ (·ₚ (non0ₚ ta) (non0ₚ (ld b pb)))) 
                                        ≡⟨ cong₂ _+ₚ_ {non0ₚ (ld ((A · a) b) (nzd A a!=e pb))}{non0ₚ (ld ((A · b) a) (nzd A pb a!=e))}{x·ₚ (·ₚ (non0ₚ ta) (non0ₚ (ld b pb)))}{x·ₚ (non0ₚ (kmul b ta b!=e))} 
                                        (cong non0ₚ (dcong₂ ld (·-comm A a b) refl)) (cong x·ₚ commtab) ⟩
                                      ((non0ₚ (ld ((A · b) a) (nzd A pb a!=e)) +ₚ x·ₚ (non0ₚ (kmul b ta b!=e) ) )) ≡⟨ sym split_product ⟩
                                       non0ₚ ((A · b) a ∷ₚ kmul b ta b!=e) ∎
                                       where 
                                        split_product : non0ₚ ((A · b) a ∷ₚ kmul b ta pb) ≡ non0ₚ (ld ((A · b) a) (nzd A pb a!=e)) +ₚ x·ₚ (non0ₚ (kmul b ta b!=e) ) 
                                        split_product with inspect (dec A b) (e₊ A)
                                        ... | [ eq ] rewrite eq =  cong non0ₚ (cong₂ _∷ₚ_ (sym ((e₊-right {A} ( (A · b) a)))) refl)
... | yes x | r2 | commtab with pb x 
... | ()
·ₚ-commhlp {A} (a ∷ₚ x) (b ∷ₚ y) with (dec A) a (e₊ A) | (dec A) b (e₊ A) |  (inspect (dec A b)) (e₊ A)  |  (·ₚ-commhlp x y) | (·ₚ-commhlp x (b ∷ₚ y) ) | (·ₚ-commhlp (a ∷ₚ x) y  ) | (·ₚ-commhlp  x y  )
... | yes x₁ | yes x₂ | [ eqbe ] | commxy | commxby | commyax | commxey = cong x·ₚ ( begin ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡⟨ cong₂ ·ₚ {(non0ₚ x)} {(non0ₚ x)} {(non0ₚ (b ∷ₚ y))} {(non0ₚ (e₊ A ∷ₚ y))} refl (cong non0ₚ (cong₂ _∷ₚ_ x₂ refl)) ⟩
                                          ·ₚ (non0ₚ x) (non0ₚ ((e₊ A) ∷ₚ y)) ≡⟨ trans (sym helppls) help22 ⟩
                                          ·ₚ (non0ₚ ((e₊ A) ∷ₚ x)) (non0ₚ y)  ≡⟨ help ⟩
                                          ·ₚ (non0ₚ y) (non0ₚ ((e₊ A) ∷ₚ x))  ≡⟨ sym (cong₂ ·ₚ {(non0ₚ y)} {(non0ₚ y)} {(non0ₚ (a ∷ₚ x))} {(non0ₚ (e₊ A ∷ₚ x))} refl (cong non0ₚ (cong₂ _∷ₚ_ x₁ refl))) ⟩
                                          ·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x)) ∎)

            where 
              helppls : ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡ ·ₚ (non0ₚ x) (non0ₚ ((e₊ A) ∷ₚ y))
              helppls =  cong₂ ·ₚ {(non0ₚ x)}{(non0ₚ x)}{(non0ₚ (b ∷ₚ y))}{(non0ₚ ((e₊ A) ∷ₚ y))} refl (cong non0ₚ (cong₂ _∷ₚ_ x₂ refl))

              help22 : ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡ (·ₖₒₙₛₜ (e₊ A) (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))
              help22  with  dec A (e₊ A) (e₊ A) | (inspect  (dec A (e₊ A)))(e₊ A)
              ... | yes e0=e0 | [ eq ] rewrite eq = begin ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡⟨ commxby ⟩ 
                                                          x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)) ≡⟨ cong x·ₚ (sym commxy) ⟩ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))  ∎
                                                                
              ... | no e!=e | [ eq ] with ¬-elim e!=e (e0=e0 {A})
              ... | () 

              
              help : ((·ₖₒₙₛₜ (e₊ A) (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))) ≡ ·ₚ (non0ₚ y) (non0ₚ (e₊ A ∷ₚ x))
              help with dec A (e₊ A) (e₊ A) | inspect (dec A (e₊ A)) (e₊ A) 
              ... | yes p | [ eq ]  = begin x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)) ≡⟨ refl ⟩ 
                                  (0ₚ +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))) ≡⟨ morehelp ⟩
                                  (((·ₖₒₙₛₜ (e₊ A) (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))) ≡⟨⟩
                                  ·ₚ (non0ₚ ((e₊ A) ∷ₚ x)) (non0ₚ y) ≡⟨ ·ₚ-commhlp  ((e₊ A) ∷ₚ x)  y ⟩
                                  ·ₚ (non0ₚ y)  (non0ₚ ((e₊ A) ∷ₚ x)) ∎
                        where
                          morehelp : x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)) ≡ ((·ₖₒₙₛₜ (e₊ A) (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))
                          morehelp with dec A (e₊ A) (e₊ A)
                          ... | yes x = cong x·ₚ refl
                          
              ... | no p | [ eq ] with ¬-elim p (e0=e0 {A}) 
              ... | ()
              -- begin ? ≡⟨ ? ⟩ ? ∎
... | yes a=e | no b!=e  | [ eqbe ] | commxy | commxby | commyax  | commxey =  begin x·ₚ (·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y))) ≡⟨ cong x·ₚ commxby ⟩
                                                                                x·ₚ (non0ₚ (kmul b x b!=e) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))) ≡⟨ cong x·ₚ (cong₂ _+ₚ_ {non0ₚ (kmul b x b!=e)}{non0ₚ (kmul b x b!=e)}
                                                                                                                                                     {x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))}{x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))}
                                                                                                                                                      refl (cong x·ₚ (sym commxy))) ⟩ 
                                                                                x·ₚ (non0ₚ (kmul b x b!=e) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))  ≡⟨ split∷ₚ (non0ₚ (kmul b x b!=e)) (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))) ⟩ 
                                                                                ((non0ₚ ((e₊ A) ∷ₚ kmul b x b!=e) +ₚ x·ₚ(  x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))))) 
                                                                                ≡⟨ cong₂ _+ₚ_ {non0ₚ (e₊ A ∷ₚ kmul b x b!=e)}{non0ₚ ((A · b) a ∷ₚ kmul b x b!=e)}
                                                                                          {x·ₚ(  x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))}{x·ₚ (·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x)))} 
                                                                                (cong non0ₚ (cong₂ _∷ₚ_ (sym (b=e:ab=e {A} b a a=e)) refl)) (  cong x·ₚ commyax ) ⟩ 
                                                                                -- ·ₚ (non0ₚ y) (non0ₚ (e₊ A ∷ₚ x)) ≡
      -- ·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x))
                                                                                (non0ₚ ((A · b) a ∷ₚ kmul b x b!=e) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x))))  ∎
                                                                                
... | no a!=e | yes b=e  | [ eqbe ] | commxy | commxby | commyax | commxey = begin (non0ₚ ((A · a) b ∷ₚ kmul a y a!=e) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)))) 
                                                                                  ≡⟨ cong₂ _+ₚ_ {non0ₚ ((A · a) b ∷ₚ kmul a y a!=e)}{non0ₚ ( (e₊ A) ∷ₚ kmul a y a!=e)}{x·ₚ (·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)))}{x·ₚ(x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))} 
                                                                                      (cong non0ₚ (cong₂ _∷ₚ_ ( b=e:ab=e {A} a b b=e ) refl)) (cong x·ₚ commxby) ⟩ 
                                                                                    ((non0ₚ ((e₊ A) ∷ₚ kmul a y a!=e) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))))) ≡⟨ refl ⟩
                                                                                     (x·ₚ(non0ₚ (kmul a y a!=e)) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))) ≡⟨ sym (split∷ₚ {A} ((non0ₚ (kmul a y a!=e))) ((x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))) ) ⟩
                                                                                     x·ₚ ((non0ₚ (kmul a y a!=e)) +ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))) 
                                                                                     ≡⟨ cong x·ₚ (cong₂ _+ₚ_ {non0ₚ (kmul a y a!=e)}{non0ₚ (kmul a y a!=e)}{x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))}{x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))} refl (cong x·ₚ (sym commxy))) ⟩
                                                                                     x·ₚ ((non0ₚ (kmul a y a!=e)) +ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))) ≡⟨ cong x·ₚ commyax ⟩
                                                                                 x·ₚ (·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x))) ∎

... | no x₁ | no x₂  | [ eqbe ] | commxy | commxby | commyax | commxey =  begin non0ₚ ((A · a) b ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y))) ≡⟨ cong₂ _+ₚ_ {non0ₚ ((A · a) b ∷ₚ kmul a y x₁)} {non0ₚ ((A · a) b ∷ₚ kmul a y x₁)} {x·ₚ (·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)))} {x·ₚ ((·ₖₒₙₛₜ b (non0ₚ x)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))} refl ((cong x·ₚ (reduction1 ))) ⟩
                              non0ₚ ((A · a) b ∷ₚ kmul a y x₁) +ₚ x·ₚ ((·ₖₒₙₛₜ b (non0ₚ x)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))) ≡⟨ split x y a b x₁ x₂ ⟩
                              ((non0ₚ (ld ((A · a) b) ((nzd A) x₁ x₂))) +ₚ (non0ₚ  ((e₊ A) ∷ₚ kmul a y x₁))) +ₚ ((x·ₚ (·ₖₒₙₛₜ b (non0ₚ x))) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))) ≡⟨ rearrange2 (non0ₚ (ld ((A · a) b) ((nzd A) x₁ x₂))) (non0ₚ  ((e₊ A) ∷ₚ kmul a y x₁)) (x·ₚ (·ₖₒₙₛₜ b (non0ₚ x))) (x·ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))) ⟩
                              ((non0ₚ (ld ((A · a) b) ((nzd A) x₁ x₂))) +ₚ (((non0ₚ  ((e₊ A) ∷ₚ kmul a y x₁)) +ₚ (x·ₚ (·ₖₒₙₛₜ b (non0ₚ x)))) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))))) ≡⟨ cong₂ _+ₚ_ {non0ₚ (ld ((A · a) b) (nzd A x₁ x₂))} {non0ₚ (ld ((A · b) a) (nzd A x₂ x₁))} {((non0ₚ (e₊ A ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₖₒₙₛₜ b (non0ₚ x))) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))))} {((x·ₚ (·ₖₒₙₛₜ a (non0ₚ y)) +ₚ non0ₚ (e₊ A ∷ₚ kmul b x x₂)) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))))} (cong non0ₚ (dcong₂ ld ((·-comm A) a b) refl)) final_comp ⟩
                              (non0ₚ (ld ((A · b) a) ((nzd A) x₂ x₁))) +ₚ (((x·ₚ (·ₖₒₙₛₜ a (non0ₚ y))) +ₚ (non0ₚ  ((e₊ A) ∷ₚ kmul b x x₂))) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))) ≡⟨ sym (rearrange1 (non0ₚ (ld ((A · b) a) ((nzd A) x₂ x₁))) (x·ₚ (·ₖₒₙₛₜ a (non0ₚ y))) (non0ₚ  ((e₊ A) ∷ₚ kmul b x x₂)) (x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))))) ⟩
                              ((non0ₚ (ld ((A · b) a) ((nzd A) x₂ x₁))) +ₚ (non0ₚ  ((e₊ A) ∷ₚ kmul b x x₂))) +ₚ ((x·ₚ (·ₖₒₙₛₜ a (non0ₚ y))) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))) ≡⟨ sym (split y x b a x₂ x₁) ⟩
                              (non0ₚ ((A · b) a ∷ₚ kmul b x x₂) +ₚ x·ₚ ((·ₖₒₙₛₜ a (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))) ≡⟨ cong₂ _+ₚ_ {non0ₚ ((A · b) a ∷ₚ kmul b x x₂)} {non0ₚ ((A · b) a ∷ₚ kmul b x x₂)} {x·ₚ ((·ₖₒₙₛₜ a (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))} {x·ₚ (·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x)))} refl (cong x·ₚ (sym (reduction2))) ⟩
                              non0ₚ ((A · b) a ∷ₚ kmul b x x₂) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x))) ∎
            where 
              kmul_konst : (u : NonZeroPoly A) → (i : M A) → (pi : ¬ (i ≡ (e₊ A))) → non0ₚ (kmul i u pi) ≡ (·ₖₒₙₛₜ i (non0ₚ u))
              kmul_konst u i pi with (dec A i (e₊ A)) | (inspect (dec A i) (e₊ A)) 
              ... | no x | [ eq ]  = cong non0ₚ refl
              ... | yes x | [ eq ] with pi x
              ... | ()

            

              reduction1 :  ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡ ((·ₖₒₙₛₜ b (non0ₚ x)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))) 
              reduction1 with (dec A) b (e₊ A) | (inspect ((dec A) b)) (e₊ A)
              ... | no pb | [ eq ] = begin ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡⟨ hlp ⟩ 
                                  ·ₚ (non0ₚ (b ∷ₚ y)) (non0ₚ x) ≡⟨ cong₂ _+ₚ_ {(·ₖₒₙₛₜ b (non0ₚ x))} {non0ₚ (kmul b x pb)} {x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))} {x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))} (sym (kmul_konst x b pb)) (cong x·ₚ (sym commxy )) ⟩
                                  (non0ₚ (kmul b x pb) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))∎
                                  where 
                                    hlp : ·ₚ (non0ₚ x) (non0ₚ (b ∷ₚ y)) ≡ ((·ₖₒₙₛₜ b (non0ₚ x)) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))
                                    hlp rewrite eq = commxby
              ... | yes pb | [ eq ]  with x₂ pb
              ... | ()

              reduction2 : ·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x)) ≡ (·ₖₒₙₛₜ a (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))
              reduction2 with (dec A) a (e₊ A) | (inspect ((dec A) a)) (e₊ A)
              ... | no pa | [ eq ] = begin ·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x)) ≡⟨ hlp ⟩ 
                                  ·ₚ (non0ₚ (a ∷ₚ x)) (non0ₚ y) ≡⟨ cong₂ _+ₚ_ {(·ₖₒₙₛₜ a (non0ₚ y))} {non0ₚ (kmul a y pa)} {x·ₚ (·ₚ (non0ₚ x) (non0ₚ y))} {x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))} (sym (kmul_konst y a pa)) (cong x·ₚ ( commxy )) ⟩
                                  (non0ₚ (kmul a y pa) +ₚ x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))∎
                                  where 
                                    hlp : ·ₚ (non0ₚ y) (non0ₚ (a ∷ₚ x)) ≡ ((·ₖₒₙₛₜ a (non0ₚ y)) +ₚ x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))
                                    hlp rewrite eq = sym commyax
              ... | yes pa | [ eq ]  with x₁ pa
              ... | ()

              split : (u : NonZeroPoly A) → (v : NonZeroPoly A) → (i : M A) → (j : M A) → (pi : ¬ (i ≡ (e₊ A))) → (pj : ¬ (j ≡ (e₊ A))) → (non0ₚ ((A · i) j ∷ₚ kmul i v pi) +ₚ x·ₚ ((·ₖₒₙₛₜ j (non0ₚ u)) +ₚ x·ₚ (·ₚ (non0ₚ u) (non0ₚ v)))) ≡ (non0ₚ ((A +ᵣ (A · i) j) (e₊ A) ∷ₚ kmul i v pi) +ₚ (x·ₚ (·ₖₒₙₛₜ j (non0ₚ u)) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ u) (non0ₚ v)))))
              split u v i j pi pj = cong₂ _+ₚ_ {non0ₚ ((A · i) j ∷ₚ kmul i v pi)} {non0ₚ ((A +ᵣ (A · i) j) (e₊ A) ∷ₚ kmul i v pi)} {x·ₚ ((·ₖₒₙₛₜ j (non0ₚ u)) +ₚ x·ₚ (·ₚ (non0ₚ u) (non0ₚ v)))} {x·ₚ (·ₖₒₙₛₜ j (non0ₚ u)) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ u) (non0ₚ v)))} 
                      (merge ((A · i) j) (kmul i v pi) ((nzd A) pi pj)) (split∷ₚ  (·ₖₒₙₛₜ j (non0ₚ u)) (x·ₚ (·ₚ (non0ₚ u) (non0ₚ v))))


              xmul_e₊ : (u : NonZeroPoly A) → non0ₚ ((e₊ A) ∷ₚ u) ≡ x·ₚ (non0ₚ u)
              xmul_e₊ u = refl

              midelement_switch1 : non0ₚ (e₊ A ∷ₚ kmul a y x₁) ≡ x·ₚ (·ₖₒₙₛₜ a (non0ₚ y))
              midelement_switch1 with (dec A) a (e₊ A)
              ... | no pa = refl
              ... | yes pa with x₁ pa
              ... | ()

              midelement_switch2 : x·ₚ (·ₖₒₙₛₜ b (non0ₚ x)) ≡ non0ₚ (e₊ A ∷ₚ kmul b x x₂)
              midelement_switch2 with (dec A) b (e₊ A)
              ... | no pb = refl
              ... | yes pb with x₂ pb
              ... | ()

              final_comp : ((non0ₚ (e₊ A ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₖₒₙₛₜ b (non0ₚ x))) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))) ≡ ((x·ₚ (·ₖₒₙₛₜ a (non0ₚ y)) +ₚ non0ₚ (e₊ A ∷ₚ kmul b x x₂)) +ₚ x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x))))
              final_comp = cong₂ _+ₚ_ {non0ₚ (e₊ A ∷ₚ kmul a y x₁) +ₚ x·ₚ (·ₖₒₙₛₜ b (non0ₚ x))} {x·ₚ (·ₖₒₙₛₜ a (non0ₚ y)) +ₚ non0ₚ (e₊ A ∷ₚ kmul b x x₂)} {x·ₚ (x·ₚ (·ₚ (non0ₚ x) (non0ₚ y)))} {x·ₚ (x·ₚ (·ₚ (non0ₚ y) (non0ₚ x)))}
               (cong₂ _+ₚ_ {non0ₚ (e₊ A ∷ₚ kmul a y x₁)} {x·ₚ (·ₖₒₙₛₜ a (non0ₚ y))} {x·ₚ (·ₖₒₙₛₜ b (non0ₚ x))} {non0ₚ (e₊ A ∷ₚ kmul b x x₂)} midelement_switch1 midelement_switch2) (cong x·ₚ (cong x·ₚ (·ₚ-commhlp x y)))



·ₚ-comm : {A : Ring} → (a : Poly A)→ (b : Poly A) → (·ₚ a b) ≡ (·ₚ b a)
·ₚ-comm 0ₚ 0ₚ = refl
·ₚ-comm 0ₚ (non0ₚ (ld a x)) = refl
·ₚ-comm 0ₚ (non0ₚ (x ∷ₚ tx)) = begin ·ₚ 0ₚ (non0ₚ (x ∷ₚ tx)) ≡⟨⟩ 0ₚ ≡⟨⟩ x·ₚ 0ₚ ≡⟨ cong x·ₚ (sym (0ₚ-multi (non0ₚ tx)) ) ⟩ x·ₚ (·ₚ (non0ₚ tx) 0ₚ) ∎
·ₚ-comm (non0ₚ (ld a x)) 0ₚ = refl
·ₚ-comm (non0ₚ (x ∷ₚ tx)) 0ₚ = sym (begin 0ₚ ≡⟨ refl ⟩ x·ₚ 0ₚ ≡⟨ cong x·ₚ (sym (0ₚ-multi (non0ₚ tx))) ⟩ x·ₚ (·ₚ (non0ₚ tx) 0ₚ) ∎ )
·ₚ-comm (non0ₚ x) (non0ₚ y) = ·ₚ-commhlp x y


--///////////////////////// DEGREE DEFINITION /////////////////////////
degreehlp : {A : Ring} → NonZeroPoly A → ℕ
degreehlp (ld a x) = 0
degreehlp (x ∷ₚ p) = 1 + degreehlp p

degree : {A : Ring} → Poly A → ℕ
degree 0ₚ = 0
degree (non0ₚ x) = degreehlp x

--///////////////////////// PROOFS FOR DEGREE /////////////////////////
-- addition of polynomials can only reduce degree
+-deg : {A : Ring} → (p q : Poly A ) →  degree q ≤ degree p  →  degree (p +ₚ q) ≤ degree p
+-deg {A} 0ₚ 0ₚ h = h
+-deg {A} 0ₚ (non0ₚ x) h = h
+-deg {A} (non0ₚ p) 0ₚ z≤n = {! ≤-refl ? ?   !}
+-deg {A} (non0ₚ p) (non0ₚ q) h = {!   !}

-- multiplication by constant doesn't change degree
kmul-deg : {A : Ring} → (a : M A) → (p : NonZeroPoly A) → (x : ¬ (a ≡ (e₊ A))) → degreehlp (kmul a p x) ≡ degreehlp p
kmul-deg {A} a (ld a₁ x₁) x = refl
kmul-deg {A} a (x₁ ∷ₚ p) x = cong suc (kmul-deg a p x)

·ₖₒₙₛₜ-degree : {A : Ring} → (a : M A) → (p : Poly A) → ¬ (a ≡ (e₊ A)) →  degree (·ₖₒₙₛₜ a p) ≡ (degree p)
·ₖₒₙₛₜ-degree {A} a 0ₚ x = refl
·ₖₒₙₛₜ-degree {A} a (non0ₚ h) pr with ((dec A) a (e₊ A) )
...                                 | yes x with (pr x)
...                                          | ()
·ₖₒₙₛₜ-degree {A} a (non0ₚ p) pr      | no x = kmul-deg a p pr

-- multiplication by x increases degree by 1  (NONZERO POLYNOMIALS)
x·ₚ-deg : {A : Ring} → (a : NonZeroPoly A) → degree (x·ₚ (non0ₚ a)) ≡ 1 + (degree (non0ₚ a)) 
x·ₚ-deg (ld a x) = refl
x·ₚ-deg (x ∷ₚ a) = cong suc refl

-- ·ₚ-degree : {A : Ring} → (p : NonZeroPoly A) → (q : NonZeroPoly A) → degree (·ₚ (non0ₚ p) (non0ₚ q)) ≡ (degree (non0ₚ p)) + (degree (non0ₚ q))
-- ·ₚ-degree {A} (ld a x) q = ·ₖₒₙₛₜ-degree a (non0ₚ q) x

-- ·ₚ-degree {A} (x ∷ₚ p) (ld ha pa) with dec A x (e₊ A)
-- ... | no t = {!   !}
-- ... | yes t = {!   !}
-- ·ₚ-degree {A} (hp ∷ₚ tp) (hq ∷ₚ tq) with dec A hp (e₊ A)
-- ... | yes x = {!   !}
-- ... | no x = {!   !}

-- dokaz, da mnozenje dveh nenicelnih stopnji sesteje

-- multiplication of two polynomials results in a polynomial with degree equal to the sum of degrees of starting polynomials
·ₚ-degree : {A : Ring} → (p : NonZeroPoly A) → (q : NonZeroPoly A) → degree (·ₚ (non0ₚ p) (non0ₚ q)) ≡ (degree (non0ₚ p)) + (degree (non0ₚ q))
·ₚ-degree {A} (ld a x) q = ·ₖₒₙₛₜ-degree a (non0ₚ q) x

·ₚ-degree {A} (x ∷ₚ p) (ld ha pa) = begin degree (·ₚ (non0ₚ (x ∷ₚ p)) (non0ₚ (ld ha pa))) 
                                  ≡⟨  {! ·ₚ-commhlp  (non0ₚ (x ∷ₚ p)) (non0ₚ (ld ha pa)) !} ⟩ degree (·ₚ (non0ₚ  (ld ha pa)) (non0ₚ (x ∷ₚ p))) 
                                  ≡⟨ {!   !} ⟩ {!   !} ∎ 
·ₚ-degree {A} (x ∷ₚ p) (x₁ ∷ₚ q) = {!   !}








-- 1ₚ≠0ₚ : {A : Ring } → ¬  (1ₚ  ≡ 0ₚ)
-- 1ₚ≠0ₚ  = {!   !} 

-- -ᵣ_ : M → M

-- -ᵣ-left  : (m : M) → (-ᵣ m) +ᵣ m ≡ e₊
-- nonzeroring
-- 1ᵣ≠e₊ :  ¬ (1ᵣ ≡ e₊)
-- ring laws
-- 1ᵣ-left  : (m : M) → 1ᵣ · m ≡ m
-- ·-assoc : (m₁ m₂ m₃ : M) → (m₁ · m₂) · m₃ ≡ m₁ · (m₂ · m₃)
-- ·-comm : (m₁ m₂ : M) → m₁ · m₂ ≡  m₂ · m₁

-- ω-left  : (m : M) → e₊ +ᵣ m ≡ m
-- +-assoc : (m₁ m₂ m₃ : M) → (m₁ +ᵣ m₂) +ᵣ m₃ ≡ m₁ +ᵣ (m₂ +ᵣ m₃)
-- +-comm : (m₁ m₂ : M) → m₁ +ᵣ m₂ ≡  m₂ +ᵣ m₁

-- dist-l : (m₁ m₂ m₃ : M) → m₃ · (m₁ +ᵣ m₂) ≡ (m₃ · m₁) +ᵣ (m₃ · m₂)

-- dec : (x y : M) → Dec(x ≡ y)
-- no zero divisors 
-- nzd : {x y : M}  → ¬ (x ≡ e₊) → ¬ (y ≡ e₊) → ¬ ((x · y) ≡ e₊)



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

-1ni0 : ¬ (oneN ≡ zeroN)
-1ni0 ()

ring2 : Ring
ring2 = record { M = Num
    ; 1ᵣ = oneN ;
    _·_  = _*m_  ;
    e₊ = zeroN;
    _+ᵣ_ = _+m_    ;
    -ᵣ_ = -rm_ ;
    -ᵣ-left = -rl ;
    1ᵣ-left  = -asl ;
    ·-assoc = -asoc ;
    ·-comm = -comm ;
    ω-left  = -wlm ;
    +-assoc = -a+m ;
    +-comm = -+cm ;
    dist-l = -dm ;
    dec = -decm ;
    nzd = -nzdm ;
    1ᵣ≠e₊ = -1ni0
                }

t1_p : Poly ring2
t1_p = 0ₚ
t1_q : Poly ring2
t1_q = 0ₚ
test1 : (t1_p +ₚ t1_q) ≡ 0ₚ
test1 = refl
--  testi za  +ₚ     
hlp : ¬ (oneN ≡ zeroN)
hlp ()


t2_p : Poly ring2
t2_p = non0ₚ (zeroN ∷ₚ (oneN ∷ₚ (oneN ∷ₚ (ld oneN   hlp ))))
t2_q : Poly ring2
t2_q = non0ₚ (zeroN ∷ₚ (zeroN ∷ₚ (oneN ∷ₚ (ld oneN hlp))))
test2 : (t2_p +ₚ t2_q) ≡ non0ₚ (zeroN ∷ₚ (ld oneN hlp))
test2 = refl

--  testi za  ·ₚ     
t4_p : Poly ring2
t4_p = non0ₚ (ld oneN  hlp )
t4_q : Poly ring2
t4_q = non0ₚ (ld oneN hlp )
test4 : (·ₚ t4_p  t4_q) ≡ t4_p
test4 = refl

t3_p : Poly ring2
t3_p = non0ₚ (zeroN ∷ₚ (oneN ∷ₚ (oneN ∷ₚ (ld oneN  hlp ))))
t3_q : Poly ring2
t3_q = non0ₚ (zeroN ∷ₚ (zeroN ∷ₚ (oneN ∷ₚ (ld oneN hlp ))))
test3 : (·ₚ t3_p  t3_q) ≡ non0ₚ (zeroN ∷ₚ(zeroN ∷ₚ(zeroN ∷ₚ(oneN ∷ₚ(zeroN ∷ₚ(zeroN ∷ₚ (ld oneN hlp)))))))
test3 = refl









