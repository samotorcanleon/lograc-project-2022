open import Ring

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans;cong;cong₂)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)


module RingProperties {A : Ring}  where

  open Ring.Ring A

  contraposition : ∀ {A B : Set}
    → (A → B)
      -----------
    → (¬ B → ¬ A)
  contraposition f ¬y x = ¬y (f x)

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
                                                  ≡⟨ sym (hlp x a) ⟩
                                - x + ( x + a) 
                                                  ≡⟨ cong₂  (_+_ ) refl (a+x=b+x→x+a=x+b x a b h) ⟩
                                - x + ( x + b) 
                                                  ≡⟨ hlp x b ⟩
                                b ∎
    where 
      hlp : (x a : M ) → - x + (x + a) ≡  a
      hlp x a =  begin - x + (x + a)   
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
  n0→n0 a = contraposition (hlp a)
    where 
      hlp :  (a : M) → (- a ≡ 𝟘) → (a ≡ 𝟘) 
      hlp  a p = trans (sym (trans (a=b→a+x=b+x a (- a) 𝟘 p) ((ω-left ) a))) ((-left ) a)