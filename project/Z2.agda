import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;refl)
open import Ring


module Z2 where
  
  data Num : Set where
    zero : Num
    one : Num

  _+m_ : (a : Num) → (b : Num) → Num
  zero +m b = b
  one +m zero = one
  one +m one = zero
  _*m_ : (a : Num) → (b : Num) → Num
  zero *m b = zero
  one *m b = b

  -rm_ : (a : Num)  → Num
  -rm zero = zero
  -rm one = one

  -rml : (m : Num) → (-rm m) +m m ≡ zero
  -rml zero = refl
  -rml one = refl
  -rl  : (m : Num) → (-rm m) +m m ≡ zero
  -rl zero = refl
  -rl one = refl

  -asl : (m : Num) → one *m m ≡ m
  -asl zero = refl
  -asl one = refl
  -asoc : (m₁ m₂ m₃ : Num) → (m₁ *m m₂) *m m₃ ≡ m₁ *m (m₂ *m m₃)
  -asoc zero b c = refl
  -asoc one b c = refl
  -comm : (m₁ m₂ : Num) → m₁ *m m₂ ≡  m₂ *m m₁
  -comm zero zero = refl
  -comm zero one = refl
  -comm one zero = refl
  -comm one one = refl
  -wlm : (m : Num) → zero +m m ≡ m
  -wlm a = refl
  -a+m : (m₁ m₂ m₃ : Num) → (m₁ +m m₂) +m m₃ ≡ m₁ +m (m₂ +m m₃)
  -a+m zero b c = refl
  -a+m one zero c = refl
  -a+m one one zero = refl
  -a+m one one one = refl
  -+cm : (m₁ m₂ : Num) → m₁ +m m₂ ≡  m₂ +m m₁
  -+cm zero zero = refl
  -+cm zero one = refl
  -+cm one zero = refl
  -+cm one one = refl
  -dm : (m₁ m₂ m₃ : Num) → m₃ *m (m₁ +m m₂) ≡ (m₃ *m m₁) +m (m₃ *m m₂)
  -dm a b zero = refl
  -dm a b one = refl
  -decm : (x y : Num) → Dec(x ≡ y)
  -decm zero zero = yes refl
  -decm zero one = no λ ()
  -decm one zero = no λ ()
  -decm one one = yes refl
  -nzdm : {x y : Num}  → ¬ (x ≡ zero) → ¬ (y ≡ zero) → ¬ ((x *m y) ≡ zero)
  -nzdm {zero} {zero} a b = b
  -nzdm {zero} {one} a b = a
  -nzdm {one} {y} a b = b

  -1ni𝟘 : ¬ (one ≡ zero)
  -1ni𝟘 ()

  ring2 : Ring
  ring2 = record { M = Num
      ; 𝟙 = one ;
      _·_  = _*m_  ;
      𝟘 = zero;
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

-- ////////////////    TESTS 	////////////////
  open import Polynomials (ring2)

  t1_p : Poly 
  t1_p = 𝟘ₚ
  t1_q : Poly
  t1_q = 𝟘ₚ
  test1 : (t1_p +ₚ t1_q) ≡ 𝟘ₚ
  test1 = refl
  --  testi za  +ₚ
  hlp : ¬ (one ≡ zero)
  hlp ()

  t2_p : Poly
  t2_p = non𝟘ₚ (zero ∷ₚ (one ∷ₚ (one ∷ₚ (ld one   hlp ))))
  t2_q : Poly
  t2_q = non𝟘ₚ (zero ∷ₚ (zero ∷ₚ (one ∷ₚ (ld one hlp))))
  test2 : (t2_p +ₚ t2_q) ≡ non𝟘ₚ (zero ∷ₚ (ld one hlp))
  test2 = refl

  --  testi za  ·ₚ
  t4_p : Poly
  t4_p = non𝟘ₚ (ld one  hlp )
  t4_q : Poly
  t4_q = non𝟘ₚ (ld one hlp )
  test4 : (·ₚ t4_p  t4_q) ≡ t4_p
  test4 = refl

  t3_p : Poly
  t3_p = non𝟘ₚ (zero ∷ₚ (one ∷ₚ (one ∷ₚ (ld one  hlp ))))
  t3_q : Poly
  t3_q = non𝟘ₚ (zero ∷ₚ (zero ∷ₚ (one ∷ₚ (ld one hlp ))))
  test3 : (·ₚ t3_p  t3_q) ≡ non𝟘ₚ (zero ∷ₚ(zero ∷ₚ(zero ∷ₚ(one ∷ₚ(zero ∷ₚ(zero ∷ₚ (ld one hlp)))))))
  test3 = refl