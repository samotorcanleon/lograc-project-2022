
module Ring where

  import Relation.Binary.PropositionalEquality as Eq
  open import Data.Empty   using (⊥)
  open Eq                  using (_≡_)

  ¬_ : Set → Set
  ¬ A = A → ⊥

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