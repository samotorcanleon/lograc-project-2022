open import Ring
import RingProperties

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_) renaming (_+_ to _+ⁿ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

module Polynomials (A : Ring) where

  open Ring.Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ; _+_ to _+ᵣ_; _·_ to _·ᵣ_; -_ to -ᵣ_ ;
                            𝟙≠𝟘 to 𝟙ᵣ≠𝟘ᵣ; 𝟙-left to 𝟙ᵣ-left; ·-comm to ·ᵣ-comm)
  open RingProperties {A}

  data NonZeroPoly : Set where
    ld : (a : M)  → ¬ (a ≡ 𝟘ᵣ) →  NonZeroPoly
    _∷ₚ_ : M  → NonZeroPoly -> NonZeroPoly

  data Poly : Set where
    𝟘ₚ : Poly
    non𝟘ₚ : NonZeroPoly → Poly



-- ////////////  ADDITION ////////////
  addp : (p q : NonZeroPoly ) → Maybe NonZeroPoly 
  addp (ld a a≠0) (ld b b≠0) with (dec (a +ᵣ b) 𝟘ᵣ)
  ...     | yes _ = nothing  --vsota je 𝟘
  ...     | no a+b≠0 = just (ld (a +ᵣ b) a+b≠0)
  addp (ld a a≠0) (hb ∷ₚ tb) = just ((a +ᵣ hb) ∷ₚ tb)
  addp (ha ∷ₚ ta) (ld b b≠0) = addp (ld b b≠0) (ha ∷ₚ ta)
  addp (ha ∷ₚ ta) (hb ∷ₚ tb) with (addp ta tb)
  ...     | just ta+tb≠0 = just ((ha +ᵣ hb) ∷ₚ ta+tb≠0)
  ...     | nothing with (dec (ha +ᵣ hb) (𝟘ᵣ))
  ...               | yes _ = nothing
  ...               | no ha+hb≠0 = just (ld (ha +ᵣ hb) ha+hb≠0)

  _+ₚ_ : (p q : Poly) → Poly 
  𝟘ₚ +ₚ q = q
  non𝟘ₚ p +ₚ 𝟘ₚ = non𝟘ₚ p
  non𝟘ₚ p +ₚ non𝟘ₚ q with (addp p q)
  ... | just p+q = non𝟘ₚ p+q
  ... | nothing = 𝟘ₚ

-- ////////////  INVERSE for addition ////////////
  -ₚh : NonZeroPoly → NonZeroPoly
  -ₚh  (ld a a≠0) = ld (-ᵣ a)  (n0→n0 a a≠0)
  -ₚh  (x ∷ₚ p) = (-ᵣ x) ∷ₚ (-ₚh p)

  -ₚ : Poly → Poly 
  -ₚ  𝟘ₚ = 𝟘ₚ
  -ₚ  (non𝟘ₚ p) = non𝟘ₚ (-ₚh p)

-- ////////////  MULTIPLICATION ////////////
  kmul : (x : M) → NonZeroPoly → ¬ (x ≡ 𝟘ᵣ) → NonZeroPoly
  kmul x (ha ∷ₚ ta) x≠0 = (x ·ᵣ ha) ∷ₚ (kmul x ta x≠0)
  kmul x (ld a a≠0) x≠0 = ld (x ·ᵣ a) (nzd x≠0 a≠0)

  ·ₖₒₙₛₜ : (x : M) → Poly -> Poly
  ·ₖₒₙₛₜ _ 𝟘ₚ = 𝟘ₚ
  ·ₖₒₙₛₜ x (non𝟘ₚ p) with dec x 𝟘ᵣ
  ... | yes x=0 = 𝟘ₚ
  ... | no x≠0 = non𝟘ₚ (kmul x p  x≠0)

  x·ₚ : Poly → Poly
  x·ₚ 𝟘ₚ = 𝟘ₚ
  x·ₚ (non𝟘ₚ p) = non𝟘ₚ (𝟘ᵣ ∷ₚ p)

  ·ₚ : (p q : Poly) → Poly
  ·ₚ 𝟘ₚ _ = 𝟘ₚ
  ·ₚ (non𝟘ₚ (ld ha _))  q = ·ₖₒₙₛₜ ha q
  ·ₚ (non𝟘ₚ (ha ∷ₚ ta))  q = ·ₖₒₙₛₜ ha q +ₚ x·ₚ (·ₚ (non𝟘ₚ ta) q)


  -- ////////////  CONSTANT AND ZERO POLYNOMIALS ////////////
  1ₚ : Poly
  1ₚ = non𝟘ₚ (ld 𝟙ᵣ 𝟙ᵣ≠𝟘ᵣ)

  0ₚ : Poly
  0ₚ = 𝟘ₚ

  -- ////////////  DEGREE ////////////
  degreehlp : NonZeroPoly → ℕ
  degreehlp (ld _ _) = 0
  degreehlp (_ ∷ₚ ta) = 1 +ⁿ degreehlp ta

  degree : Poly → ℕ
  degree 𝟘ₚ = 0
  degree (non𝟘ₚ x) = degreehlp x