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

  open Ring.Ring A renaming (𝟘 to 𝟘ᵣ; 𝟙 to 𝟙ᵣ; _+_ to _+ᵣ_; _·_ to _·ᵣ_; -_ to -ᵣ_ ;𝟙≠𝟘 to 𝟙ᵣ≠𝟘ᵣ; 𝟙-left to 𝟙ᵣ-left; ·-comm to ·ᵣ-comm)
  open RingProperties {A}

  data NonZeroPoly : Set where
    ld : (a : M)  → ¬ (a ≡ 𝟘ᵣ) →  NonZeroPoly
    _∷ₚ_ : M  → NonZeroPoly -> NonZeroPoly

  data Poly : Set where
    𝟘ₚ : Poly
    non𝟘ₚ : NonZeroPoly → Poly



-- ////////////  ADDITION ////////////
  addp : (x y : NonZeroPoly ) → Maybe (NonZeroPoly )
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

  _+ₚ_ : (a : Poly ) → (b : Poly) → Poly 
  𝟘ₚ +ₚ b = b
  non𝟘ₚ x +ₚ 𝟘ₚ = non𝟘ₚ x
  non𝟘ₚ x +ₚ non𝟘ₚ y with (addp x y)
  ... | just res = non𝟘ₚ res
  ... | nothing = 𝟘ₚ

-- ////////////  INVERSE ////////////
  -ₚh :  (p : NonZeroPoly) → NonZeroPoly
  -ₚh  (ld a x) = ld (-ᵣ a)  (n0→n0  a x)
  -ₚh  (x ∷ₚ p) = (-ᵣ x) ∷ₚ (-ₚh p)

  -ₚ :  (p : Poly) → Poly 
  -ₚ  𝟘ₚ = 𝟘ₚ
  -ₚ  (non𝟘ₚ p) = non𝟘ₚ (-ₚh p)

-- ////////////  MULTIPLICATION ////////////
  kmul : (a : M) → (x : NonZeroPoly) → ¬ (a ≡ 𝟘ᵣ) → (NonZeroPoly)
  kmul a (hx ∷ₚ tx) pa = (a ·ᵣ hx) ∷ₚ (kmul a tx pa)
  kmul a (ld hx p) pa = ld (a ·ᵣ hx) (nzd pa p)

  ·ₖₒₙₛₜ : (a : M) → (p : Poly) -> Poly
  ·ₖₒₙₛₜ a 𝟘ₚ = 𝟘ₚ
  ·ₖₒₙₛₜ a (non𝟘ₚ x) with dec a 𝟘ᵣ
  ... | yes x₁ = 𝟘ₚ
  ... | no p¬𝟘 = non𝟘ₚ (kmul a x p¬𝟘)

  x·ₚ : (a : Poly) → Poly
  x·ₚ 𝟘ₚ = 𝟘ₚ
  x·ₚ (non𝟘ₚ x) = non𝟘ₚ (𝟘ᵣ ∷ₚ x)

  ·ₚ : (a : Poly) → (b : Poly) → Poly
  ·ₚ 𝟘ₚ b = 𝟘ₚ
  ·ₚ (non𝟘ₚ (ld hx p))  b = ·ₖₒₙₛₜ hx b
  ·ₚ (non𝟘ₚ (hx ∷ₚ tx))  b = ·ₖₒₙₛₜ hx b +ₚ x·ₚ (·ₚ (non𝟘ₚ tx)  b)


  -- ////////////  CONSTANT AND ZERO POLYNOMIALS ////////////
  1ₚ : Poly
  1ₚ = non𝟘ₚ (ld 𝟙ᵣ 𝟙ᵣ≠𝟘ᵣ)

  0ₚ : Poly
  0ₚ = 𝟘ₚ

  -- ////////////  DEGREE ////////////
  degreehlp : NonZeroPoly → ℕ
  degreehlp (ld a x) = 0
  degreehlp (x ∷ₚ p) = 1 +ⁿ degreehlp p

  degree : Poly → ℕ
  degree 𝟘ₚ = 0
  degree (non𝟘ₚ x) = degreehlp x