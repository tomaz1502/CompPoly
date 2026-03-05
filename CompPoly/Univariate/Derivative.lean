/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Derivative
import CompPoly.Univariate.ToPoly

/-!
  # Computable Derivative for Univariate Polynomials

  This file defines a computable `derivative` operation on `CPolynomial.Raw R` and
  `CPolynomial R`, and proves that it agrees with Mathlib's `Polynomial.derivative`
  when viewed via `toPoly`.

  ## Main Definitions

  * `CPolynomial.Raw.derivative`: Computable derivative on raw polynomials.
  * `CPolynomial.derivative`: Computable derivative on canonical polynomials.

  ## Main Results

  * `CPolynomial.Raw.derivative_toPoly`: `p.derivative.toPoly = Polynomial.derivative p.toPoly`
  * `CPolynomial.derivative_toPoly`: `p.derivative.toPoly = Polynomial.derivative p.toPoly`
-/

open Polynomial

namespace CompPoly

namespace CPolynomial

namespace Raw

variable {R : Type*} [CommRing R] [BEq R]

/-- Computable derivative of a raw polynomial.

  Given `p = #[a₀, a₁, a₂, ..., aₙ]` representing `a₀ + a₁X + a₂X² + ... + aₙXⁿ`,
  returns `#[a₁, 2·a₂, 3·a₃, ..., n·aₙ]` representing the formal derivative
  `a₁ + 2a₂X + 3a₃X² + ... + naₙXⁿ⁻¹`. -/
def derivative (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (p.extract 1 p.size).mapFinIdx (fun i a _ => (↑(i + 1) : R) * a)

omit [BEq R] in
/-- The size of the derivative is `p.size - 1`. -/
@[simp]
theorem size_derivative (p : CPolynomial.Raw R) :
    p.derivative.size = p.size - 1 := by
  simp [derivative]

omit [BEq R] in
/-- The `n`-th coefficient of the derivative is `(n + 1) * p.coeff (n + 1)`. -/
theorem coeff_derivative (p : CPolynomial.Raw R) (n : ℕ) :
    p.derivative.coeff n = (↑(n + 1) : R) * p.coeff (n + 1) := by
  simp only [coeff, derivative]
  rw [Array.getD_eq_getD_getElem?]
  by_cases hn : n < p.size - 1
  · rw [Array.getElem?_mapFinIdx]
    simp [hn, Array.getElem_extract]
    grind
  · rw [Array.getElem?_mapFinIdx]
    simp [hn]
    grind

omit [BEq R] in
/-- The computable derivative of a raw polynomial agrees with Mathlib's `Polynomial.derivative`
  when converted via `toPoly`. -/
theorem derivative_toPoly (p : CPolynomial.Raw R) :
    p.derivative.toPoly = Polynomial.derivative p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_derivative, Polynomial.coeff_derivative, coeff_toPoly]
  grind

end Raw

section Canonical

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- Computable derivative of a canonical polynomial. The result is trimmed to remain canonical. -/
def derivative (p : CPolynomial R) : CPolynomial R :=
  ⟨p.val.derivative.trim, Raw.Trim.trim_twice p.val.derivative⟩

/-- The computable derivative of a canonical polynomial agrees with Mathlib's
  `Polynomial.derivative` when converted via `toPoly`. -/
theorem derivative_toPoly (p : CPolynomial R) :
    p.derivative.toPoly = Polynomial.derivative p.toPoly := by
  simp only [derivative, toPoly, Raw.toPoly_trim]
  exact Raw.derivative_toPoly p.val

end Canonical

end CPolynomial

end CompPoly
