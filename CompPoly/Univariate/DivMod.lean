/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.CategoryTheory.Category.Basic
import CompPoly.Univariate.ToPoly

open Polynomial CompPoly CompPoly.CPolynomial CompPoly.CPolynomial.Raw

section Operations

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

namespace CompPoly.CPolynomial.Raw

omit [BEq R] [LawfulBEq R] in
lemma toPoly_neg (p : CPolynomial.Raw R) :
    (-p).toPoly = -p.toPoly := by
  ext n
  simp only [coeff_toPoly, Polynomial.coeff_neg]
  exact neg_coeff p n

lemma toPoly_sub_raw (p q : CPolynomial.Raw R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  have h_sub : (p - q).toPoly = p.toPoly + (-q).toPoly := by
    have h_add : (p + (-q)).toPoly = p.toPoly + (-q).toPoly := by
      grind
    convert h_add using 1
  rw [ h_sub, toPoly_neg, sub_eq_add_neg ]

lemma toPoly_mul_raw (p q : CPolynomial.Raw R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  convert Raw.toPoly_mul_coeff p q using 1
  simp [ Polynomial.ext_iff, Polynomial.coeff_mul ]

lemma toPoly_pow_raw (p : CPolynomial.Raw R) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := by
  induction' n with n ih generalizing p <;> simp_all [ pow_succ ]
  · convert Raw.toPoly_one <;> infer_instance
  · rw [ pow_succ', toPoly_mul_raw, ih ]

lemma trim_size_zero_iff_toPoly_zero (p : CPolynomial.Raw R) :
    p.trim.size = 0 ↔ p.toPoly = 0 := by
  constructor <;> intro h
  · rw [ ← Raw.toPoly_trim ] ; aesop
  · have h_trim_zero : p.trim = 0 := by
      convert Raw.toImpl_toPoly p
      · convert Raw.toImpl_toPoly p |> Eq.symm
      · convert Raw.toImpl_toPoly p
        unfold Raw.toPoly at *; aesop
    aesop

lemma trim_size_pos_iff_toPoly_ne_zero (p : CPolynomial.Raw R) :
    0 < p.trim.size ↔ p.toPoly ≠ 0 := by
  constructor <;> intro h
  · contrapose! h
    convert trim_size_zero_iff_toPoly_zero p |>.2 h |> le_of_eq
  · contrapose! h
    convert trim_size_zero_iff_toPoly_zero p |>.1 ( le_antisymm h ( Nat.zero_le _ ) ) using 1

lemma trim_size_eq_natDegree_succ (p : CPolynomial.Raw R) (hp : p.toPoly ≠ 0) :
    p.trim.size = p.toPoly.natDegree + 1 := by
  obtain ⟨q, hq⟩ : ∃ q : Polynomial R, p.toPoly = q ∧ q ≠ 0 := by
    use p.toPoly
  have h_trim_size_eq : p.toPoly.toImpl = p.trim := by
    exact toImpl_toPoly p
  rw [ ← h_trim_size_eq, hq.1 ]
  unfold Polynomial.toImpl
  cases h : q.degree <;> simp_all [ Polynomial.natDegree ]

lemma leadingCoeff_eq_toPoly_leadingCoeff (p : CPolynomial.Raw R) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  by_contra h_neq
  set q : Polynomial R := p.toPoly
  have hq : p.leadingCoeff = q.leadingCoeff := by
    by_cases hq : q = 0
    · convert trim_size_zero_iff_toPoly_zero p |>.2 hq |> fun h => ?_
      unfold CPolynomial.Raw.leadingCoeff
      unfold Array.getLastD; aesop
    · have hq_deg : q.natDegree + 1 = p.trim.size := by
        convert trim_size_eq_natDegree_succ p hq
        · exact Eq.symm (trim_size_eq_natDegree_succ p hq)
        · convert trim_size_eq_natDegree_succ p hq
      have hq_coeff : q.coeff (q.natDegree) = p.trim.coeff (q.natDegree) := by
        rw [ ← CPolynomial.Raw.coeff_toPoly ]
        rw [ Raw.toPoly_trim ]
      simp_all [ leadingCoeff ]
      convert h_neq ?_
      simp [ Array.getLastD, hq_deg.symm ]
  contradiction

lemma natDegree_eq_toPoly_natDegree (p : CPolynomial.Raw R) (hp : p.toPoly ≠ 0) :
    p.natDegree = p.toPoly.natDegree := by
  have h_def : p.natDegree = p.trim.size - 1 := by
    rw [ Raw.natDegree, Raw.trim ]
    cases h : p.lastNonzero <;> simp
  have h_toPoly_def : (p.toPoly).natDegree = p.trim.size - 1 := by
    have := trim_size_eq_natDegree_succ p hp
    rw [ this, Nat.add_sub_cancel ]
  rw [h_def, h_toPoly_def]

lemma monic_iff_toPoly_monic (q : CPolynomial.Raw R) :
    q.monic = true ↔ q.toPoly.Monic := by
  have h_leading_coeff : q.leadingCoeff = q.toPoly.leadingCoeff := leadingCoeff_eq_toPoly_leadingCoeff q
  unfold CPolynomial.Raw.monic
  simp_all only [beq_iff_eq]
  rfl

lemma toPoly_C_mul_X_pow (lc : R) (n : ℕ) :
    (C lc * X ^ n : CPolynomial.Raw R).toPoly =
    Polynomial.C lc * Polynomial.X ^ n := by
  have h_C : (C lc : CPolynomial.Raw R).toPoly = Polynomial.C lc := toPoly_C lc
  have h_X_pow : (X ^ n : CPolynomial.Raw R).toPoly = Polynomial.X ^ n := by
    have h_X_pow : (X ^ n : CPolynomial.Raw R).toPoly = (X : CPolynomial.Raw R).toPoly ^ n := toPoly_pow_raw X n
    rw [ h_X_pow, Raw.toPoly_X ]
  rw [toPoly_mul_raw (C lc) (X ^ n), h_C, h_X_pow]

lemma toPoly_div_step (p q : CPolynomial.Raw R) :
    (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))).toPoly =
    p.toPoly - q.toPoly * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree)) := by
  convert toPoly_sub_raw p ( q * ( C p.leadingCoeff * X ^ ( p.natDegree - q.natDegree ) ) ) using 1
  have h_poly_mul : ∀ (p q : CPolynomial.Raw R), (p * q).toPoly = p.toPoly * q.toPoly := by
    exact fun p q => toPoly_mul_raw p q
  convert rfl using 2
  convert h_poly_mul q ( C p.leadingCoeff * X ^ ( p.natDegree - q.natDegree ) ) using 1
  congr! 1
  convert Raw.toPoly_C_mul_X_pow p.leadingCoeff ( p.natDegree - q.natDegree ) |> Eq.symm using 1

lemma div_step_degree_lt (p q : CPolynomial.Raw R)
    (hp : p.toPoly ≠ 0) (hq : q.toPoly.Monic)
    (hdeg : Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly) :
    (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))).toPoly.degree <
      p.toPoly.degree := by
  norm_num at *
  have := @Polynomial.div_wf_lemma R
  convert this ⟨ hdeg, hp ⟩ hq using 1
  rw [ ← leadingCoeff_eq_toPoly_leadingCoeff, ← natDegree_eq_toPoly_natDegree ]
  · convert congr_arg Polynomial.degree ( toPoly_div_step p q ) using 1
    rw [ show q.toPoly.natDegree = q.natDegree from ?_ ]
    by_cases hq_zero : q.toPoly = 0
    · simp_all [ Polynomial.Monic.def ]
      cases subsingleton_or_nontrivial R <;> simp_all [ eq_iff_true_of_subsingleton ]
    · rw [ ← natDegree_eq_toPoly_natDegree ]
      exact hq_zero
  · exact hp

lemma trim_size_lt_of_degree_lt (r p : CPolynomial.Raw R)
    (hp : p.toPoly ≠ 0)
    (hdeg : r.toPoly.degree < p.toPoly.degree) :
    r.trim.size < p.trim.size := by
  by_cases hr : r.toPoly = 0
  · have := trim_size_zero_iff_toPoly_zero r
    exact this.mpr hr ▸ trim_size_pos_iff_toPoly_ne_zero p |>.2 hp
  · rw [ trim_size_eq_natDegree_succ, trim_size_eq_natDegree_succ ]
    · exact Nat.succ_lt_succ ( Polynomial.natDegree_lt_natDegree hr hdeg )
    · exact hp
    · exact hr

lemma degree_le_of_trim_size_le (p q : CPolynomial.Raw R)
    (h1 : q.trim.size ≤ p.trim.size) (h2 : 0 < p.trim.size) :
    Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly := by
  by_cases hp : p.toPoly = 0 <;> by_cases hq : q.toPoly = 0 <;> simp_all [ Polynomial.degree_eq_natDegree ]
  · have hp_zero : p.trim.size = 0 := (trim_size_zero_iff_toPoly_zero p).mpr hp
    linarith
  · have h_deg : q.trim.size = q.toPoly.natDegree + 1 ∧ p.trim.size = p.toPoly.natDegree + 1 := by
      exact ⟨ trim_size_eq_natDegree_succ q hq, trim_size_eq_natDegree_succ p hp ⟩
    linarith

lemma divByMonic_wf_termination (p q : CPolynomial.Raw R)
    (hq : q.monic = true) (h1 : q.trim.size ≤ p.trim.size) (h2 : 0 < p.trim.size) :
    (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))).trim.size <
      p.trim.size := by
  have hp : p.toPoly ≠ 0 := (trim_size_pos_iff_toPoly_ne_zero p).mp h2
  have hq_monic : q.toPoly.Monic := (monic_iff_toPoly_monic q).mp hq
  have hdeg : Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly :=
    degree_le_of_trim_size_le p q h1 h2
  exact trim_size_lt_of_degree_lt _ p hp (div_step_degree_lt p q hp hq_monic hdeg)

def divModByMonicAux (p q : CPolynomial.Raw R) : CPolynomial.Raw R × CPolynomial.Raw R :=
  if hq : q.monic = true then
    go p q hq
  else ⟨0, 0⟩
where
  go (p q : CPolynomial.Raw R) (hq : q.monic = true) : CPolynomial.Raw R × CPolynomial.Raw R :=
    if h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size then
      let z := C p.leadingCoeff * X ^ (p.natDegree - q.natDegree)
      have _wf : (p - q * z).trim.size < p.trim.size :=
        divByMonic_wf_termination p q hq h.1 h.2
      let ⟨e, r⟩ := go (p - q * z) q hq 
      ⟨z + e, r⟩
    else ⟨0, p⟩
  termination_by p.trim.size

def divByMonic (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (divModByMonicAux p q).1

def modByMonic (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (divModByMonicAux p q).2

def div [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

def mod [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (CPolynomial.Raw R) := ⟨div⟩
instance [Field R] : Mod (CPolynomial.Raw R) := ⟨mod⟩

end CompPoly.CPolynomial.Raw

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def CPolynomial.divByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, by simpa using Trim.trim_twice (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def CPolynomial.modByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, by simpa using Trim.trim_twice (Raw.modByMonic p.val q.val)⟩

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div [Field R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.div p.val q.val).trim, by simpa using Trim.trim_twice (Raw.div p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod [Field R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.mod p.val q.val).trim, by simpa using Trim.trim_twice (Raw.mod p.val q.val)⟩

instance [Field R] : Div (CPolynomial R) := ⟨div⟩
instance [Field R] : Mod (CPolynomial R) := ⟨mod⟩

end Operations

section ImplementationCorrectness

namespace CompPoly.CPolynomial.Raw

section DivModByMonic

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

lemma divModByMonicAux_go_unfold_1 (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (divModByMonicAux.go p q hq).1 =
    if q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size then
      C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) +
      (divModByMonicAux.go (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))) q hq).1
    else 0 := by
  rw [ divModByMonicAux.go ]
  split_ifs <;> aesop

lemma divModByMonicAux_go_unfold_2 (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (divModByMonicAux.go p q hq).2 =
    if q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size then
      (divModByMonicAux.go (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))) q hq).2
    else p := by
  rw [ divModByMonicAux.go ]
  split_ifs <;> aesop

lemma size_cond_iff_degree_cond (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic) :
    (q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size) ↔
    (Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly ∧ p.toPoly ≠ 0) := by
  by_cases hp : p.toPoly ≠ 0 <;> by_cases hq : q.toPoly ≠ 0 <;> simp_all [ trim_size_pos_iff_toPoly_ne_zero ]
  · constructor <;> intro h
    · rw [ Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq ] ; norm_cast ; linarith [ trim_size_eq_natDegree_succ p hp, trim_size_eq_natDegree_succ q hq ] 
    · rw [ trim_size_eq_natDegree_succ q hq, trim_size_eq_natDegree_succ p hp ]
      exact Nat.succ_le_succ ( Polynomial.natDegree_le_natDegree h )
  · cases subsingleton_or_nontrivial R <;> simp_all [ eq_iff_true_of_subsingleton ]

lemma z_toPoly_eq (p q : CPolynomial.Raw R) (hp : p.toPoly ≠ 0) :
    (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) : CPolynomial.Raw R).toPoly =
    Polynomial.C p.toPoly.leadingCoeff * Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree) := by
  have h_deg : p.natDegree = p.toPoly.natDegree ∧ q.natDegree = q.toPoly.natDegree := by
    constructor <;> by_cases hq : q.toPoly = 0 <;> simp_all [ CPolynomial.Raw.natDegree_eq_toPoly_natDegree ]
    rw [ CPolynomial.Raw.natDegree ]
    cases h : q.lastNonzero <;> simp_all [ CPolynomial.Raw.toPoly ]
    have h_deg : q.toPoly = 0 := by
      convert hq using 1
    generalize_proofs at *
    have h_deg : q.trim.size = 0 := by
      exact (trim_size_zero_iff_toPoly_zero q).mpr hq
    generalize_proofs at *
    cases h' : q.trim ; simp_all [ CPolynomial.Raw.trim ]
  convert toPoly_C_mul_X_pow p.leadingCoeff ( p.natDegree - q.natDegree ) using 1
  rw [ h_deg.1, h_deg.2, leadingCoeff_eq_toPoly_leadingCoeff ]

lemma divByMonic_eq_zero_of_not_cond_1 (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : ¬(q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size)) :
    p.toPoly /ₘ q.toPoly = 0 := by
  simp_all [ Polynomial.divByMonic ]
  rw [ Polynomial.divModByMonicAux ]
  have := size_cond_iff_degree_cond p q hq
  aesop

lemma divByMonic_eq_p_of_not_cond_2 (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : ¬(q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size)) :
    p.toPoly %ₘ q.toPoly = p.toPoly := by
  simp_all [ Polynomial.modByMonic ]
  rw [ Polynomial.divModByMonicAux ]
  have := size_cond_iff_degree_cond p q hq
  aesop

lemma divByMonic_unfold_step_1 (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size) :
    p.toPoly /ₘ q.toPoly =
    Polynomial.C p.toPoly.leadingCoeff * Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree) +
    (p.toPoly - q.toPoly * (Polynomial.C p.toPoly.leadingCoeff *
      Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree))) /ₘ q.toPoly := by
  have h_eq : ∀ (p q : Polynomial R), q.Monic → q ≠ 0 → p.degree ≥ q.degree → p /ₘ q = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree) + (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))) /ₘ q := by
    intros p q hq hq' hpq
    rw [ Polynomial.divByMonic ]
    unfold Polynomial.divModByMonicAux
    split_ifs <;> simp_all [ Polynomial.divByMonic ]
  by_cases hq_zero : q.toPoly = 0
  · cases subsingleton_or_nontrivial R <;> aesop_cat
  · have := size_cond_iff_degree_cond p q hq; aesop

lemma divByMonic_unfold_step_2 (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size) :
    p.toPoly %ₘ q.toPoly =
    (p.toPoly - q.toPoly * (Polynomial.C p.toPoly.leadingCoeff *
      Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree))) %ₘ q.toPoly := by
  have h_eq : ∀ (p q : Polynomial R), q.Monic → q ≠ 0 → p.degree ≥ q.degree →
      p %ₘ q = (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))) %ₘ q := by
    intros p q hq hq' hpq
    rw [ Polynomial.modByMonic ]
    unfold Polynomial.divModByMonicAux
    split_ifs <;> simp_all [ Polynomial.modByMonic ]
  by_cases hq_zero : q.toPoly = 0
  · cases subsingleton_or_nontrivial R <;> aesop_cat
  · have := size_cond_iff_degree_cond p q hq
    aesop

lemma divModByMonicAux_go_toPoly_1 (p q : CPolynomial.Raw R)
    (hq : q.monic = true) :
    (divModByMonicAux.go p q hq).1.toPoly = p.toPoly /ₘ q.toPoly := by
  induction' n : p.trim.size using Nat.strong_induction_on with n ih generalizing p q hq
  by_cases h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size
  · rw [ divModByMonicAux_go_unfold_1 ]
    rw [ if_pos h, divByMonic_unfold_step_1 p q ((monic_iff_toPoly_monic q).mp hq) h ]
    rw [ toPoly_add ]
    rw [ ih _ _ _ _ hq rfl ]
    · rw [ z_toPoly_eq p q ]
      · rw [ toPoly_sub_raw, toPoly_mul_raw ]
        rw [ z_toPoly_eq p q ]
        have := trim_size_zero_iff_toPoly_zero p; aesop
      · have := trim_size_zero_iff_toPoly_zero p; aesop
    · exact n ▸ divByMonic_wf_termination p q hq h.1 h.2
  · have h_div_zero : p.toPoly /ₘ q.toPoly = 0 := by
      apply divByMonic_eq_zero_of_not_cond_1 p q ((monic_iff_toPoly_monic q).mp hq) h
    unfold divModByMonicAux.go; aesop

lemma divModByMonicAux_go_toPoly_2 (p q : CPolynomial.Raw R) (hq : q.monic = true)  :
    (divModByMonicAux.go p q hq).2.toPoly = p.toPoly %ₘ q.toPoly := by
  induction' n : p.trim.size using Nat.strong_induction_on with n ih generalizing p q hq
  by_cases h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size
  · rw [ divModByMonicAux_go_unfold_2 ]
    rw [ if_pos h, divByMonic_unfold_step_2 p q ((monic_iff_toPoly_monic q).mp hq) h ]
    rw [ ih _ _ _ _ hq rfl ]
    · rw [ toPoly_sub_raw, toPoly_mul_raw, z_toPoly_eq p q ]
      have := trim_size_zero_iff_toPoly_zero p; aesop
    · exact n ▸ divByMonic_wf_termination p q hq h.1 h.2
  · have h_div_zero : p.toPoly %ₘ q.toPoly = p.toPoly :=
      divByMonic_eq_p_of_not_cond_2 p q ((monic_iff_toPoly_monic q).mp hq) h
    unfold divModByMonicAux.go; aesop

theorem divByMonic_toPoly (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (divByMonic p q).toPoly = Polynomial.divByMonic p.toPoly q.toPoly := by
  unfold divByMonic divModByMonicAux
  rw [dif_pos hq]
  exact divModByMonicAux_go_toPoly_1 p q hq

theorem modByMonic_toPoly (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (modByMonic p q).toPoly = Polynomial.modByMonic p.toPoly q.toPoly := by
  unfold modByMonic divModByMonicAux
  rw [dif_pos hq]
  exact divModByMonicAux_go_toPoly_2 p q hq

end DivModByMonic

end CompPoly.CPolynomial.Raw

section DivMod

variable {R : Type*}
variable [Field R] [BEq R] [LawfulBEq R]

lemma Polynomial.C_mul_divByMonic_eq' {R : Type*} [Field R] (a : R) (p q : R[X]) (hq : q.Monic) :
    (Polynomial.C a * p) /ₘ q = Polynomial.C a * (p /ₘ q) := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (Polynomial.div_modByMonic_unique _ _ hq ⟨by
      calc Polynomial.C a * (p %ₘ q) + q * (Polynomial.C a * (p /ₘ q))
          = Polynomial.C a * ((p %ₘ q) + q * (p /ₘ q)) := by ring
        _ = Polynomial.C a * p := by rw [Polynomial.modByMonic_add_div p hq],
      by rw [Polynomial.degree_C_mul ha]; exact Polynomial.degree_modByMonic_lt p hq⟩).1

private lemma not_monic_of_toPoly_zero (q : CPolynomial.Raw R)
    (hq' : q.toPoly = 0) : ¬ (Raw.C q.leadingCoeff⁻¹ * q).monic = true := by
  intro h
  have := (CPolynomial.Raw.monic_iff_toPoly_monic _).mp h
  rw [CPolynomial.Raw.toPoly_mul_raw, CPolynomial.Raw.toPoly_C,
      CPolynomial.Raw.leadingCoeff_eq_toPoly_leadingCoeff, hq'] at this
  simp [Polynomial.Monic] at this

private lemma monic_raw_of_toPoly_ne_zero (q : CPolynomial.Raw R)
    (hq' : q.toPoly ≠ 0) : (Raw.C q.leadingCoeff⁻¹ * q).monic = true := by
  rw [CPolynomial.Raw.monic_iff_toPoly_monic, CPolynomial.Raw.toPoly_mul_raw,
      CPolynomial.Raw.toPoly_C, CPolynomial.Raw.leadingCoeff_eq_toPoly_leadingCoeff]
  have := Polynomial.monic_mul_leadingCoeff_inv hq'
  rwa [_root_.mul_comm] at this

private lemma monic_poly_of_toPoly_ne_zero (q : CPolynomial.Raw R)
    (hq' : q.toPoly ≠ 0) :
    (Polynomial.C q.toPoly.leadingCoeff⁻¹ * q.toPoly).Monic := by
  have := Polynomial.monic_mul_leadingCoeff_inv hq'
  rwa [_root_.mul_comm] at this

theorem CPolynomial.Raw.div_toPoly (p q : CPolynomial.Raw R) :
    (div p q).toPoly = (Polynomial.div p.toPoly q.toPoly) := by
  unfold Raw.div
  by_cases hq' : q.toPoly = 0
  · unfold Raw.divByMonic Raw.divModByMonicAux
    simp [not_monic_of_toPoly_zero q hq']
    change (0 : CPolynomial.Raw R).toPoly = _
    rw [Raw.toPoly_zero]
    simp [Polynomial.div, hq']
  · rw [show Raw.C q.leadingCoeff⁻¹ • p = Raw.C q.leadingCoeff⁻¹ * p from rfl]
    rw [divByMonic_toPoly _ _ (monic_raw_of_toPoly_ne_zero q hq')]
    rw [toPoly_mul_raw, toPoly_C, toPoly_mul_raw, toPoly_C, leadingCoeff_eq_toPoly_leadingCoeff]
    rw [Polynomial.C_mul_divByMonic_eq' _ _ _ (monic_poly_of_toPoly_ne_zero q hq')]
    show Polynomial.C q.toPoly.leadingCoeff⁻¹ *
        (p.toPoly /ₘ (Polynomial.C q.toPoly.leadingCoeff⁻¹ * q.toPoly)) = _
    simp only [Polynomial.div]
    ring_nf

theorem CPolynomial.div_toPoly (p q : CPolynomial R) :
    (div p q).toPoly = (Polynomial.div p.toPoly q.toPoly) := by
  show (Raw.div p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  exact CPolynomial.Raw.div_toPoly p.val q.val

theorem CPolynomial.Raw.mod_toPoly (p q : CPolynomial.Raw R) (hq : q.toPoly ≠ 0) :
    (mod p q).toPoly = (Polynomial.mod p.toPoly q.toPoly) := by
  unfold Raw.mod
  rw [modByMonic_toPoly _ _ (monic_raw_of_toPoly_ne_zero q hq)]
  rw [toPoly_mul_raw, toPoly_C, leadingCoeff_eq_toPoly_leadingCoeff]
  simp only [Polynomial.mod]
  ring_nf

theorem CPolynomial.mod_toPoly (p q : CPolynomial R) (hq : q ≠ 0) :
    (mod p q).toPoly = (Polynomial.mod p.toPoly q.toPoly) := by
  show (Raw.mod p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  have hq_val : q.val.toPoly ≠ 0 := by
    intro h
    apply hq
    apply CPolynomial.ext
    have hsize := (trim_size_zero_iff_toPoly_zero q.val).mpr h
    rw [q.property] at hsize
    exact Array.eq_empty_of_size_eq_zero hsize
  exact CPolynomial.Raw.mod_toPoly p.val q.val hq_val

end DivMod

end ImplementationCorrectness
