import Mathlib

/-! # Analytic estimates used in the transfer

Each theorem keeps the analytic input local. In particular no zero computation
or explicit formula is introduced as a global axiom. Indices may distinguish
multiple copies of a zero with the same value. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Mertens

/-- Real contribution to the Hadamard mass from a single zero. -/
def hadamardTerm (z : ℂ) : ℝ := ((z * (1 - z))⁻¹).re

theorem hadamard_term_nonneg (z : ℂ) (h₀ : 0 ≤ z.re) (h₁ : z.re ≤ 1) :
    0 ≤ hadamardTerm z := by
  rw [hadamardTerm, Complex.inv_re]
  apply div_nonneg
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, zero_sub, mul_neg, sub_neg_eq_add]
    exact add_nonneg (mul_nonneg h₀ (sub_nonneg.mpr h₁)) (mul_self_nonneg _)
  · rw [Complex.normSq_eq_norm_sq]
    positivity

theorem hadamard_mass_on_critical_line (z : ℂ) (hz : z.re = 1 / 2) :
    hadamardTerm z = (‖z‖ ^ 2)⁻¹ := by
  have h : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext <;> simp [hz]
    ring
  rw [hadamardTerm, h, Complex.mul_conj, ← Complex.ofReal_inv, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- A finite set of critical-line zeros spends at most the global Hadamard mass.
The identity evaluating that global mass comes from the logarithmic derivative
of the completed zeta function. -/
theorem finite_mass_le {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (strip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (half : ∀ i ∈ s, (ρ i).re = 1 / 2)
    (hs : Summable (fun i => hadamardTerm (ρ i))) :
    (∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹) ≤ ∑' i, hadamardTerm (ρ i) := by
  calc
    (∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹) = ∑ i ∈ s, hadamardTerm (ρ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hadamard_mass_on_critical_line (ρ i) (half i hi)).symm
    _ ≤ ∑' i, hadamardTerm (ρ i) :=
      hs.sum_le_tsum s (fun i _ => hadamard_term_nonneg (ρ i) (strip i).1 (strip i).2)

/-- On the critical line the oscillatory factor has norm one. -/
def criticalWave (γ ω : ℝ) (ell : ℝ → ℝ) : ℂ :=
  Complex.exp (((-(γ * ω) : ℝ) : ℂ) * Complex.I) * (ell γ : ℂ)

theorem criticalWave_norm (γ ω : ℝ) (ell : ℝ → ℝ) :
    ‖criticalWave γ ω ell‖ = |ell γ| := by
  simp [criticalWave, norm_mul, Complex.norm_exp, Complex.mul_re]

/-- Büthe's coefficient and the desired coefficient share the same wave. -/
def butheTerm (ω : ℝ) (b z : ℂ) : ℝ :=
  (b * (z⁻¹ - ((ω : ℂ) * z ^ 2)⁻¹)).re

def firstTerm (b z : ℂ) : ℝ := (b * z⁻¹).re

theorem reweight_low_zeros {ι : Type*} (s : Finset ι) (ρ b : ι → ℂ)
    (ω : ℝ) (hω : 0 < ω) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    (∑ i ∈ s, firstTerm (b i) (ρ i)) ≤
      (∑ i ∈ s, butheTerm ω (b i) (ρ i)) + (∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹) / ω := by
  let corr (i : ι) := b i * ((ω : ℂ) * (ρ i) ^ 2)⁻¹
  have hcorr (i) (hi : i ∈ s) : (corr i).re ≤ (‖ρ i‖ ^ 2)⁻¹ / ω := by
    calc
      (corr i).re ≤ ‖corr i‖ := Complex.re_le_norm _
      _ = ‖b i‖ * (ω * ‖ρ i‖ ^ 2)⁻¹ := by
        simp [corr, norm_mul, norm_pow, abs_of_pos hω]
      _ ≤ 1 * (ω * ‖ρ i‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (hb i hi) (by positivity)
      _ = (‖ρ i‖ ^ 2)⁻¹ / ω := by
        simp [mul_inv_rev, div_eq_mul_inv]
  calc
    (∑ i ∈ s, firstTerm (b i) (ρ i)) =
        (∑ i ∈ s, butheTerm ω (b i) (ρ i)) + ∑ i ∈ s, (corr i).re := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [firstTerm, butheTerm, corr, mul_sub]
    _ ≤ (∑ i ∈ s, butheTerm ω (b i) (ρ i)) + ∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹ / ω :=
      add_le_add_left (Finset.sum_le_sum hcorr) _
    _ = _ := by rw [Finset.sum_div]

/-- Dusart's relative error decreases along the ray once its logarithm is
at least 247. -/
theorem dusart_uniform_on_ray {y : ℝ} (theta : ℝ → ℝ)
    (hy : 0 < y) (hlog : 247 ≤ Real.log y)
    (hd : ∀ t, y ≤ t → |theta t - t| ≤ (1 / 100 : ℝ) * t / (Real.log t)^2) :
    ∀ t, y ≤ t → |theta t - t| ≤ ((1 / 100 : ℝ) / 247^2) * t := by
  intro t ht
  have ht₀ := hy.trans_le ht
  have hlogt := hlog.trans (Real.log_le_log hy ht)
  have hden : (247 : ℝ)^2 ≤ (Real.log t)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlogt)
      (show 0 ≤ Real.log t + 247 by linarith)]
  calc
    _ ≤ (1 / 100 : ℝ) * t / (Real.log t)^2 := hd t ht
    _ ≤ (1 / 100 : ℝ) * t / 247^2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

/-- The improper integral comparison in the prime-square estimate. Here
`theta` is instantiated by Chebyshev's theta function. The hypotheses are
the partial summation identity and the two-sided relative error bound. -/
theorem square_bound_of_partial_summation {y D Q : ℝ} (theta : ℝ → ℝ)
    (hy : 0 < y) (hD : 0 ≤ D)
    (hθ : ∀ t, y ≤ t → |theta t - t| ≤ D * t)
    (hAbel : Q = -(theta y / y) + (2 * y) *
        (∫ t in Set.Ioi y, theta t / t ^ 3)) :
    Q ≤ 1 + 3 * D := by
  have hstart : 1 - D ≤ theta y / y := by
    apply (le_div_iff₀ hy).2
    nlinarith [(abs_le.mp (hθ y le_rfl)).1]
  have hneg (t : ℝ) (ht : 0 < t) : t ^ (-2 : ℝ) = (t ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.rpow_two]
  have hI : (∫ t in Set.Ioi y, t ^ (-2 : ℝ)) = 1 / y := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy]
    norm_num [one_div]
    exact Real.rpow_neg_one _
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy).const_mul (1 + D)
  have hcomp : (∫ t in Set.Ioi y, theta t / t ^ 3) ≤ (1 + D) * (1 / y) := by
    by_cases hint : IntegrableOn (fun t : ℝ => theta t / t ^ 3) (Set.Ioi y)
    · calc
        (∫ t in Set.Ioi y, theta t / t ^ 3) ≤
            ∫ t in Set.Ioi y, (1 + D) * t ^ (-2 : ℝ) := by
          apply setIntegral_mono_on hint hmajor measurableSet_Ioi
          intro t ht
          have ht₀ : 0 < t := hy.trans ht
          rw [hneg t ht₀, div_le_iff₀ (pow_pos ht₀ 3)]
          calc
            theta t ≤ (1 + D) * t := by nlinarith [(abs_le.mp (hθ t ht.le)).2]
            _ = (1 + D) * (t ^ 2)⁻¹ * t ^ 3 := by field_simp [ht₀.ne']; ring
        _ = (1 + D) * (1 / y) := by rw [integral_const_mul, hI]
    · rw [integral_undef hint]
      positivity
  have h := mul_le_mul_of_nonneg_left hcomp (by positivity : 0 ≤ 2 * y)
  have hscale : 2 * y * ((1 + D) * (1 / y)) = 2 * (1 + D) := by
    field_simp [hy.ne']; ring
  rw [hscale] at h
  linarith

/-- The normalized trivial-zero series, indexed by the zeros -2,-4,... . -/
theorem trivial_zero_tail_le {u : ℝ} (hu : 0 < u) :
    (∑' n : ℕ, Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) / (2 * (n : ℝ) + 3)) ≤
      Real.exp (-(5 / 2) * u) / (1 - Real.exp (-2 * u)) := by
  let c := Real.exp (-(5 / 2) * u)
  let q := Real.exp (-2 * u)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq' : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hq hq').mul_left c
  let f (n : ℕ) := Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) / (2 * (n : ℝ) + 3)
  have hbound (n : ℕ) : f n ≤ c * q ^ n := by
    have hnum : Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) = c * q ^ n := by
      dsimp [c, q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    dsimp [f]
    rw [hnum]
    apply div_le_self (mul_nonneg hc (pow_nonneg hq n))
    linarith [Nat.cast_nonneg (α := ℝ) n]
  change (∑' n, f n) ≤ c / (1 - q)
  have hs : Summable f := Summable.of_nonneg_of_le
    (fun n => div_nonneg (Real.exp_pos _).le (by positivity)) hbound hg.summable
  calc
    (∑' n, f n) ≤ ∑' n : ℕ, c * q ^ n := hs.tsum_le_tsum hbound hg.summable
    _ = c / (1 - q) := by simpa [div_eq_mul_inv] using hg.tsum_eq

end Mertens
