import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The scalar sides of Büthe's Lemmas 6.2 and 6.3 at the parameters used in the
paper. Range reduction to powers of two keeps the exponential estimates
short enough for exact rational Taylor comparisons in the kernel.
-/

namespace Mertens

noncomputable def middleMajorant : ℝ :=
  (1 + 11 * 280 * (28/10^9)) / (Real.pi * 280 * ((4/10)^2)) *
    Real.log (10^10) * Real.cosh (280 * Real.sqrt (1 - (4/10)^2)) / Real.sinh 280

noncomputable def highMajorant : ℝ :=
  (32/100) * Real.exp ((495702833137/10^9)/2 + (71/100)*Real.sqrt (280*(28/10^9))) /
    Real.sinh 280 * Real.log (3*280) * Real.log (10^10)

private theorem exp_upper_by_series {u r B : ℝ} {n m : ℕ}
    (hu : u ≤ n * Real.log 2 + r) (hr : 0 ≤ r) (hr' : r ≤ 1) (hm : 0 < m)
    (hB : (2 : ℝ)^n * ((∑ i ∈ Finset.range m, r^i / i.factorial) +
      r^m * (m + 1) / (m.factorial * m)) < B) : Real.exp u < B := by
  have h := Real.exp_bound' hr hr' hm
  calc
    Real.exp u ≤ Real.exp ((n : ℝ) * Real.log 2 + r) := Real.exp_le_exp.mpr hu
    _ = 2^n * Real.exp r := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
    _ < _ := hB

private theorem exp_lower_by_series {u r B : ℝ} {n m : ℕ}
    (hu : n * Real.log 2 + r ≤ u) (hr : 0 ≤ r)
    (hB : B < (2 : ℝ)^n * (∑ i ∈ Finset.range m, r^i / i.factorial)) :
    B < Real.exp u := by
  calc
    B < _ := hB
    _ ≤ (2 : ℝ)^n * Real.exp r :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hr m) (by positivity)
    _ = Real.exp ((n : ℝ) * Real.log 2 + r) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr hu

private theorem denominator_lower : (2001 : ℝ) * 10^118 < Real.sinh 280 := by
  have h : (4002 : ℝ) * 10^118 + 1 < Real.exp 280 := by
    apply exp_lower_by_series (n := 403) (m := 7) (r := 66168/100000)
    · norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  have hneg : Real.exp (-280) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [Real.sinh_eq]
  linarith

private theorem cosh_upper :
    Real.cosh (280 * Real.sqrt (1 - (4/10)^2)) < (1412 : ℝ)*10^108 := by
  have hroot : Real.sqrt (1 - (4/10)^2) ≤ 9165152/10000000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h : Real.exp (280 * Real.sqrt (1 - (4/10)^2)) < (2823 : ℝ)*10^108 := by
    apply exp_upper_by_series (n := 370) (m := 5) (r := 16/100)
    · norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_gt_d9]
    · norm_num
    · norm_num
    · decide
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  have hneg : Real.exp (-(280 * Real.sqrt (1 - (4/10)^2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  rw [Real.cosh_eq]
  linarith

private theorem high_exp_upper :
    Real.exp ((495702833137/10^9)/2 + (71/100)*Real.sqrt (280*(28/10^9))) <
      (438 : ℝ)*10^105 := by
  have hroot : Real.sqrt (280 * (28/10^9)) ≤ 28/10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  apply exp_upper_by_series (n := 357) (m := 6) (r := 3999/10000)
  · norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  · norm_num
  · norm_num
  · decide
  · norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem log_height_upper : Real.log (10^10) < 2303/100 := by
  apply (Real.log_lt_iff_lt_exp (by positivity)).2
  apply exp_lower_by_series (n := 33) (m := 5) (r := 155/1000)
  · norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  · norm_num
  · norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem log_840_upper : Real.log (3*280) < 674/100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  apply exp_lower_by_series (n := 9) (m := 5) (r := 1/2)
  · norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  · norm_num
  · norm_num [Finset.sum_range_succ, Nat.factorial]

theorem middleMajorant_lt : middleMajorant < 116/(10 : ℝ)^13 := by
  have hden : 0 < Real.sinh 280 := lt_trans (by positivity) denominator_lower
  have hp : 0 < Real.pi * 280 * ((4/10 : ℝ)^2) := by positivity
  have h0 : 0 ≤ Real.log (10^10) := Real.log_nonneg (by norm_num)
  have hc0 : 0 ≤ Real.cosh (280 * Real.sqrt (1 - (4/10)^2)) :=
    (Real.cosh_pos _).le
  unfold middleMajorant
  rw [div_lt_iff₀ hden]
  calc
    _ ≤ (1 + 11 * 280 * (28/10^9 : ℝ)) / ((314/100)*280*((4/10)^2)) *
          (2303/100) * (1412*10^108) := by
      gcongr <;> first | exact log_height_upper.le | exact cosh_upper.le | linarith [Real.pi_gt_d2]
    _ < (116/(10 : ℝ)^13) * (2001*10^118) := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left denominator_lower.le (by positivity)

theorem highMajorant_lt : highMajorant < 109/(10 : ℝ)^14 := by
  have hden : 0 < Real.sinh 280 := lt_trans (by positivity) denominator_lower
  have h0 : 0 ≤ Real.log (10^10) := Real.log_nonneg (by norm_num)
  have h1 : 0 ≤ Real.log (3*280) := Real.log_nonneg (by norm_num)
  unfold highMajorant
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hden]
  calc
    _ ≤ (32/100 : ℝ) * (438*10^105) * (674/100) * (2303/100) := by
      gcongr <;> first | exact high_exp_upper.le | exact log_840_upper.le | exact log_height_upper.le
    _ < (109/(10 : ℝ)^14) * (2001*10^118) := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left denominator_lower.le (by positivity)

end Mertens
