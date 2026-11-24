import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponentiating the window

Dyadic range reduction turns both endpoint estimates into comparisons at
arguments less than one. Only mathlib's bounds on `log 2` and the real
exponential series are needed. Every numerical comparison is rational.
-/

namespace Mertens

private theorem exp_dyadic_shift (n : ℕ) (v : ℝ) :
    Real.exp ((n : ℝ) * Real.log 2 + v) = (2 : ℝ) ^ n * Real.exp v := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem exp_remainder_upper :
    Real.exp ((513 : ℝ) / 5000) < 110805 / 100000 := by
  have h := Real.exp_bound' (x := (513 : ℝ) / 5000)
    (by norm_num) (by norm_num) (n := 4) (by decide)
  apply lt_of_le_of_lt h
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem exp_remainder_lower :
    (14769 : ℝ) / 10000 ≤ Real.exp (1989 / 5000) := by
  have h := Real.sum_le_exp_of_nonneg (x := (1989 : ℝ) / 5000) (by norm_num) 3
  apply le_trans _ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The real endpoint is below the decimal upper bound in Theorem 1. -/
theorem exp_upper_endpoint_lt :
    Real.exp ((495702833165 : ℝ) / 10 ^ 9) < (191 / 100 : ℝ) * 10 ^ 215 := by
  have hu : (495702833165 : ℝ) / 10 ^ 9 <
      ((715 : ℕ) : ℝ) * Real.log 2 + 513 / 5000 := by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  calc
    _ < Real.exp (((715 : ℕ) : ℝ) * Real.log 2 + 513 / 5000) := Real.exp_lt_exp.mpr hu
    _ = (2 : ℝ) ^ 715 * Real.exp (513 / 5000) := exp_dyadic_shift 715 _
    _ < (2 : ℝ) ^ 715 * (110805 / 100000) :=
      mul_lt_mul_of_pos_left exp_remainder_upper (by positivity)
    _ < _ := by norm_num

/-- The short interval already has the stated length at the lower endpoint. -/
theorem length_lower_endpoint_gt :
    (26 / 10 : ℝ) * 10 ^ 103 <
      (60 / 10 ^ 6 : ℝ) * Real.exp (((495702833109 : ℝ) / 10 ^ 9) / 2) := by
  have hu : ((357 : ℕ) : ℝ) * Real.log 2 + 1989 / 5000 <
      ((495702833109 : ℝ) / 10 ^ 9) / 2 := by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have h :
      (2 : ℝ) ^ 357 * (14769 / 10000) <
        Real.exp (((495702833109 : ℝ) / 10 ^ 9) / 2) := by
    calc
      _ ≤ (2 : ℝ) ^ 357 * Real.exp (1989 / 5000) :=
        mul_le_mul_of_nonneg_left exp_remainder_lower (by positivity)
      _ = Real.exp (((357 : ℕ) : ℝ) * Real.log 2 + 1989 / 5000) :=
        (exp_dyadic_shift 357 _).symm
      _ < _ := Real.exp_lt_exp.mpr hu
  calc
    _ < (60 / 10 ^ 6 : ℝ) * ((2 : ℝ) ^ 357 * (14769 / 10000)) := by norm_num
    _ < _ := mul_lt_mul_of_pos_left h (by norm_num)


private theorem two_pow_lt_exp {x : ℝ} (n : ℕ) (h : (n : ℝ) * Real.log 2 < x) :
    (2 : ℝ) ^ n < Real.exp x := by
  have hh := Real.exp_lt_exp.mpr h
  rwa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh

private theorem exp_neg_lt_dyadic {x : ℝ} (n : ℕ) (h : (n : ℝ) * Real.log 2 < x) :
    Real.exp (-x) < 1 / (2 : ℝ) ^ n := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by positivity) (two_pow_lt_exp n h)

/-- Dusart's threshold and the coarser logarithmic square threshold on
the whole log window. -/
theorem dusart_range {u : ℝ} (hu : 495 ≤ u) :
    7713133853 < Real.exp (u / 3) ∧ 247 < u / 2 := by
  constructor
  · apply lt_trans _ (two_pow_lt_exp 33 (by
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]))
    norm_num
  · linarith

/-- The sum of the two higher-power majorants in §4 after normalization. -/
theorem higher_majorant_lt {u : ℝ} (hu : 495 ≤ u) (hu' : u ≤ 496) :
    (4 + 4 * (u / 3 + 1)) * Real.exp (-u / 6) < 1 / (10 : ℝ) ^ 29 := by
  have hh := exp_neg_lt_dyadic (x := u / 6) 110 (by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9])
  rw [← neg_div] at hh
  calc
    _ ≤ 670 * Real.exp (-u / 6) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    _ < 670 * (1 / (2 : ℝ) ^ 110) := mul_lt_mul_of_pos_left hh (by norm_num)
    _ < _ := by norm_num

/-- Geometric tail of the normalized contributions of the trivial zeros. -/
theorem trivial_majorant_lt {u : ℝ} (hu : 495 ≤ u) :
    Real.exp (-5 * u / 2) / (1 - Real.exp (-2 * u)) < 1 / (10 : ℝ) ^ 500 := by
  have hn := exp_neg_lt_dyadic (x := 5 * u / 2) 1700 (by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9])
  have hd := exp_neg_lt_dyadic (x := 2 * u) 1 (by
    norm_num only [Nat.cast_one, one_mul]
    linarith [Real.log_two_lt_d9])
  rw [show -(5 * u / 2) = -5 * u / 2 by ring] at hn
  rw [show -(2 * u) = -2 * u by ring, pow_one] at hd
  apply (div_lt_iff₀ (by linarith : 0 < 1 - Real.exp (-2 * u))).2
  calc
    _ < 1 / (2 : ℝ) ^ 1700 := hn
    _ < 1 / (10 : ℝ) ^ 500 * (1 / 2) := by norm_num
    _ ≤ 1 / (10 : ℝ) ^ 500 * (1 - Real.exp (-2 * u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)


/-- Exponential envelope used by the alternative Rankin estimate for higher powers. -/
theorem rankin_majorant_lt {u : ℝ} (hu : 495 ≤ u) :
    51000 * Real.exp (-(4 / 25) * u) < 1 / (10 : ℝ) ^ 29 := by
  have hh := exp_neg_lt_dyadic (x := (4 / 25) * u) 114 (by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9])
  rw [← neg_mul] at hh
  calc
    _ < 51000 * (1 / (2 : ℝ) ^ 114) := mul_lt_mul_of_pos_left hh (by norm_num)
    _ < _ := by norm_num

end Mertens
