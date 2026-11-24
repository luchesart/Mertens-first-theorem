import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A numerical bound for the Hadamard constant
The midpoint correction reduces the required exact computation to 384
harmonic summands. The estimate of the logarithm uses dyadic reduction.
-/

open Filter Topology

namespace Mertens

private noncomputable def harmonicMidpoint (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2)

/-- Shifting the logarithm by a half gives decreasing upper bounds for γ. -/
theorem euler_le_harmonic_midpoint (n : ℕ) :
    Real.eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2) := by
  have hanti : Antitone harmonicMidpoint := by
    apply antitone_nat_of_succ_le
    intro k
    have hp : 0 < (k : ℝ) + 1 / 2 := by positivity
    have h := Real.le_log_one_add_of_nonneg (x := 1 / ((k : ℝ) + 1 / 2)) (by positivity)
    have hq : 2 * (1 / ((k : ℝ) + 1 / 2)) / (1 / ((k : ℝ) + 1 / 2) + 2) =
        1 / ((k : ℝ) + 1) := by
      field_simp
      ring
    have ha : 1 + 1 / ((k : ℝ) + 1 / 2) =
        ((k : ℝ) + 1 + 1 / 2) / ((k : ℝ) + 1 / 2) := by
      field_simp
      ring
    rw [hq, ha, Real.log_div (by positivity) hp.ne'] at h
    simp only [harmonicMidpoint, harmonic_succ, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast, Rat.cast_one, Nat.cast_add_one]
    rw [one_div] at h
    linarith [h]
  have hm : Tendsto harmonicMidpoint atTop (𝓝 Real.eulerMascheroniConstant) := by
    have hh := Real.tendsto_harmonic_sub_log.sub
      ((Real.tendsto_log_comp_add_sub_log (1 / 2)).comp tendsto_natCast_atTop_atTop)
    rw [sub_zero] at hh
    apply hh.congr
    intro k
    dsimp [harmonicMidpoint]
    ring
  exact hanti.le_of_tendsto hm n

private def harmonicRec : ℕ → ℚ
| 0 => 0
| n+1 => harmonicRec n + ((n+1:ℕ):ℚ)⁻¹
private theorem harmonic_eq_rec (n : ℕ) : harmonic n = harmonicRec n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [harmonic_succ, harmonicRec, ih, Nat.cast_add_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
private theorem harmonic_384_upper : harmonic 384 < (652915974 : ℚ) / 100000000 := by
  rw [harmonic_eq_rec]
  decide +kernel

private theorem log_product_lower :
    (84829679 : ℝ) / 10000000 < Real.log ((384 + 1 / 2 : ℝ) * (4 * Real.pi)) := by
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  have hr : (84829679 : ℝ) / 10000000 <
      ((12 : ℕ) : ℝ) * Real.log 2 + 16520175 / 100000000 := by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  have ht : Real.exp ((16520175 : ℝ) / 100000000) < 11796311 / 10000000 := by
    have h := Real.exp_bound' (x := (16520175 : ℝ) / 100000000)
      (by norm_num) (by norm_num) (n := 8) (by decide)
    apply lt_of_le_of_lt h
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    _ < Real.exp (((12 : ℕ) : ℝ) * Real.log 2 + 16520175 / 100000000) :=
      Real.exp_lt_exp.mpr hr
    _ = (2 : ℝ) ^ 12 * Real.exp (16520175 / 100000000) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < (2 : ℝ) ^ 12 * (11796311 / 10000000) :=
      mul_lt_mul_of_pos_left ht (by norm_num)
    _ < _ := by linarith [Real.pi_gt_d20]

/-- The numerical input in the paper's Hadamard-mass estimate. -/
theorem hadamard_constant_lt :
    2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) < (46192 : ℝ) / 1000000 := by
  have hH : (harmonic 384 : ℝ) < (652915974 : ℝ) / 100000000 := by
    have hh := (Rat.cast_lt (K := ℝ)).2 harmonic_384_upper
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh.trans_le (by norm_num)
  have hγ := euler_le_harmonic_midpoint 384
  have hlog := log_product_lower
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hγ
  linarith

end Mertens
