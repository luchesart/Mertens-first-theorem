import Mertens.Concrete
import Mertens.Exponential
import Mathlib

/-! A Rankin bound for all exponents at least three. This direct majorant
avoids a second appeal to a prime number theorem. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens

private def rankinWeight (n : ℕ) : ℝ := (n : ℝ) ^ (-101 / 100 : ℝ)

private theorem rankin_weight_nonneg (n : ℕ) : 0 ≤ rankinWeight n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

private theorem rankin_summable : Summable rankinWeight :=
  Real.summable_nat_rpow.mpr (by norm_num)

private theorem rankin_sum_le : (∑' n : ℕ, rankinWeight n) ≤ 101 := by
  let f (x : ℝ) := x ^ (-101 / 100 : ℝ)
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-101 / 100 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)
  have hI : ∫ t : ℝ in Set.Ioi 1, f t = 100 := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num
  have htail : (∑' n : ℕ, rankinWeight (n + 2)) ≤ 100 := by
    apply Real.tsum_le_of_sum_range_le (fun n => rankin_weight_nonneg _)
    intro N
    have ha : AntitoneOn f (Icc (1 : ℝ) (1 + (N : ℝ))) := by
      intro a ha b _ hab
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one ha.1) hab (by norm_num)
    calc
      (∑ i ∈ Finset.range N, rankinWeight (i + 2)) =
          ∑ i ∈ Finset.range N, f (1 + (i + 1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [rankinWeight, f]
        push_cast
        congr 1
        ring
      _ ≤ ∫ x in (1 : ℝ)..1 + N, f x := ha.sum_le_integral
      _ ≤ ∫ x in Set.Ioi 1, f x := by
        rw [intervalIntegral.integral_of_le (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ 1 + (N : ℝ))]
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with t ht
          exact Real.rpow_nonneg (le_trans zero_le_one ht.le) _
        · exact Filter.Eventually.of_forall (fun _ ht => ht.1)
      _ = 100 := hI
  have htwo : (∑ n ∈ Finset.range 2, rankinWeight n) = 1 := by
    norm_num [Finset.sum_range_succ, rankinWeight]
  have hsplit := rankin_summable.sum_add_tsum_nat_add 2
  linarith

/-- Decay from one extra power of any prime, uniform down to the prime 2. -/
private theorem rankin_ratio {p : ℝ} (hp : 2 ≤ p) :
    Real.exp (-(17 / 50) * Real.log p) ≤ 4 / 5 := by
  have hp₁ : 1 ≤ p := by linarith
  have h := Real.log_le_log (x := (5 / 4 : ℝ) ^ 3) (y := p) (by norm_num)
    ((by norm_num : (5 / 4 : ℝ) ^ 3 ≤ 2).trans hp)
  rw [Real.log_pow] at h
  have hlog : -(17 / 50) * Real.log p ≤ -Real.log (5 / 4) := by
    nlinarith [Real.log_nonneg hp₁]
  calc
    _ ≤ Real.exp (-Real.log (5 / 4)) := Real.exp_le_exp.mpr hlog
    _ = 4 / 5 := by rw [Real.exp_neg, Real.exp_log (by norm_num)] ; norm_num

/-- Estimate one prime power across the cutoff by splitting its exponent
between the cutoff, the geometric series in j and a convergent p-series. -/
private theorem rankin_term (u : ℝ) (j : ℕ) (p : Nat.Primes) :
    (if Real.exp u < (p : ℝ) ^ (j + 3)
      then Real.log (p : ℝ) / (p : ℝ) ^ (j + 3) else 0) ≤
      (100 * Real.exp (-(33 / 50) * u) * (4 / 5 : ℝ)^j) * rankinWeight p.val := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp₂ : 2 ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  let l := Real.log (p : ℝ)
  have hweight : rankinWeight p.val = Real.exp (l * (-101 / 100)) :=
    Real.rpow_def_of_pos hp _
  split_ifs with hcut
  · have hlog : u < ((j : ℝ) + 3) * l := by
      have h := Real.log_lt_log (Real.exp_pos u) hcut
      simpa [l, Real.log_pow] using h
    have hA : Real.exp (-(33 / 50) * (((j : ℝ) + 3) * l)) ≤
        Real.exp (-(33 / 50) * u) := Real.exp_le_exp.mpr (by linarith)
    have hB : (Real.exp (-(17 / 50) * l)) ^ j ≤ (4 / 5 : ℝ) ^ j :=
      pow_le_pow_left₀ (Real.exp_pos _).le (rankin_ratio hp₂) j
    have hl : l ≤ 100 * Real.exp (l / 100) := by linarith [Real.add_one_le_exp (l / 100)]
    have hpowers : (p : ℝ) ^ (j + 3) = Real.exp (((j : ℝ) + 3) * l) := by
      simpa [l, Real.exp_log hp] using (Real.exp_nat_mul l (j+3)).symm
    calc
      Real.log (p : ℝ) / (p : ℝ) ^ (j+3) =
          l * Real.exp (-(((j : ℝ) + 3) * l)) := by rw [hpowers, Real.exp_neg, div_eq_mul_inv]
      _ ≤ (100 * Real.exp (l/100)) * Real.exp (-(((j : ℝ) + 3) * l)) :=
        mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = (100 * Real.exp (-(33/50) * (((j : ℝ) + 3) * l)) *
          (Real.exp (-(17/50) * l))^j) * rankinWeight p.val := by
        rw [hweight, ← Real.exp_nat_mul]
        simp only [mul_assoc, ← Real.exp_add]
        congr 2; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (rankin_weight_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB
          (pow_nonneg (Real.exp_pos _).le _) (by positivity)
  · exact mul_nonneg (by positivity) (rankin_weight_nonneg _)

private theorem prime_weight_sum_le : (∑' p : Nat.Primes, rankinWeight p.val) ≤ 101 := by
  have h := rankin_summable.tsum_subtype_le (fun n : ℕ => rankinWeight n)
    {n : ℕ | n.Prime} rankin_weight_nonneg
  exact h.trans rankin_sum_le

/-- A uniform bound for the complete, normalized sum over all powers k ≥ 3,
with the exact prime cutoff of the manuscript. -/
theorem higher_rankin_majorant (u : ℝ) :
    Input.higherAt u ≤ 50500 * Real.exp (-(4 / 25) * u) := by
  let c := 100 * Real.exp (-(33/50) * u)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hweights : Summable (fun p : Nat.Primes => rankinWeight p.val) := rankin_summable.subtype _
  have hj (j : ℕ) : Input.primePowerTail (j+3) (Real.exp u) ≤
      (c * 101) * (4 / 5 : ℝ) ^ j := by
    have hq : 0 ≤ c * (4 / 5 : ℝ) ^ j := mul_nonneg hc (by positivity)
    let term (p : Nat.Primes) := if Real.exp u < (p : ℝ)^(j + 3)
      then Real.log (p : ℝ) / (p : ℝ)^(j + 3) else 0
    have hi : Summable term := Summable.of_nonneg_of_le (fun p => by
      dsimp [term]; split_ifs
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le))
          (pow_nonneg (Nat.cast_nonneg _) _)
      · rfl) (rankin_term u j) (hweights.mul_left (c * (4/5:ℝ)^j))
    change (∑' p, term p) ≤ _
    calc
      _ ≤ ∑' p : Nat.Primes, (c * (4/5:ℝ)^j) * rankinWeight p.val :=
        hi.tsum_le_tsum (rankin_term u j) (hweights.mul_left _)
      _ = (c * (4/5:ℝ)^j) * ∑' p : Nat.Primes, rankinWeight p.val := by rw [tsum_mul_left]
      _ ≤ (c * (4/5:ℝ)^j) * 101 :=
        mul_le_mul_of_nonneg_left prime_weight_sum_le hq
      _ = _ := by ring
  have hg := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (4/5:ℝ)) (by norm_num)).mul_left (c * 101)
  have hsum : (∑' j : ℕ, Input.primePowerTail (j+3) (Real.exp u)) ≤ (c * 101) * 5 := by
    have hs : Summable (fun j : ℕ => Input.primePowerTail (j+3) (Real.exp u)) := by
      apply Summable.of_nonneg_of_le _ hj hg.summable
      intro j
      apply tsum_nonneg
      intro p
      split_ifs
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le))
          (pow_nonneg (Nat.cast_nonneg _) _)
      · exact le_rfl
    calc
      _ ≤ _ := hs.tsum_le_tsum hj hg.summable
      _ = _ := by convert hg.tsum_eq using 1; norm_num
  have hsqrt : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
    rw [← Real.exp_half]
  calc
    Input.higherAt u ≤ Real.sqrt (Real.exp u) * ((c*101)*5) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = _ := by
      rw [hsqrt]
      dsimp [c]
      calc
        _ = 50500 * (Real.exp (u / 2) * Real.exp (-(33 / 50) * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem higher_tail_lt {u : ℝ} (hu : 495 ≤ u) :
    Input.higherAt u < 1 / (10 : ℝ)^29 :=
  (higher_rankin_majorant u).trans_lt <|
    (mul_le_mul_of_nonneg_right (by norm_num : (50500 : ℝ) ≤ 51000)
      (Real.exp_pos _).le).trans_lt (rankin_majorant_lt hu)

end Mertens
