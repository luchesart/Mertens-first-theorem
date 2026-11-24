import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The arithmetic function, its weighted average, and extraction and propagation
of a negative value. The analytic estimate on the actual weighted mean is passed
as an explicit hypothesis of the extraction theorem. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Mertens

/-- Logarithmic prime weight, extended by zero to all natural numbers. -/
def primeWeight (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

/-- The cutoff includes a prime at the right endpoint. -/
def primeSum (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋₊ + 1), primeWeight n

private theorem primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n := by
  by_cases hp : n.Prime
  · have hn : 1 ≤ (n : ℝ) := by exact_mod_cast hp.one_le
    rw [primeWeight, if_pos hp]
    exact div_nonneg (Real.log_nonneg hn) n.cast_nonneg
  · simp [primeWeight, hp]

theorem primeSum_mono : Monotone primeSum := by
  intro x y hxy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hxy) 1))
    (fun n _ _ => primeWeight_nonneg n)

/-- Summand of the constant correction in the first theorem, indexed by genuine primes. -/
def constantTerm (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))

theorem constantTerm_summable : Summable constantTerm := by
  have hseries := (Nat.Primes.summable_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 4
  apply hseries.of_nonneg_of_le
  · intro p
    have hp : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
    exact div_nonneg (Real.log_nonneg hp) (mul_nonneg (by positivity) (sub_nonneg.mpr hp))
  · intro p
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hs : (p : ℝ) ^ (-(3 / 2 : ℝ)) * (p : ℝ) ^ 2 = (p : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_add hp]
      norm_num
    have hb := Real.log_le_rpow_div hp.le (by norm_num : 0 < (1 / 2 : ℝ))
    have hpow := Real.rpow_nonneg hp.le (-(3 / 2 : ℝ))
    change Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ))
    apply (div_le_iff₀ (mul_pos hp (by linarith))).mpr
    nlinarith [mul_nonneg hpow (mul_nonneg hp.le (sub_nonneg.mpr hp2))]

def mertensConstant : ℝ := -Real.eulerMascheroniConstant - ∑' p : Nat.Primes, constantTerm p

def error (x : ℝ) : ℝ := primeSum x - Real.log x - mertensConstant

/-- The normalized error on the logarithmic axis. -/
def normalized (u : ℝ) : ℝ := Real.sqrt (Real.exp u) * error (Real.exp u)

theorem normalized_eq_exp (u : ℝ) :
    normalized u = Real.exp (u / 2) * error (Real.exp u) := by
  rw [normalized, Real.exp_half]

/-- The kernel includes the translation by the centre. Endpoint values do not
affect this Lebesgue integral. -/
def weightedMean (K : ℝ → ℝ) (lo hi : ℝ) : ℝ :=
  ∫ u in Ioo lo hi, K u * normalized u

private theorem not_ae_lower_of_mean_lt {K : ℝ → ℝ} {lo hi m : ℝ}
    (hK : ∀ u ∈ Ioo lo hi, 0 ≤ K u)
    (hmass : ∫ u in Ioo lo hi, K u = 1)
    (hm : m ≤ 0) (hmean : weightedMean K lo hi < m) :
    ¬ ∀ᵐ u ∂volume.restrict (Ioo lo hi), m ≤ normalized u := by
  intro h
  have hki : IntegrableOn K (Ioo lo hi) := integrable_of_integral_eq_one hmass
  have hfi : IntegrableOn (fun u => K u * normalized u) (Ioo lo hi) :=
    Integrable.of_integral_ne_zero (ne_of_lt (lt_of_lt_of_le hmean hm))
  have hmono : (∫ u in Ioo lo hi, m * K u) ≤ weightedMean K lo hi := by
    apply integral_mono_ae (hki.const_mul m) hfi
    filter_upwards [h, ae_restrict_mem (measurableSet_Ioo (a := lo) (b := hi))] with u hu hs
    exact (mul_le_mul_of_nonneg_right hu (hK u hs)).trans_eq (mul_comm _ _)
  rw [integral_const_mul, hmass, mul_one] at hmono
  exact (not_lt_of_ge hmono) hmean

/-- A strict negative mean forces a set of positive Lebesgue measure in the
open log window. A singleton or endpoint cannot be the only witness. -/
theorem positive_measure_of_mean_lt {K : ℝ → ℝ} {lo hi m : ℝ}
    (hK : ∀ u ∈ Ioo lo hi, 0 ≤ K u)
    (hmass : ∫ u in Ioo lo hi, K u = 1)
    (hm : m ≤ 0) (hmean : weightedMean K lo hi < m) :
    0 < (volume.restrict (Ioo lo hi)) {u | normalized u < m} := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  apply not_ae_lower_of_mean_lt hK hmass hm hmean
  rw [ae_iff]
  simpa only [not_le] using hzero

/-- Extract an actual x, with its strict open log bounds, from the mean. -/
theorem witness_of_mean_lt {K : ℝ → ℝ} {lo hi m : ℝ}
    (hK : ∀ u ∈ Ioo lo hi, 0 ≤ K u)
    (hmass : ∫ u in Ioo lo hi, K u = 1)
    (hm : m ≤ 0) (hmean : weightedMean K lo hi < m) :
    ∃ x : ℝ, 0 < x ∧ lo < Real.log x ∧ Real.log x < hi ∧ Real.sqrt x * error x < m := by
  have hex : ∃ u ∈ Ioo lo hi, normalized u < m := by
    by_contra! h
    apply not_ae_lower_of_mean_lt hK hmass hm hmean
    filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := lo) (b := hi))] with u hu
    exact h u hu
  obtain ⟨u, hu, hv⟩ := hex
  exact ⟨Real.exp u, Real.exp_pos _, by simpa only [Real.log_exp] using hu.1,
    by simpa only [Real.log_exp] using hu.2, hv⟩

/-- Monotonicity of the prime sum controls the error between any two positive arguments. -/
theorem error_le_left {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    error t ≤ error x + Real.log (x / t) := by
  rw [Real.log_div (ne_of_gt (ht.trans_le htx)) ht.ne']
  unfold error
  linarith [primeSum_mono htx]

/-- Corollary 2: the margin at x pays for every point to its left within the
stated length. The mild hypothesis 1 ≤ sqrt x follows from the paper's window. -/
theorem negative_left_interval {x : ℝ} (hx : 0 < x) (hsize : 1 ≤ Real.sqrt x)
    (hmargin : Real.sqrt x * error x < -(605 / 10^7 : ℝ)) :
    ∀ t ∈ Icc (x - (60 / 10^6) * Real.sqrt x) x, error t < 0 := by
  intro t ht
  set s := Real.sqrt x with hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hsize
  have hsq : s ^ 2 = x := Real.sq_sqrt hx.le
  have hlo : x - (60 / 10^6) * s ≤ t := ht.1
  have hprod := mul_nonneg hspos.le (sub_nonneg.mpr hsize)
  have htpos : 0 < t := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx htpos)
  have herr := error_le_left htpos ht.2
  have hbound : s * Real.log (x / t) < (605 / 10^7 : ℝ) := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlog hspos.le)
    have hdiv : (x - t) * s / t < (605 / 10^7 : ℝ) := by
      apply (div_lt_iff₀ htpos).mpr
      nlinarith [mul_nonneg hspos.le (sub_nonneg.mpr hlo)]
    calc s * (x / t - 1) = (x - t) * s / t := by field_simp; ring
         _ < _ := hdiv
  have hscaled := mul_le_mul_of_nonneg_left herr hspos.le
  change s * error x < _ at hmargin
  by_contra! he
  nlinarith [mul_nonneg hspos.le he]

end Mertens
