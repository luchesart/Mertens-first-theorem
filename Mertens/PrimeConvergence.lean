import Mertens.Mollifier
import Mertens.PrimeSplit
import Mertens.Components
import Mertens.Exponential
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Passage from smooth Landau pairings to the fixed Logan kernel

The mollified primal pairing is written by moving the mollifier onto the
summatory function. This tests the explicit formula against the convolution of
the Logan kernel with the reflected mollifier. The compact cutoff is identically
one wherever the translated test can see the summatory function. -/
noncomputable section
open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology Convolution BigOperators
namespace Mertens.Input

private theorem smoothAverage_limit (mass : ∫ u in window, kernel u = 1)
    {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ) (hb : ∀ u ∈ smoothClip, ‖f u‖ ≤ B) :
    Tendsto (fun n => smoothAverage n f) atTop (𝓝 (avg f)) := by
  have hki : IntegrableOn kernel window := integrable_of_integral_eq_one mass
  have hB0 := (norm_nonneg (f 495)).trans (hb 495 (by norm_num [smoothClip]))
  have hcm : MeasurableSet smoothClip := measurableSet_Icc
  have hfc : Integrable (smoothClip.indicator f) := by
    apply (integrable_indicator_iff hcm).mpr
    exact (integrableOn_const (s := smoothClip) (μ:=volume) (C:=B) |>.mpr
      (Or.inr isCompact_Icc.measure_lt_top)).mono' hf.aestronglyMeasurable
        ((ae_restrict_mem hcm).mono (fun u hu => hb u hu))
  have hbc (u : ℝ) : ‖smoothClip.indicator f u‖ ≤ B := by
    by_cases hu : u ∈ smoothClip
    · simpa [hu] using hb u hu
    · simpa [hu] using hB0
  have hconv (n : ℕ) (u : ℝ) : ‖smoothValue n f u‖ ≤ B := by
    simpa only [dist_zero_right] using
      (dist_convolution_le (z₀:=0) hB0 ((smoothBump n).support_normed_eq (μ:=volume)).subset
        ((smoothBump n).nonneg_normed) ((smoothBump n).integral_normed)
        hfc.aestronglyMeasurable
        (fun t (_ : t ∈ Metric.ball u (smoothBump n).rOut) => by simpa using hbc t))
  have hcont (n : ℕ) : Continuous (smoothValue n f) :=
    (smoothBump n).hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ)
      (smoothBump n).continuous_normed hfc.locallyIntegrable
  have hl := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) bump_shrinks (K:=2) (Eventually.of_forall (fun n => by dsimp [smoothBump]; linarith))
    hfc.locallyIntegrable
  apply tendsto_integral_of_dominated_convergence (fun u => kernel u * B)
  · intro n
    exact hki.aestronglyMeasurable.mul (hcont n).aestronglyMeasurable
  · exact hki.mul_const B
  · intro n
    exact ae_of_all _ (fun u => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg u)]
      exact mul_le_mul_of_nonneg_left (hconv n u) (kernel_nonneg u))
  · filter_upwards [ae_mono (Measure.restrict_le_self (s:=window)) hl,
      ae_restrict_mem (measurableSet_Ioo (a:=lo) (b:=hi))] with u hu hw
    have hc : u ∈ smoothClip := by
      obtain ⟨h₁,h₂⟩ := hw
      norm_num [lo,hi] at h₁ h₂
      constructor <;> linarith
    simpa only [indicator_of_mem hc] using hu.const_mul (kernel u)

theorem mangoldt_measurable : Measurable normalizedMangoldt := by
  have h : Measurable (fun u : ℝ => mangoldtSum (Real.exp u)) :=
    (measurable_of_countable (fun m : ℕ => ∑ n ∈ Finset.range (m+1),
      ArithmeticFunction.vonMangoldt n / (n:ℝ))).comp Real.continuous_exp.measurable.nat_floor
  exact (Real.continuous_sqrt.comp Real.continuous_exp).measurable.mul
    ((h.sub measurable_id).add measurable_const)

theorem trivial_measurable : Measurable trivialAt := by
  let a (n : ℕ) (u : ℝ) := Real.exp (-(2*(n:ℝ)+5/2)*u)/(2*(n:ℝ)+3)
  have hm : Measurable (fun u : ℝ => (∑' n, ENNReal.ofReal (a n u)).toReal) :=
    (Measurable.ennreal_tsum (fun n => by dsimp [a]; fun_prop)).ennreal_toReal
  convert hm using 1
  ext u
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun n => (ENNReal.toReal_ofReal (by positivity)).symm

theorem mangoldt_bounded : ∃ B, ∀ u ∈ smoothClip, ‖normalizedMangoldt u‖ ≤ B := by
  let A := mangoldtSum (Real.exp 497)
  let Y := Real.sqrt (Real.exp 497)
  refine ⟨Y * (A + 497 + |Real.eulerMascheroniConstant|), ?_⟩
  intro u hu
  have hau : mangoldtSum (Real.exp u) ≤ A := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.range_mono
      exact Nat.succ_le_succ (Nat.floor_mono (Real.exp_le_exp.mpr hu.2))
    · exact fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hA0 : 0 ≤ mangoldtSum (Real.exp u) := Finset.sum_nonneg
    (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
  have hu0 : 0 ≤ u := (by norm_num : (0:ℝ) ≤ 495).trans hu.1
  rw [normalizedMangoldt, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul (Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hu.2)) _ (abs_nonneg _)
    (Real.sqrt_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add_right ((abs_sub _ _).trans (by
    rw [abs_of_nonneg hA0, abs_of_nonneg hu0]
    exact add_le_add hau hu.2)) _)

theorem trivial_bounded (u : ℝ) (hu : u ∈ smoothClip) : ‖trivialAt u‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (trivialAt_nonneg _)]
  have h := trivial_zero_tail_le (u := u) ((by norm_num : (0:ℝ) < 495).trans_le hu.1)
  have h' := trivial_majorant_lt hu.1
  have h'' : Real.exp (-(5 / 2) * u) / (1 - Real.exp (-2 * u)) < 1 / (10:ℝ)^500 := by
    convert h' using 3; ring
  exact (h.trans h''.le).trans (by norm_num)

theorem smoothAverage_mangoldt_limit (mass : ∫ u in window, kernel u = 1) :
    Tendsto (fun n => smoothAverage n normalizedMangoldt) atTop (𝓝 (avg normalizedMangoldt)) := by
  obtain ⟨B,hB⟩ := mangoldt_bounded
  exact smoothAverage_limit mass mangoldt_measurable B hB

theorem smoothAverage_trivial_limit (mass : ∫ u in window, kernel u = 1) :
    Tendsto (fun n => smoothAverage n trivialAt) atTop (𝓝 (avg trivialAt)) :=
  smoothAverage_limit mass trivial_measurable 1 trivial_bounded

end Mertens.Input
