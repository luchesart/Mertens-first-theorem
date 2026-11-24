import Mertens.LandauTest
import Mertens.InputProd
import Mertens.PrimeConvergence

/-! # Moving the smooth test to the function being averaged

Fubini's theorem changes the order of integration between the Logan kernel
and the smooth bump. Clipping the function to the fixed compact interval
is harmless on every translate of the bump meeting the Logan window.
-/

noncomputable section
open MeasureTheory Set Filter Function ContinuousLinearMap
open scoped Convolution
namespace Mertens.Input

private theorem bump_vanishes_outside {n : ℕ} {u t : ℝ}
    (hu : u ∈ window) (ht : t ∉ smoothClip) :
    (smoothBump n).normed volume (u - t) = 0 := by
  by_contra! h
  have hclip := clip_covers_test hu (show u - t ∈ support ((smoothBump n).normed volume) from h)
  exact ht (by simpa using hclip)

private theorem loganTest_zero_outside {n : ℕ} {t : ℝ} (ht : t ∉ smoothClip) :
    loganTest n t = 0 := by
  rw [loganTest_eq]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet window from measurableSet_Ioo)]
    with u hu
  simp [bump_vanishes_outside hu ht]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Change of integration order, valid for real or complex valued functions. -/
theorem test_pair_smul (n : ℕ) {f : ℝ → E} (hf : Integrable (smoothClip.indicator f)) :
    (∫ t : ℝ, loganTest n t • f t) =
      ∫ u in window, kernel u • (∫ t : ℝ, (smoothBump n).normed volume (u-t) •
        smoothClip.indicator f t) := by
  let g := smoothClip.indicator f
  calc
    _ = ∫ t : ℝ, loganTest n t • g t := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      by_cases ht : t ∈ smoothClip
      · simp [g, ht]
      · simp [g, ht, loganTest_zero_outside ht]
    _ = ∫ t : ℝ, ∫ u in window,
          kernel u • ((smoothBump n).normed volume (u - t) • g t) := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      simp_rw [← smul_assoc, smul_eq_mul]
      rw [integral_smul_const, loganTest_eq]
    _ = ∫ u in window, ∫ t : ℝ,
          kernel u • ((smoothBump n).normed volume (u - t) • g t) :=
      (integral_integral_swap (test_integrable_prod n hf)).symm
    _ = _ := by simp_rw [integral_smul]; rfl

/-- The clipping disappears pointwise wherever a translated bump is nonzero. -/
theorem test_pair_smul_full (n : ℕ) {f : ℝ → E} (hf : Integrable (smoothClip.indicator f)) :
    (∫ t : ℝ, loganTest n t • f t) =
      ∫ u in window, kernel u • (∫ t : ℝ, (smoothBump n).normed volume (u-t) • f t) := by
  rw [test_pair_smul n hf]
  apply setIntegral_congr_fun (show MeasurableSet window from measurableSet_Ioo)
  intro u hu
  apply congrArg (fun q : E => kernel u • q)
  apply integral_congr_ae
  apply ae_of_all
  intro t
  by_cases ht : t ∈ smoothClip
  · simp [ht]
  · simp [ht, bump_vanishes_outside hu ht]

theorem smoothTest_pairing (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ)
    (hb : ∀ t ∈ smoothClip, ‖f t‖ ≤ B) :
    (∫ t : ℝ, loganTest n t * f t) = smoothAverage n f := by
  have hm : MeasurableSet smoothClip := measurableSet_Icc
  have hg : Integrable (smoothClip.indicator f) := by
    apply (integrable_indicator_iff hm).mpr
    exact (integrableOn_const (s := smoothClip) (μ := volume) (C := B) |>.mpr
      (Or.inr isCompact_Icc.measure_lt_top)).mono' hf.aestronglyMeasurable
        ((ae_restrict_mem hm).mono (fun t ht => hb t ht))
  simpa only [smoothAverage, avg, smoothValue, convolution_lsmul_swap, smul_eq_mul]
    using test_pair_smul n hg

theorem testPair_mangoldt (n : ℕ) :
    (∫ t : ℝ, loganTest n t * normalizedMangoldt t) = smoothAverage n normalizedMangoldt := by
  obtain ⟨B, hB⟩ := mangoldt_bounded
  exact smoothTest_pairing n mangoldt_measurable B hB

theorem testPair_trivial (n : ℕ) :
    (∫ t : ℝ, loganTest n t * trivialAt t) = smoothAverage n trivialAt :=
  smoothTest_pairing n trivial_measurable 1 trivial_bounded

end Mertens.Input
