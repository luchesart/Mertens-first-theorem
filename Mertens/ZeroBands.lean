import Mertens.Transfer
import Mertens.PrimeSplit
import Mertens.KernelSymmetry

/-! Split the absolutely summable, actual zero series. Relate the complex
transform on the critical line to the published real transform using the
proved symmetry of the particular shifted kernel. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens.Input

theorem wave_on_critical_line (mass : ∫ u in window, kernel u = 1) (z : ZeroCopy)
    (hz : (rho z).re = 1 / 2) :
    (wave z).re = firstTerm (lowWeight z) (rho z) := by
  have hphase : (1/2 - rho z) * (omega : ℂ) =
      (((-((rho z).im * omega)) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hz]
  rw [wave, frequency_on_critical_line z hz, transform_real mass, hphase]
  rfl

/-- The remaining external explicit-formula input contains a single sum over
all actual nontrivial zeros, not the paper's decomposition into three bands. -/
theorem explicit_formula_bands (finite : lowBand.Finite)
    (mass : ∫ u in window, kernel u = 1)
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2)
    (landau : HasSum (fun z : ZeroCopy => (wave z).re) (avg normalizedMangoldt - avg trivialAt)) :
    avg normalizedMangoldt = lowSum finite.toFinset + middle + high + avg trivialAt := by
  classical
  let f := fun z : ZeroCopy => (wave z).re
  let M : Set ZeroCopy := {z | 4*10^9 < |(rho z).im| ∧ |(rho z).im| ≤ 10^10}
  let H : Set ZeroCopy := {z | 10^10 < |(rho z).im|}
  have hf : Summable f := landau.summable
  have hlow : (∑' z, lowBand.indicator f z) = lowSum finite.toFinset := by
    rw [tsum_eq_sum (s := finite.toFinset)]
    · refine Finset.sum_congr rfl (fun z hz => ?_)
      have hmem := finite.mem_toFinset.mp hz
      rw [Set.indicator_of_mem hmem]
      refine wave_on_critical_line mass z (critical z ?_)
      exact (show |(rho z).im| ≤ 4*10^9 from hmem).trans (by norm_num)
    · exact fun z h => Set.indicator_of_not_mem (fun hz => h (finite.mem_toFinset.mpr hz)) _
  have hmid : (∑' z, M.indicator f z) = middle := by
    apply tsum_congr
    intro z
    simp only [M, Set.indicator_apply, Set.mem_setOf_eq, middle, f]
  have hhi : (∑' z, H.indicator f z) = high := by
    apply tsum_congr
    intro z
    simp only [H, Set.indicator_apply, Set.mem_setOf_eq, high, f]
  have hparts (z : ZeroCopy) : lowBand.indicator f z + M.indicator f z + H.indicator f z = f z := by
    by_cases h₁ : |(rho z).im| ≤ 4*10^9
    · have h₂ : |(rho z).im| ≤ 10^10 := h₁.trans (by norm_num)
      simp [Set.indicator, lowBand, H, M, h₁, h₂, not_lt.mpr h₁, not_lt.mpr h₂]
    · by_cases h₂ : |(rho z).im| ≤ 10^10
      · simp [Set.indicator, lowBand, H, M, h₁, h₂, lt_of_not_ge h₁, not_lt.mpr h₂]
      · simp [Set.indicator, lowBand, H, M, h₁, h₂, lt_of_not_ge h₂]
  have htotal : lowSum finite.toFinset + middle + high = avg normalizedMangoldt - avg trivialAt := by
    rw [← hlow, ← hmid, ← hhi, ← (hf.indicator lowBand).tsum_add (hf.indicator M),
      ← ((hf.indicator lowBand).add (hf.indicator M)).tsum_add (hf.indicator H)]
    exact (tsum_congr hparts).trans landau.tsum_eq
  linarith only [htotal]

end Mertens.Input
