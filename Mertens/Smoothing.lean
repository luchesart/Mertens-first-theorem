import Mertens.PrimeConvergence
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

/-- Landau's explicit formula, applied only to smooth tests. All functions
and the mollifiers are fixed. -/
def SmoothLandauPairings : Prop := ∀ n : ℕ,
  HasSum (fun z : ZeroCopy => (wave z * smoothMultiplier n z).re)
    (smoothAverage n normalizedMangoldt - smoothAverage n trivialAt)

/-- Remove the mollifier by Tannery's theorem on the zero side and dominated
convergence on the prime side. Neither side requires the Riemann hypothesis. -/
theorem smoothed_landau_hasSum (mass : ∫ u in window, kernel u = 1)
    (absolute : Summable (fun z : ZeroCopy => ‖wave z‖)) (landau : SmoothLandauPairings) :
    HasSum (fun z : ZeroCopy => (wave z).re) (avg normalizedMangoldt - avg trivialAt) := by
  let F (n : ℕ) (z : ZeroCopy) := (wave z * smoothMultiplier n z).re
  have hf (z : ZeroCopy) : Tendsto (fun n => F n z) atTop (𝓝 (wave z).re) := by
    simpa only [F, mul_one] using
      (Complex.continuous_re.tendsto (wave z * 1)).comp ((smoothMultiplier_limit z).const_mul (wave z))
  have hb (n : ℕ) (z : ZeroCopy) : ‖F n z‖ ≤ Real.exp 1 * ‖wave z‖ := by
    change |(wave z * smoothMultiplier n z).re| ≤ _
    calc
      _ ≤ ‖wave z * smoothMultiplier n z‖ := Complex.abs_re_le_norm _
      _ = ‖wave z‖ * ‖smoothMultiplier n z‖ := norm_mul _ _
      _ ≤ ‖wave z‖ * Real.exp 1 := mul_le_mul_of_nonneg_left (smoothMultiplier_bound n z) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hz := tendsto_tsum_of_dominated_convergence (absolute.mul_left (Real.exp 1))
    hf (Eventually.of_forall hb)
  have hp := (smoothAverage_mangoldt_limit mass).sub (smoothAverage_trivial_limit mass)
  have hsum : Summable (fun z : ZeroCopy => (wave z).re) :=
    Summable.of_norm_bounded _ absolute (fun z => Complex.abs_re_le_norm _)
  have heq : (∑' z : ZeroCopy, (wave z).re) = avg normalizedMangoldt - avg trivialAt :=
    tendsto_nhds_unique hz (hp.congr (fun n => (landau n).tsum_eq.symm))
  simpa only [← heq] using hsum.hasSum

end Mertens.Input
