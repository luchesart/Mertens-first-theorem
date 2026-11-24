import Mertens.Concrete
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

def smoothBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / 8) * (1 / ((n : ℝ) + 1))
  rOut := (1 / 4) * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := mul_lt_mul_of_pos_right (by norm_num) (by positivity)

theorem bump_shrinks : Tendsto (fun n => (smoothBump n).rOut) atTop (𝓝 0) := by
  simpa [smoothBump] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1/4:ℝ)

theorem bump_width (n : ℕ) : (smoothBump n).rOut ≤ 1 / 4 := by
  dsimp [smoothBump]
  have h : 1 / ((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  nlinarith

def smoothClip : Set ℝ := Icc 495 497

theorem clip_covers_test {u v : ℝ} {n : ℕ} (hu : u ∈ window)
    (hv : v ∈ support ((smoothBump n).normed volume)) : u - v ∈ smoothClip := by
  rw [(smoothBump n).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hv
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hv
  have hb := bump_width n
  obtain ⟨h₃,h₄⟩ := hu
  norm_num [lo,hi] at h₃ h₄
  constructor <;> linarith

def smoothValue (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  ((smoothBump n).normed volume ⋆[lsmul ℝ ℝ, volume] smoothClip.indicator f)

/-- The ordinary scalar pairing with the n-th smoothed Logan kernel. -/
def smoothAverage (n : ℕ) (f : ℝ → ℝ) : ℝ := avg (smoothValue n f)

/-- The Laplace transform of the same mollifier at this zero. -/
def smoothMultiplier (n : ℕ) (z : ZeroCopy) : ℂ :=
  ((smoothBump n).normed volume ⋆[lsmul ℝ ℝ, volume]
    (fun t : ℝ => Complex.exp ((1/2-rho z) * (t : ℂ)))) 0

theorem smoothMultiplier_limit (z : ZeroCopy) :
    Tendsto (fun n => smoothMultiplier n z) atTop (𝓝 1) := by
  have hg : Continuous (fun t : ℝ => Complex.exp ((1/2-rho z) * (t : ℂ))) := by fun_prop
  simpa [smoothMultiplier] using
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) bump_shrinks hg 0

theorem smoothMultiplier_bound (n : ℕ) (z : ZeroCopy) :
    ‖smoothMultiplier n z‖ ≤ Real.exp 1 := by
  let g (t : ℝ) := Complex.exp ((1/2-rho z) * (t : ℂ))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hb (t : ℝ) (ht : t ∈ Metric.ball (0:ℝ) (smoothBump n).rOut) :
      dist (g t) 0 ≤ Real.exp 1 := by
    rw [dist_zero_right]
    change ‖Complex.exp ((1 / 2 - rho z) * (t : ℂ))‖ ≤ _
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    obtain ⟨ha,hb⟩ := abs_lt.mp ht
    have hw := bump_width n
    have hβ0 := z.prop.2.1.le
    have hβ1 := z.prop.2.2.1.le
    change 0 ≤ (rho z).re at hβ0
    change (rho z).re ≤ 1 at hβ1
    norm_num [Complex.mul_re]
    by_cases h : 0 ≤ t
    · nlinarith [mul_nonneg hβ0 h]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hβ1) (neg_nonneg.mpr (le_of_not_ge h))]
  simpa only [dist_zero_right] using
    (dist_convolution_le (Real.exp_pos 1).le ((smoothBump n).support_normed_eq (μ:=volume)).subset
      ((smoothBump n).nonneg_normed) ((smoothBump n).integral_normed)
      hg.aestronglyMeasurable hb)


end Mertens.Input
