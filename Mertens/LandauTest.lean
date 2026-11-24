import Mertens.Mollifier

/-! The actual convolution used to test Landau's distributional formula.
Its support is contained in a positive compact interval, including for n=0. -/
noncomputable section
open MeasureTheory Set Function ContinuousLinearMap
open scoped Topology Convolution Pointwise ContDiff
namespace Mertens.Input

def loganTest (n : ℕ) : ℝ → ℝ :=
  kernel ⋆[lsmul ℝ ℝ, volume] (fun t => (smoothBump n).normed volume (-t))

theorem loganTest_eq (n : ℕ) (t : ℝ) :
    loganTest n t = ∫ u in window, kernel u * (smoothBump n).normed volume (u - t) := by
  simp only [loganTest, convolution_def, lsmul_apply, smul_eq_mul, neg_sub]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  simp [kernel, hu]

theorem kernel_integrable (mass : ∫ u in window, kernel u = 1) : Integrable kernel := by
  have hi : Integrable (window.indicator kernel) :=
    (integrable_indicator_iff (measurableSet_Ioo (a:=lo) (b:=hi))).mpr
      (integrable_of_integral_eq_one mass)
  have h : window.indicator kernel = kernel := by
    ext u
    by_cases hu : u ∈ window <;> simp [hu,kernel]
  rwa [h] at hi

private theorem reflected_support (n : ℕ) {t : ℝ}
    (ht : t ∈ support (fun t : ℝ => (smoothBump n).normed volume (-t))) :
    -(1/4) < t ∧ t < 1/4 := by
  have hb : -t ∈ support ((smoothBump n).normed volume) := ht
  rw [(smoothBump n).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg] at hb
  exact abs_lt.mp (lt_of_lt_of_le hb (bump_width n))

theorem loganTest_tsupport (n : ℕ) : tsupport (loganTest n) ⊆ smoothClip := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  obtain ⟨u,hu,v,hv,rfl⟩ := support_convolution_subset (lsmul ℝ ℝ) ht
  have hw : u ∈ window := by
    by_contra hn
    exact hu (by simp [kernel,hn])
  obtain ⟨h₁,h₂⟩ := hw
  obtain ⟨h₃,h₄⟩ := reflected_support n hv
  norm_num [lo,hi] at h₁ h₂
  change 495 ≤ u + v ∧ u + v ≤ 497
  constructor <;> linarith

theorem loganTest_compact (n : ℕ) : HasCompactSupport (loganTest n) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (loganTest_tsupport n)

theorem loganTest_positive_support (n : ℕ) : tsupport (loganTest n) ⊆ Ioi 0 := by
  intro t ht
  exact (by norm_num : (0:ℝ) < 495).trans_le ((loganTest_tsupport n ht).1)

theorem loganTest_smooth (mass : ∫ u in window, kernel u = 1) (n : ℕ) :
    ContDiff ℝ ∞ (loganTest n) := by
  have hs : HasCompactSupport (fun t : ℝ => (smoothBump n).normed volume (-t)) := by
    apply (isCompact_Icc (a := (-1:ℝ)) (b:=1)).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_Icc
    intro t ht
    obtain ⟨h₁,h₂⟩ := reflected_support n ht
    constructor <;> linarith
  exact hs.contDiff_convolution_right (lsmul ℝ ℝ) (kernel_integrable mass).locallyIntegrable
    ((smoothBump n).contDiff_normed.comp contDiff_neg)

end Mertens.Input
