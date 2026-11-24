import Mertens.Concrete

/-! Symmetry of the translated kernel gives the real cosine transform
at real frequencies. -/
noncomputable section
open MeasureTheory Set
namespace Mertens.Input

theorem kernel_reflection (u : ℝ) : kernel (2*omega-u) = kernel u := by
  have hmem : 2*omega-u ∈ window ↔ u ∈ window := by
    change (lo < 2*omega-u ∧ 2*omega-u < hi) ↔ (lo < u ∧ u < hi)
    have ha : 2 * omega - hi = lo := by norm_num [omega,lo,hi]
    have hb : 2 * omega - lo = hi := by norm_num [omega,lo,hi]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have heq : ((2*omega-u-omega)/radius)^2 = ((u-omega)/radius)^2 := by ring
  by_cases hu : u ∈ window
  · simp only [kernel, hmem.mpr hu, hu, if_true, heq]
  · have hn : 2*omega-u ∉ window := fun h => hu (hmem.mp h)
    simp only [kernel, hn, hu, if_false]

private theorem reflect_integral (f : ℝ → ℝ) :
    (∫ u in window, f (2*omega-u)) = ∫ u in window, f u := by
  have conv (g : ℝ → ℝ) : (∫ u in window, g u) = ∫ u in lo..hi, g u := by
    rw [intervalIntegral.integral_of_le (by norm_num [lo,hi]), integral_Ioc_eq_integral_Ioo]
    rfl
  rw [conv, intervalIntegral.integral_comp_sub_left, conv,
    show 2 * omega - hi = lo by norm_num [omega,hi,lo],
    show 2 * omega - lo = hi by norm_num [omega,hi,lo]]

private theorem sine_integral_eq_zero (t : ℝ) :
    (∫ u in window, kernel u * Real.sin (t * (u-omega))) = 0 := by
  let f := fun u : ℝ => kernel u * Real.sin (t * (u-omega))
  have h (u : ℝ) : f (2*omega-u) = -f u := by
    dsimp only [f]
    rw [kernel_reflection, show t * (2*omega-u-omega) = -(t*(u-omega)) by ring,
      Real.sin_neg, mul_neg]
  have H := reflect_integral f
  simp only [h, integral_neg] at H
  change (∫ u in window, f u) = 0
  linarith

/-- The full kernel transform restricted to the real axis is the cosine
transform used in the published low-zero sum. -/
theorem transform_real (mass : ∫ u in window, kernel u = 1) (t : ℝ) :
    transform (t : ℂ) = (ell t : ℂ) := by
  let e := fun u : ℝ => Complex.exp (-Complex.I * (t:ℂ) * (↑(u-omega):ℂ))
  have heCont : Continuous e := by dsimp [e]; fun_prop
  have hre (u : ℝ) : (e u).re = Real.cos (t*(u-omega)) := by
    simp [e, Complex.exp_re, Complex.mul_re, Complex.mul_im]
  have him (u : ℝ) : (e u).im = -Real.sin (t*(u-omega)) := by
    simp [e, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have henorm (u : ℝ) : ‖e u‖ = 1 := by
    simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hK : IntegrableOn kernel window := integrable_of_integral_eq_one mass
  have hφ : IntegrableOn (fun u => (kernel u : ℂ)*e u) window := by
    refine hK.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      hK.aestronglyMeasurable).mul heCont.aestronglyMeasurable) ?_
    exact ae_of_all _ (fun u => by simp [norm_mul, henorm, Real.norm_eq_abs,
      abs_of_nonneg (kernel_nonneg u)])
  change (∫ u in window, (kernel u : ℂ)*e u) = ↑(ell t)
  apply Complex.ext
  · have h := integral_re hφ
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, hre] at h
    exact h.symm
  · have h := integral_im hφ
    simp only [RCLike.im_to_complex, Complex.im_ofReal_mul, him, mul_neg, integral_neg,
      sine_integral_eq_zero t, neg_zero] at h
    exact h.symm

theorem frequency_on_critical_line (z : ZeroCopy) (hz : (rho z).re = 1/2) :
    (rho z - 1/2) / Complex.I = (((rho z).im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.div_I, Complex.mul_re, Complex.mul_im, hz]

end Mertens.Input
