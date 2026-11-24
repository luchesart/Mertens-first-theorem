import Mertens.TestPairing

/-! Fourier coefficient of the smoothed test kernel. The change of variable
v = u − t separates the mollifier from the Logan transform. -/
noncomputable section
open MeasureTheory Set ContinuousLinearMap
open scoped Convolution
namespace Mertens.Input

private def character (z : ZeroCopy) (u : ℝ) := Complex.exp ((1/2 - rho z) * (u : ℂ))

private theorem character_sub (z : ZeroCopy) (u v : ℝ) :
    character z (u-v) = character z u * character z (0-v) := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem smooth_character (n : ℕ) (z : ZeroCopy) (u : ℝ) :
    (∫ t : ℝ, (smoothBump n).normed volume (u-t) • (character z t / rho z)) =
      (character z u / rho z) * smoothMultiplier n z := by
  let g := fun t : ℝ => (smoothBump n).normed volume (u-t) • (character z t / rho z)
  calc
    (∫ t, g t) = ∫ v, g (u-v) := (integral_sub_left_eq_self g volume u).symm
    _ = ∫ v, (character z u / rho z) * ((smoothBump n).normed volume v • character z (0-v)) := by
      apply integral_congr_ae
      apply ae_of_all
      intro v
      dsimp only [g]
      rw [sub_sub_cancel, character_sub z u v]
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      rw [integral_const_mul]
      rfl

private theorem kernel_character (z : ZeroCopy) :
    (∫ u in window, (kernel u : ℂ) * character z u / rho z) = wave z := by
  let α : ℂ := 1/2 - rho z
  have hid : -Complex.I * ((rho z - 1/2)/Complex.I) = α := by
    dsimp only [α]
    field_simp
    ring
  rw [wave, transform, integral_div, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro u
  rw [hid]
  unfold character
  change (kernel u : ℂ) * Complex.exp (α*(u:ℂ)) =
    Complex.exp (α*(omega:ℂ)) * ((kernel u : ℂ) * Complex.exp (α*(((u-omega):ℝ):ℂ)))
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The coefficient of the actual smooth compact test factors into the wave
of the unsmoothed Logan kernel and the Laplace transform of the same bump. -/
theorem smooth_test_fourier (n : ℕ) (z : ZeroCopy) :
    (∫ t : ℝ, (loganTest n t : ℂ) * Complex.exp ((1/2-rho z)*(t:ℂ)) / rho z) =
      wave z * smoothMultiplier n z := by
  let f := fun t : ℝ => character z t / rho z
  have hc : Continuous f := by
    dsimp [f, character]
    fun_prop
  have hf : Integrable (smoothClip.indicator f) :=
    (integrable_indicator_iff (show MeasurableSet smoothClip from measurableSet_Icc)).2
      (hc.continuousOn.integrableOn_compact isCompact_Icc)
  calc
    _ = ∫ t : ℝ, loganTest n t • f t := by
      apply integral_congr_ae (ae_of_all _ (fun t => ?_))
      dsimp [f, character]
      rw [mul_div_assoc]
    _ = _ := test_pair_smul_full n hf
    _ = (∫ u in window, (kernel u : ℂ) * character z u / rho z) * smoothMultiplier n z := by
      rw [← integral_mul_const]
      apply integral_congr_ae (ae_of_all _ (fun u => ?_))
      dsimp only [f]
      rw [smooth_character, Complex.real_smul]
      ring
    _ = _ := by rw [kernel_character]

end Mertens.Input
