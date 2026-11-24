import Mertens.Concrete

/-!
# Unit mass of the shifted Logan kernel

Integrate its defining Bessel series term by term. For the moments of
`(1-y²)^n`, with `y = (u-ω)/ε`, integrating the derivative of
`(u-ω)(1-y²)^(n+1)` gives a two-term recurrence. The factorials in
the Bessel coefficients then turn the sum of the moments into the
ordinary Taylor series for `sinh 280`.
-/

noncomputable section
open Set MeasureTheory
namespace Mertens.Input

private def profile (u : ℝ) := 1 - ((u - omega) / radius)^2
private def profileMoment (n : ℕ) := ∫ u in lo..hi, profile u ^ n

private theorem profile_continuous : Continuous profile := by unfold profile; fun_prop

private theorem profileMoment_succ (n : ℕ) :
    (2 * (n : ℝ) + 3) * profileMoment (n+1) = (2 * (n : ℝ) + 2) * profileMoment n := by
  let f := fun u : ℝ => (u - omega) * profile u ^ (n+1)
  let g := fun u : ℝ => (2*(n:ℝ)+3)*(profile u)^(n+1) - (2*(n:ℝ)+2)*(profile u)^n
  have hder (u : ℝ) : HasDerivAt f (g u) u := by
    have hu := (hasDerivAt_id u).sub_const omega
    have hb := (hasDerivAt_const u (1:ℝ)).sub ((hu.div_const radius).pow 2)
    change HasDerivAt profile _ u at hb
    convert hu.mul (hb.pow (n+1)) using 1
    dsimp [g]
    simp only [Nat.cast_add_one, Nat.cast_ofNat, Nat.add_sub_cancel, pow_one,
      pow_succ (profile u) n, id_eq]
    unfold profile
    ring_nf
  have hg : Continuous g := by
    dsimp [g, profile]
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := lo) (b := hi) (f := f) (f' := g) (fun u _ => hder u) (hg.intervalIntegrable ..)
  have hleft : profile lo = 0 := by norm_num [profile, lo, omega, radius]
  have hright : profile hi = 0 := by norm_num [profile, hi, omega, radius]
  dsimp [f, g] at h
  simp only [hleft, hright, zero_pow (Nat.succ_ne_zero _), mul_zero, sub_zero] at h
  have h₁ : IntervalIntegrable (fun u : ℝ => (2*(n:ℝ)+3) * profile u ^ (n+1)) volume lo hi :=
    (continuous_const.mul (profile_continuous.pow _)).intervalIntegrable ..
  have h₂ : IntervalIntegrable (fun u : ℝ => (2*(n:ℝ)+2) * profile u ^ n) volume lo hi :=
    (continuous_const.mul (profile_continuous.pow _)).intervalIntegrable ..
  rw [intervalIntegral.integral_sub h₁ h₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  exact sub_eq_zero.mp h

private def seriesCoefficient (n : ℕ) : ℝ := ((140 : ℝ)^n / n.factorial)^2
private def besselPolynomial (n : ℕ) (u : ℝ) : ℝ := seriesCoefficient n * profile u ^ n

/-- Integrating the nth Bessel polynomial produces the nth odd sinh coefficient. -/
private theorem scaled_moment (n : ℕ) :
    seriesCoefficient n * profileMoment n = (2 * radius) * (280 : ℝ)^(2*n) / (2*n+1).factorial := by
  induction n with
  | zero =>
    simp [seriesCoefficient, profileMoment]
    norm_num [lo, hi, radius]
  | succ n ih =>
    have hm := profileMoment_succ n
    have hfac : 0 < (n.factorial : ℝ) := by positivity
    have hf2 : 0 < ((2*n+1).factorial : ℝ) := by positivity
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hn2 : 0 < 2 * (n : ℝ) + 3 := by positivity
    have hfrac : profileMoment (n+1) = (2*(n:ℝ)+2) * profileMoment n / (2*(n:ℝ)+3) := by
      apply (eq_div_iff hn2.ne').2
      linarith only [hm]
    have he : 2*(n+1)+1 = ((2*n+1)+1)+1 := by omega
    rw [hfrac, he, Nat.factorial_succ, Nat.factorial_succ, show 2*(n+1) = 2*n+2 by omega, pow_add]
    simp only [seriesCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      pow_succ (140:ℝ) n] at ih ⊢
    field_simp at ih ⊢
    linear_combination (78400 * ((n:ℝ)+1)^2 * (2*n+3)) * ih


private theorem profile_nonneg {u : ℝ} (hu : u ∈ window) : 0 ≤ profile u := by
  have hr : 0 < radius := by norm_num [radius]
  have h₁ : -1 ≤ (u - omega) / radius := by
    apply (le_div_iff₀ hr).2
    linarith only [hu.1, show lo = omega - radius by norm_num [lo, omega, radius]]
  have h₂ : (u - omega) / radius ≤ 1 := by
    apply (div_le_iff₀ hr).2
    linarith only [hu.2, show hi = omega + radius by norm_num [hi, omega, radius]]
  unfold profile
  nlinarith [mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₁)]

private theorem bessel_expansion {u : ℝ} (hu : u ∈ window) :
    besselI0 (280 * Real.sqrt (profile u)) = ∑' n, besselPolynomial n u := by
  unfold besselI0
  apply tsum_congr
  intro n
  have hs : (Real.sqrt (profile u)^n)^2 = profile u ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (profile_nonneg hu)]
  unfold besselPolynomial seriesCoefficient
  rw [show 280 * Real.sqrt (profile u) / 2 = 140 * Real.sqrt (profile u) by ring, mul_pow, ← hs]
  ring

private theorem integral_besselPolynomial (n : ℕ) :
    ∫ u in window, besselPolynomial n u = (2 * radius) * (280:ℝ)^(2*n) / (2*n+1).factorial := by
  rw [← scaled_moment]
  unfold besselPolynomial profileMoment window
  rw [intervalIntegral.integral_of_le (by norm_num [lo,hi]), integral_Ioc_eq_integral_Ioo,
    integral_const_mul]

/-- The concrete compact Logan kernel has mass one by direct integration
of its defining Bessel power series. -/
theorem kernel_mass : ∫ u in window, kernel u = 1 := by
  have hs' := (Real.hasSum_sinh 280).mul_left ((2*radius)/280)
  have hs : HasSum (fun n : ℕ => (∫ u in window, besselPolynomial n u))
      ((2*radius)/280 * Real.sinh 280) := by
    convert hs' using 1
    ext n
    rw [integral_besselPolynomial, pow_succ]
    ring
  have hint (n : ℕ) : IntegrableOn (besselPolynomial n) window := by
    have hc : Continuous (besselPolynomial n) := continuous_const.mul (profile_continuous.pow n)
    exact (hc.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hn (n : ℕ) : (∫ u in window, ‖besselPolynomial n u‖) = ∫ u in window, besselPolynomial n u := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (profile_nonneg hu) n))
  have ha : Summable (fun n : ℕ => ∫ u in window, ‖besselPolynomial n u‖) := by
    simpa only [hn] using hs.summable
  have htotal := (hasSum_integral_of_summable_integral_norm hint ha).unique hs
  calc
    _ = ∫ u in window, (280 / (2 * radius * Real.sinh 280)) * ∑' n, besselPolynomial n u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      change u ∈ window at hu
      rw [kernel, if_pos hu]
      exact congrArg _ (bessel_expansion hu)
    _ = (280 / (2 * radius * Real.sinh 280)) * ((2*radius)/280 * Real.sinh 280) := by
      rw [integral_const_mul, htotal]
    _ = 1 := by
      have hr : radius ≠ 0 := by norm_num [radius]
      have hsinh : Real.sinh 280 ≠ 0 := (Real.sinh_pos_iff.mpr (by norm_num)).ne'
      field_simp

end Mertens.Input
