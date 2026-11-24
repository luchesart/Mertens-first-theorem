import Mathlib

/-! # Johnston’s problem on Mertens’ first theorem

Standalone source for Lean and mathlib v4.19.0. The theorem at the end
is conditional on the explicitly listed analytic and published numerical inputs.
Each section identifies its counterpart in the modular project.
-/

/-! ## Mertens/Analysis.lean -/
section
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
end
end

/-! ## Mertens/Components.lean -/
section
/-! # Analytic estimates used in the transfer

Each theorem keeps the analytic input local. In particular no zero computation
or explicit formula is introduced as a global axiom. Indices may distinguish
multiple copies of a zero with the same value. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Mertens

/-- Real contribution to the Hadamard mass from a single zero. -/
def hadamardTerm (z : ℂ) : ℝ := ((z * (1 - z))⁻¹).re

theorem hadamard_term_nonneg (z : ℂ) (h₀ : 0 ≤ z.re) (h₁ : z.re ≤ 1) :
    0 ≤ hadamardTerm z := by
  rw [hadamardTerm, Complex.inv_re]
  apply div_nonneg
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, zero_sub, mul_neg, sub_neg_eq_add]
    exact add_nonneg (mul_nonneg h₀ (sub_nonneg.mpr h₁)) (mul_self_nonneg _)
  · rw [Complex.normSq_eq_norm_sq]
    positivity

theorem hadamard_mass_on_critical_line (z : ℂ) (hz : z.re = 1 / 2) :
    hadamardTerm z = (‖z‖ ^ 2)⁻¹ := by
  have h : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext <;> simp [hz]
    ring
  rw [hadamardTerm, h, Complex.mul_conj, ← Complex.ofReal_inv, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- A finite set of critical-line zeros spends at most the global Hadamard mass.
The identity evaluating that global mass comes from the logarithmic derivative
of the completed zeta function. -/
theorem finite_mass_le {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (strip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (half : ∀ i ∈ s, (ρ i).re = 1 / 2)
    (hs : Summable (fun i => hadamardTerm (ρ i))) :
    (∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹) ≤ ∑' i, hadamardTerm (ρ i) := by
  calc
    (∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹) = ∑ i ∈ s, hadamardTerm (ρ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hadamard_mass_on_critical_line (ρ i) (half i hi)).symm
    _ ≤ ∑' i, hadamardTerm (ρ i) :=
      hs.sum_le_tsum s (fun i _ => hadamard_term_nonneg (ρ i) (strip i).1 (strip i).2)

/-- On the critical line the oscillatory factor has norm one. -/
def criticalWave (γ ω : ℝ) (ell : ℝ → ℝ) : ℂ :=
  Complex.exp (((-(γ * ω) : ℝ) : ℂ) * Complex.I) * (ell γ : ℂ)

theorem criticalWave_norm (γ ω : ℝ) (ell : ℝ → ℝ) :
    ‖criticalWave γ ω ell‖ = |ell γ| := by
  simp [criticalWave, norm_mul, Complex.norm_exp, Complex.mul_re]

/-- Büthe's coefficient and the desired coefficient share the same wave. -/
def butheTerm (ω : ℝ) (b z : ℂ) : ℝ :=
  (b * (z⁻¹ - ((ω : ℂ) * z ^ 2)⁻¹)).re

def firstTerm (b z : ℂ) : ℝ := (b * z⁻¹).re

theorem reweight_low_zeros {ι : Type*} (s : Finset ι) (ρ b : ι → ℂ)
    (ω : ℝ) (hω : 0 < ω) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    (∑ i ∈ s, firstTerm (b i) (ρ i)) ≤
      (∑ i ∈ s, butheTerm ω (b i) (ρ i)) + (∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹) / ω := by
  let corr (i : ι) := b i * ((ω : ℂ) * (ρ i) ^ 2)⁻¹
  have hcorr (i) (hi : i ∈ s) : (corr i).re ≤ (‖ρ i‖ ^ 2)⁻¹ / ω := by
    calc
      (corr i).re ≤ ‖corr i‖ := Complex.re_le_norm _
      _ = ‖b i‖ * (ω * ‖ρ i‖ ^ 2)⁻¹ := by
        simp [corr, norm_mul, norm_pow, abs_of_pos hω]
      _ ≤ 1 * (ω * ‖ρ i‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (hb i hi) (by positivity)
      _ = (‖ρ i‖ ^ 2)⁻¹ / ω := by
        simp [mul_inv_rev, div_eq_mul_inv]
  calc
    (∑ i ∈ s, firstTerm (b i) (ρ i)) =
        (∑ i ∈ s, butheTerm ω (b i) (ρ i)) + ∑ i ∈ s, (corr i).re := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [firstTerm, butheTerm, corr, mul_sub]
    _ ≤ (∑ i ∈ s, butheTerm ω (b i) (ρ i)) + ∑ i ∈ s, (‖ρ i‖ ^ 2)⁻¹ / ω :=
      add_le_add_left (Finset.sum_le_sum hcorr) _
    _ = _ := by rw [Finset.sum_div]

/-- Dusart's relative error decreases along the ray once its logarithm is
at least 247. -/
theorem dusart_uniform_on_ray {y : ℝ} (theta : ℝ → ℝ)
    (hy : 0 < y) (hlog : 247 ≤ Real.log y)
    (hd : ∀ t, y ≤ t → |theta t - t| ≤ (1 / 100 : ℝ) * t / (Real.log t)^2) :
    ∀ t, y ≤ t → |theta t - t| ≤ ((1 / 100 : ℝ) / 247^2) * t := by
  intro t ht
  have ht₀ := hy.trans_le ht
  have hlogt := hlog.trans (Real.log_le_log hy ht)
  have hden : (247 : ℝ)^2 ≤ (Real.log t)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlogt)
      (show 0 ≤ Real.log t + 247 by linarith)]
  calc
    _ ≤ (1 / 100 : ℝ) * t / (Real.log t)^2 := hd t ht
    _ ≤ (1 / 100 : ℝ) * t / 247^2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

/-- The improper integral comparison in the prime-square estimate. Here
`theta` is instantiated by Chebyshev's theta function. The hypotheses are
the partial summation identity and the two-sided relative error bound. -/
theorem square_bound_of_partial_summation {y D Q : ℝ} (theta : ℝ → ℝ)
    (hy : 0 < y) (hD : 0 ≤ D)
    (hθ : ∀ t, y ≤ t → |theta t - t| ≤ D * t)
    (hAbel : Q = -(theta y / y) + (2 * y) *
        (∫ t in Set.Ioi y, theta t / t ^ 3)) :
    Q ≤ 1 + 3 * D := by
  have hstart : 1 - D ≤ theta y / y := by
    apply (le_div_iff₀ hy).2
    nlinarith [(abs_le.mp (hθ y le_rfl)).1]
  have hneg (t : ℝ) (ht : 0 < t) : t ^ (-2 : ℝ) = (t ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.rpow_two]
  have hI : (∫ t in Set.Ioi y, t ^ (-2 : ℝ)) = 1 / y := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy]
    norm_num [one_div]
    exact Real.rpow_neg_one _
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy).const_mul (1 + D)
  have hcomp : (∫ t in Set.Ioi y, theta t / t ^ 3) ≤ (1 + D) * (1 / y) := by
    by_cases hint : IntegrableOn (fun t : ℝ => theta t / t ^ 3) (Set.Ioi y)
    · calc
        (∫ t in Set.Ioi y, theta t / t ^ 3) ≤
            ∫ t in Set.Ioi y, (1 + D) * t ^ (-2 : ℝ) := by
          apply setIntegral_mono_on hint hmajor measurableSet_Ioi
          intro t ht
          have ht₀ : 0 < t := hy.trans ht
          rw [hneg t ht₀, div_le_iff₀ (pow_pos ht₀ 3)]
          calc
            theta t ≤ (1 + D) * t := by nlinarith [(abs_le.mp (hθ t ht.le)).2]
            _ = (1 + D) * (t ^ 2)⁻¹ * t ^ 3 := by field_simp [ht₀.ne']; ring
        _ = (1 + D) * (1 / y) := by rw [integral_const_mul, hI]
    · rw [integral_undef hint]
      positivity
  have h := mul_le_mul_of_nonneg_left hcomp (by positivity : 0 ≤ 2 * y)
  have hscale : 2 * y * ((1 + D) * (1 / y)) = 2 * (1 + D) := by
    field_simp [hy.ne']; ring
  rw [hscale] at h
  linarith

/-- The normalized trivial-zero series, indexed by the zeros -2,-4,... . -/
theorem trivial_zero_tail_le {u : ℝ} (hu : 0 < u) :
    (∑' n : ℕ, Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) / (2 * (n : ℝ) + 3)) ≤
      Real.exp (-(5 / 2) * u) / (1 - Real.exp (-2 * u)) := by
  let c := Real.exp (-(5 / 2) * u)
  let q := Real.exp (-2 * u)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq' : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hq hq').mul_left c
  let f (n : ℕ) := Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) / (2 * (n : ℝ) + 3)
  have hbound (n : ℕ) : f n ≤ c * q ^ n := by
    have hnum : Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) = c * q ^ n := by
      dsimp [c, q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    dsimp [f]
    rw [hnum]
    apply div_le_self (mul_nonneg hc (pow_nonneg hq n))
    linarith [Nat.cast_nonneg (α := ℝ) n]
  change (∑' n, f n) ≤ c / (1 - q)
  have hs : Summable f := Summable.of_nonneg_of_le
    (fun n => div_nonneg (Real.exp_pos _).le (by positivity)) hbound hg.summable
  calc
    (∑' n, f n) ≤ ∑' n : ℕ, c * q ^ n := hs.tsum_le_tsum hbound hg.summable
    _ = c / (1 - q) := by simpa [div_eq_mul_inv] using hg.tsum_eq

end Mertens
end
end

/-! ## Mertens/Concrete.lean -/
section
/-! The specific kernel, zeta zeros (with multiplicity) and prime-power sums
used by the Johnston bound. The windows and frequencies are fixed, not
parameters that can be tuned after the finite zero sum has been evaluated. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical

namespace Mertens.Input

def omega : ℝ := 495702833137 / 10^9
def radius : ℝ := 28 / 10^9
def lo : ℝ := 495702833109 / 10^9
def hi : ℝ := 495702833165 / 10^9
def window := Ioo lo hi

/-- Modified Bessel function I₀, in its nonnegative power series. -/
def besselI0 (x : ℝ) : ℝ := ∑' n : ℕ, ((x / 2) ^ n / (n.factorial : ℝ)) ^ 2

/-- Shifted Logan kernel. Changing the values at the two endpoints does not
affect any integrals below. -/
def kernel (u : ℝ) : ℝ :=
  if u ∈ window then
    280 / (2 * radius * Real.sinh 280) *
      besselI0 (280 * Real.sqrt (1 - ((u - omega) / radius)^2))
  else 0

theorem kernel_nonneg (u : ℝ) : 0 ≤ kernel u := by
  unfold kernel
  split_ifs
  · apply mul_nonneg
    · have h : 0 < Real.sinh 280 := Real.sinh_pos_iff.mpr (by norm_num)
      unfold radius
      positivity
    · exact tsum_nonneg (fun n => sq_nonneg _)
  · exact le_rfl

def avg (f : ℝ → ℝ) : ℝ := ∫ u in window, kernel u * f u

/-- Cosine transform of the translated-back even kernel at a real ordinate. -/
def ell (t : ℝ) : ℝ := ∫ u in window, kernel u * Real.cos (t * (u - omega))

theorem abs_ell_le_one (mass : ∫ u in window, kernel u = 1) (t : ℝ) :
    |ell t| ≤ 1 := by
  have hki : IntegrableOn kernel window := integrable_of_integral_eq_one mass
  calc
    |ell t| ≤ ∫ u in window, ‖kernel u * Real.cos (t * (u - omega))‖ := by
      simpa only [ell, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict window)
          (fun u : ℝ => kernel u * Real.cos (t * (u - omega))))
    _ ≤ ∫ u in window, kernel u := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun u => norm_nonneg _)) hki
      exact ae_of_all _ (fun u => by
        change ‖kernel u * Real.cos (t * (u - omega))‖ ≤ kernel u
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg u)]
        exact mul_le_of_le_one_right (kernel_nonneg u) (abs_le.mpr
          ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
    _ = 1 := mass

/-- For a holomorphic nonzero germ, its order is the smallest derivative
index with nonzero derivative. An index j in [0,order) counts one copy. -/
def zeroOrder (z : ℂ) : ℕ := sInf {n : ℕ | iteratedDeriv n riemannZeta z ≠ 0}

def ZeroCopy := {p : ℂ × ℕ // riemannZeta p.1 = 0 ∧ 0 < p.1.re ∧
  p.1.re < 1 ∧ p.2 < zeroOrder p.1}

def rho (z : ZeroCopy) : ℂ := z.val.1

def lowBand : Set ZeroCopy := {z | |(rho z).im| ≤ 4 * 10^9}

def lowWeight (z : ZeroCopy) : ℂ :=
  Complex.exp (((-((rho z).im * omega) : ℝ) : ℂ) * Complex.I) * (ell (rho z).im : ℂ)

/-- Full transform on or off the critical line. The integral uses u-omega
to match the phase convention in the published zero computation. -/
def transform (z : ℂ) : ℂ :=
  ∫ u in window, (kernel u : ℂ) * Complex.exp (-Complex.I * z * (↑(u - omega) : ℂ))

def wave (z : ZeroCopy) : ℂ := Complex.exp ((1/2 - rho z) * (omega : ℂ)) *
  transform ((rho z - 1/2) / Complex.I) / rho z

def middle : ℝ :=
  ∑' z : ZeroCopy, if 4 * 10^9 < |(rho z).im| ∧ |(rho z).im| ≤ 10^10 then (wave z).re else 0

def high : ℝ :=
  ∑' z : ZeroCopy, if 10^10 < |(rho z).im| then (wave z).re else 0

def chebyshevTheta (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), if n.Prime then Real.log n else 0

def squareAt (u : ℝ) : ℝ :=
  let y := Real.sqrt (Real.exp u)
  y * ∑' p : Nat.Primes, if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0

def primePowerTail (k : ℕ) (x : ℝ) : ℝ :=
  ∑' p : Nat.Primes, if x < (p : ℝ)^k then Real.log (p : ℝ) / (p : ℝ)^k else 0

def higherAt (u : ℝ) : ℝ :=
  Real.sqrt (Real.exp u) * ∑' j : ℕ, primePowerTail (j + 3) (Real.exp u)

def trivialAt (u : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(2 * (n : ℝ) + 5 / 2) * u) / (2 * (n : ℝ) + 3)

/-- Any uniform cap on a nonnegative summand passes to the actual integral
with the Logan probability kernel. -/
theorem avg_le {f : ℝ → ℝ} {b : ℝ} (mass : ∫ u in window, kernel u = 1)
    (hf : ∀ u, 0 ≤ f u) (hb : ∀ u ∈ window, f u ≤ b) : avg f ≤ b := by
  have hki : IntegrableOn kernel window := integrable_of_integral_eq_one mass
  calc
    avg f ≤ ∫ u in window, kernel u * b := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun u => mul_nonneg (kernel_nonneg u) (hf u)))
        (hki.mul_const b)
      filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := lo) (b := hi))] with u hu
      exact mul_le_mul_of_nonneg_left (hb u hu) (kernel_nonneg u)
    _ = b := by rw [integral_mul_const, mass, one_mul]

theorem squareAt_nonneg (u : ℝ) : 0 ≤ squareAt u := by
  unfold squareAt
  apply mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg _)
  intro p
  split_ifs
  · apply div_nonneg _ (sq_nonneg _)
    exact Real.log_nonneg (by exact_mod_cast p.prop.one_le)
  · exact le_rfl

theorem higherAt_nonneg (u : ℝ) : 0 ≤ higherAt u := by
  unfold higherAt
  apply mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg _)
  intro j
  apply tsum_nonneg
  intro p
  split_ifs
  · apply div_nonneg _ (pow_nonneg (Nat.cast_nonneg p.val) _)
    exact Real.log_nonneg (by exact_mod_cast p.prop.one_le)
  · exact le_rfl

theorem trivialAt_nonneg (u : ℝ) : 0 ≤ trivialAt u := by
  apply tsum_nonneg
  intro n
  exact div_nonneg (Real.exp_pos _).le (by positivity)

end Mertens.Input
end
end

/-! ## Mertens/Budget.lean -/
section
/-!
# Exact arithmetic for the first Mertens error

All decimals in the paper are rational numbers. This module uses signed
numerators and positive denominators, without any floating point arithmetic
or dependencies beyond Lean's standard library. There is no need to reduce
fractions to lowest terms: their cross products determine equality and order.
The companion real-valued proof interprets these same expressions in ℝ.
-/

set_option exponentiation.threshold 1024
set_option maxRecDepth 4096

namespace Mertens.Budget

structure Fraction where
  num : Int
  den : Nat
  positive : 0 < den

def frac (n : Int) (d : Nat) (h : 0 < d := by decide) : Fraction :=
  ⟨n, d, h⟩

instance : Add Fraction where
  add a b :=
    ⟨a.num * (b.den : Int) + b.num * (a.den : Int),
     a.den * b.den, Nat.mul_pos a.positive b.positive⟩

instance : Mul Fraction where
  mul a b :=
    ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.positive b.positive⟩

/-- Equality as numbers, irrespective of the chosen denominators. -/
abbrev same (a b : Fraction) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

/-- Strict order by cross multiplication. -/
abbrev less (a b : Fraction) : Prop :=
  a.num * (b.den : Int) < b.num * (a.den : Int)

def center         := frac 495702833137 1000000000
def radius         := frac 28 1000000000
def leftEndpoint   := frac 495702833109 1000000000
def rightEndpoint  := frac 495702833165 1000000000

/-- The window uses exactly the center and radius of Büthe's computation. -/
theorem window_endpoints :
    same (leftEndpoint + radius) center ∧ same (center + radius) rightEndpoint := by
  decide

theorem cutoff_parameters :
    same (radius * frac (10^10) 1) (frac 280 1) ∧
    same (frac 4 10 * frac (10^10) 1) (frac (4 * 10^9) 1) := by
  decide

def publishedCap   := frac (-100015419) 100000000
def massCap        := frac 46192 1000000
def coefficientCap := frac 46192000 495702833137
def middleCap      := frac 116 (10^13)
def highCap        := frac 109 (10^14)
def squareExcess   := frac 3 (100 * 247^2)
def squareCap      := frac 1 1 + squareExcess
def higherCap      := frac 1 (10^29)
def trivialCap     := frac 1 (10^500)
def meanTarget     := frac (-6051) (10^8)
def witnessTarget  := frac (-605) (10^7)

/-- The cap for the removed coefficient is the mass cap divided by ω. -/
theorem coefficient_cap_scaling : same (coefficientCap * center) massCap := by
  decide

/-- The square-tail bound is 1 + 3D, with D = 0.01/247². -/
theorem square_excess_scaling :
    same squareExcess (frac 3 1 * frac 1 (100 * 247^2)) := by
  decide

/-- The exact upper bound after combining all seven estimates. -/
def upperBound : Fraction :=
  publishedCap + coefficientCap + middleCap + highCap + squareCap + higherCap + trivialCap

/-- Even the upward-rounded inputs leave a mean strictly below −0.00006051. -/
theorem upperBound_lt : less upperBound meanTarget := by
  decide

theorem meanTarget_lt_witnessTarget : less meanTarget witnessTarget := by
  decide

end Mertens.Budget
end

/-! ## Mertens/RealBudget.lean -/
section
set_option exponentiation.threshold 1024

namespace Mertens.Budget

/-- Interpret a positive-denominator fraction as an actual real number. -/
noncomputable def toReal (q : Fraction) : ℝ := (q.num : ℝ) / (q.den : ℝ)

theorem toReal_add (a b : Fraction) :
    toReal (a + b) = toReal a + toReal b := by
  have ha : (0 : ℝ) < a.den := by exact_mod_cast a.positive
  have hb : (0 : ℝ) < b.den := by exact_mod_cast b.positive
  change (((a.num * (b.den : ℤ) + b.num * (a.den : ℤ) : ℤ) : ℝ) /
    ((a.den * b.den : ℕ) : ℝ)) = (a.num : ℝ) / a.den + (b.num : ℝ) / b.den
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]

theorem toReal_lt {a b : Fraction} (h : less a b) : toReal a < toReal b := by
  have ha : (0 : ℝ) < a.den := by exact_mod_cast a.positive
  have hb : (0 : ℝ) < b.den := by exact_mod_cast b.positive
  apply (div_lt_div_iff₀ ha hb).2
  change a.num * (b.den : ℤ) < b.num * (a.den : ℤ) at h
  exact_mod_cast h

/-- The real form of the exact common-denominator computation. -/
theorem real_upperBound_lt : toReal upperBound < -(6051/100000000 : ℝ) := by
  calc
    toReal upperBound < toReal meanTarget := toReal_lt upperBound_lt
    _ = -(6051/100000000 : ℝ) := by norm_num [toReal, meanTarget, frac]

end Mertens.Budget

namespace Mertens

open Budget

/-- Add the individual analytic estimates and Büthe's published input.
The argument uses one-sided errors throughout, as the goal is an upper
bound. The scalar comparisons are proved in the standard library module. -/
theorem mean_lt_target {I published low middle high squares higher trivial : ℝ}
    (hsplit : I ≤ low + middle + high + squares + higher + trivial)
    (hpub : published ≤ -(100015419/100000000 : ℝ))
    (hlow : low - published ≤ (46192/1000000 : ℝ)/(495702833137/1000000000 : ℝ))
    (hmiddle : middle ≤ 116/(10 : ℝ)^13)
    (hhigh : high ≤ 109/(10 : ℝ)^14)
    (hsquares : squares ≤ 1 + 3/(100*(247 : ℝ)^2))
    (hhigher : higher ≤ 1/(10 : ℝ)^29)
    (htrivial : trivial ≤ 1/(10 : ℝ)^500) :
    I < -(605/10000000 : ℝ) := by
  have hlow' : low ≤ toReal publishedCap + toReal coefficientCap := by
    norm_num [toReal, publishedCap, coefficientCap, frac] at hpub hlow ⊢
    linarith only [hpub, hlow]
  have hm : middle ≤ toReal middleCap := by
    norm_num [toReal, middleCap, frac] at hmiddle ⊢
    exact hmiddle
  have hh : high ≤ toReal highCap := by
    norm_num [toReal, highCap, frac] at hhigh ⊢
    exact hhigh
  have hs : squares ≤ toReal squareCap := by
    unfold squareCap
    rw [toReal_add]
    norm_num [toReal, squareExcess, frac] at hsquares ⊢
    exact hsquares
  have hp : higher ≤ toReal higherCap := by
    norm_num [toReal, higherCap, frac] at hhigher ⊢
    exact hhigher
  have ht : trivial ≤ toReal trivialCap := by
    norm_num [toReal, trivialCap, frac] at htrivial ⊢
    exact htrivial
  have hi : I ≤ toReal upperBound := by
    unfold upperBound
    simp only [toReal_add]
    exact le_trans hsplit
      (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hlow' hm) hh) hs) hp) ht)
  have tight := lt_of_le_of_lt hi (toReal_lt upperBound_lt)
  have hw := lt_trans tight (toReal_lt meanTarget_lt_witnessTarget)
  norm_num [toReal, witnessTarget, frac] at hw ⊢
  exact hw

end Mertens
end

/-! ## Mertens/Exponential.lean -/
section
/-!
# Exponentiating the window

Dyadic range reduction turns both endpoint estimates into comparisons at
arguments less than one. Only mathlib's bounds on `log 2` and the real
exponential series are needed. Every numerical comparison is rational.
-/

namespace Mertens

private theorem exp_dyadic_shift (n : ℕ) (v : ℝ) :
    Real.exp ((n : ℝ) * Real.log 2 + v) = (2 : ℝ) ^ n * Real.exp v := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem exp_remainder_upper :
    Real.exp ((513 : ℝ) / 5000) < 110805 / 100000 := by
  have h := Real.exp_bound' (x := (513 : ℝ) / 5000)
    (by norm_num) (by norm_num) (n := 4) (by decide)
  apply lt_of_le_of_lt h
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem exp_remainder_lower :
    (14769 : ℝ) / 10000 ≤ Real.exp (1989 / 5000) := by
  have h := Real.sum_le_exp_of_nonneg (x := (1989 : ℝ) / 5000) (by norm_num) 3
  apply le_trans _ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The real endpoint is below the decimal upper bound in Theorem 1. -/
theorem exp_upper_endpoint_lt :
    Real.exp ((495702833165 : ℝ) / 10 ^ 9) < (191 / 100 : ℝ) * 10 ^ 215 := by
  have hu : (495702833165 : ℝ) / 10 ^ 9 <
      ((715 : ℕ) : ℝ) * Real.log 2 + 513 / 5000 := by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  calc
    _ < Real.exp (((715 : ℕ) : ℝ) * Real.log 2 + 513 / 5000) := Real.exp_lt_exp.mpr hu
    _ = (2 : ℝ) ^ 715 * Real.exp (513 / 5000) := exp_dyadic_shift 715 _
    _ < (2 : ℝ) ^ 715 * (110805 / 100000) :=
      mul_lt_mul_of_pos_left exp_remainder_upper (by positivity)
    _ < _ := by norm_num

/-- The short interval already has the stated length at the lower endpoint. -/
theorem length_lower_endpoint_gt :
    (26 / 10 : ℝ) * 10 ^ 103 <
      (60 / 10 ^ 6 : ℝ) * Real.exp (((495702833109 : ℝ) / 10 ^ 9) / 2) := by
  have hu : ((357 : ℕ) : ℝ) * Real.log 2 + 1989 / 5000 <
      ((495702833109 : ℝ) / 10 ^ 9) / 2 := by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have h :
      (2 : ℝ) ^ 357 * (14769 / 10000) <
        Real.exp (((495702833109 : ℝ) / 10 ^ 9) / 2) := by
    calc
      _ ≤ (2 : ℝ) ^ 357 * Real.exp (1989 / 5000) :=
        mul_le_mul_of_nonneg_left exp_remainder_lower (by positivity)
      _ = Real.exp (((357 : ℕ) : ℝ) * Real.log 2 + 1989 / 5000) :=
        (exp_dyadic_shift 357 _).symm
      _ < _ := Real.exp_lt_exp.mpr hu
  calc
    _ < (60 / 10 ^ 6 : ℝ) * ((2 : ℝ) ^ 357 * (14769 / 10000)) := by norm_num
    _ < _ := mul_lt_mul_of_pos_left h (by norm_num)


private theorem two_pow_lt_exp {x : ℝ} (n : ℕ) (h : (n : ℝ) * Real.log 2 < x) :
    (2 : ℝ) ^ n < Real.exp x := by
  have hh := Real.exp_lt_exp.mpr h
  rwa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh

private theorem exp_neg_lt_dyadic {x : ℝ} (n : ℕ) (h : (n : ℝ) * Real.log 2 < x) :
    Real.exp (-x) < 1 / (2 : ℝ) ^ n := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by positivity) (two_pow_lt_exp n h)

/-- Dusart's threshold and the coarser logarithmic square threshold on
the whole log window. -/
theorem dusart_range {u : ℝ} (hu : 495 ≤ u) :
    7713133853 < Real.exp (u / 3) ∧ 247 < u / 2 := by
  constructor
  · apply lt_trans _ (two_pow_lt_exp 33 (by
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]))
    norm_num
  · linarith

/-- The sum of the two higher-power majorants in §4 after normalization. -/
theorem higher_majorant_lt {u : ℝ} (hu : 495 ≤ u) (hu' : u ≤ 496) :
    (4 + 4 * (u / 3 + 1)) * Real.exp (-u / 6) < 1 / (10 : ℝ) ^ 29 := by
  have hh := exp_neg_lt_dyadic (x := u / 6) 110 (by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9])
  rw [← neg_div] at hh
  calc
    _ ≤ 670 * Real.exp (-u / 6) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    _ < 670 * (1 / (2 : ℝ) ^ 110) := mul_lt_mul_of_pos_left hh (by norm_num)
    _ < _ := by norm_num

/-- Geometric tail of the normalized contributions of the trivial zeros. -/
theorem trivial_majorant_lt {u : ℝ} (hu : 495 ≤ u) :
    Real.exp (-5 * u / 2) / (1 - Real.exp (-2 * u)) < 1 / (10 : ℝ) ^ 500 := by
  have hn := exp_neg_lt_dyadic (x := 5 * u / 2) 1700 (by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9])
  have hd := exp_neg_lt_dyadic (x := 2 * u) 1 (by
    norm_num only [Nat.cast_one, one_mul]
    linarith [Real.log_two_lt_d9])
  rw [show -(5 * u / 2) = -5 * u / 2 by ring] at hn
  rw [show -(2 * u) = -2 * u by ring, pow_one] at hd
  apply (div_lt_iff₀ (by linarith : 0 < 1 - Real.exp (-2 * u))).2
  calc
    _ < 1 / (2 : ℝ) ^ 1700 := hn
    _ < 1 / (10 : ℝ) ^ 500 * (1 / 2) := by norm_num
    _ ≤ 1 / (10 : ℝ) ^ 500 * (1 - Real.exp (-2 * u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)


/-- Exponential envelope used by the alternative Rankin estimate for higher powers. -/
theorem rankin_majorant_lt {u : ℝ} (hu : 495 ≤ u) :
    51000 * Real.exp (-(4 / 25) * u) < 1 / (10 : ℝ) ^ 29 := by
  have hh := exp_neg_lt_dyadic (x := (4 / 25) * u) 114 (by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9])
  rw [← neg_mul] at hh
  calc
    _ < 51000 * (1 / (2 : ℝ) ^ 114) := mul_lt_mul_of_pos_left hh (by norm_num)
    _ < _ := by norm_num

end Mertens
end

/-! ## Mertens/ZeroTailBounds.lean -/
section
/-!
The scalar sides of Büthe's Lemmas 6.2 and 6.3 at the parameters used in the
paper. Range reduction to powers of two keeps the exponential estimates
short enough for exact rational Taylor comparisons in the kernel.
-/

namespace Mertens

noncomputable def middleMajorant : ℝ :=
  (1 + 11 * 280 * (28/10^9)) / (Real.pi * 280 * ((4/10)^2)) *
    Real.log (10^10) * Real.cosh (280 * Real.sqrt (1 - (4/10)^2)) / Real.sinh 280

noncomputable def highMajorant : ℝ :=
  (32/100) * Real.exp ((495702833137/10^9)/2 + (71/100)*Real.sqrt (280*(28/10^9))) /
    Real.sinh 280 * Real.log (3*280) * Real.log (10^10)

private theorem exp_upper_by_series {u r B : ℝ} {n m : ℕ}
    (hu : u ≤ n * Real.log 2 + r) (hr : 0 ≤ r) (hr' : r ≤ 1) (hm : 0 < m)
    (hB : (2 : ℝ)^n * ((∑ i ∈ Finset.range m, r^i / i.factorial) +
      r^m * (m + 1) / (m.factorial * m)) < B) : Real.exp u < B := by
  have h := Real.exp_bound' hr hr' hm
  calc
    Real.exp u ≤ Real.exp ((n : ℝ) * Real.log 2 + r) := Real.exp_le_exp.mpr hu
    _ = 2^n * Real.exp r := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
    _ < _ := hB

private theorem exp_lower_by_series {u r B : ℝ} {n m : ℕ}
    (hu : n * Real.log 2 + r ≤ u) (hr : 0 ≤ r)
    (hB : B < (2 : ℝ)^n * (∑ i ∈ Finset.range m, r^i / i.factorial)) :
    B < Real.exp u := by
  calc
    B < _ := hB
    _ ≤ (2 : ℝ)^n * Real.exp r :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hr m) (by positivity)
    _ = Real.exp ((n : ℝ) * Real.log 2 + r) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr hu

private theorem denominator_lower : (2001 : ℝ) * 10^118 < Real.sinh 280 := by
  have h : (4002 : ℝ) * 10^118 + 1 < Real.exp 280 := by
    apply exp_lower_by_series (n := 403) (m := 7) (r := 66168/100000)
    · norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  have hneg : Real.exp (-280) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [Real.sinh_eq]
  linarith

private theorem cosh_upper :
    Real.cosh (280 * Real.sqrt (1 - (4/10)^2)) < (1412 : ℝ)*10^108 := by
  have hroot : Real.sqrt (1 - (4/10)^2) ≤ 9165152/10000000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h : Real.exp (280 * Real.sqrt (1 - (4/10)^2)) < (2823 : ℝ)*10^108 := by
    apply exp_upper_by_series (n := 370) (m := 5) (r := 16/100)
    · norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_gt_d9]
    · norm_num
    · norm_num
    · decide
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  have hneg : Real.exp (-(280 * Real.sqrt (1 - (4/10)^2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  rw [Real.cosh_eq]
  linarith

private theorem high_exp_upper :
    Real.exp ((495702833137/10^9)/2 + (71/100)*Real.sqrt (280*(28/10^9))) <
      (438 : ℝ)*10^105 := by
  have hroot : Real.sqrt (280 * (28/10^9)) ≤ 28/10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  apply exp_upper_by_series (n := 357) (m := 6) (r := 3999/10000)
  · norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  · norm_num
  · norm_num
  · decide
  · norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem log_height_upper : Real.log (10^10) < 2303/100 := by
  apply (Real.log_lt_iff_lt_exp (by positivity)).2
  apply exp_lower_by_series (n := 33) (m := 5) (r := 155/1000)
  · norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  · norm_num
  · norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem log_840_upper : Real.log (3*280) < 674/100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  apply exp_lower_by_series (n := 9) (m := 5) (r := 1/2)
  · norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  · norm_num
  · norm_num [Finset.sum_range_succ, Nat.factorial]

theorem middleMajorant_lt : middleMajorant < 116/(10 : ℝ)^13 := by
  have hden : 0 < Real.sinh 280 := lt_trans (by positivity) denominator_lower
  have hp : 0 < Real.pi * 280 * ((4/10 : ℝ)^2) := by positivity
  have h0 : 0 ≤ Real.log (10^10) := Real.log_nonneg (by norm_num)
  have hc0 : 0 ≤ Real.cosh (280 * Real.sqrt (1 - (4/10)^2)) :=
    (Real.cosh_pos _).le
  unfold middleMajorant
  rw [div_lt_iff₀ hden]
  calc
    _ ≤ (1 + 11 * 280 * (28/10^9 : ℝ)) / ((314/100)*280*((4/10)^2)) *
          (2303/100) * (1412*10^108) := by
      gcongr <;> first | exact log_height_upper.le | exact cosh_upper.le | linarith [Real.pi_gt_d2]
    _ < (116/(10 : ℝ)^13) * (2001*10^118) := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left denominator_lower.le (by positivity)

theorem highMajorant_lt : highMajorant < 109/(10 : ℝ)^14 := by
  have hden : 0 < Real.sinh 280 := lt_trans (by positivity) denominator_lower
  have h0 : 0 ≤ Real.log (10^10) := Real.log_nonneg (by norm_num)
  have h1 : 0 ≤ Real.log (3*280) := Real.log_nonneg (by norm_num)
  unfold highMajorant
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hden]
  calc
    _ ≤ (32/100 : ℝ) * (438*10^105) * (674/100) * (2303/100) := by
      gcongr <;> first | exact high_exp_upper.le | exact log_840_upper.le | exact log_height_upper.le
    _ < (109/(10 : ℝ)^14) * (2001*10^118) := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left denominator_lower.le (by positivity)

end Mertens
end

/-! ## Mertens/Transfer.lean -/
section
/-! Transfer from explicit source statements to the actual first Mertens error.
The inputs below retain the fixed kernel, the zeta zeros with multiplicities,
and the arithmetical functions. They cannot be instantiated by choosing
arbitrary real numbers to make a budget inequality true. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens.Input

def lowSum (s : Finset ZeroCopy) : ℝ := ∑ z ∈ s, firstTerm (lowWeight z) (rho z)
def publishedSum (s : Finset ZeroCopy) : ℝ := ∑ z ∈ s, butheTerm omega (lowWeight z) (rho z)

theorem low_correction (finite : lowBand.Finite) (mass : ∫ u in window, kernel u = 1)
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2)
    (hmass : HasSum (fun z : ZeroCopy => hadamardTerm (rho z))
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)))
    (hconst : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) ≤ 46192/1000000) :
    lowSum finite.toFinset - publishedSum finite.toFinset ≤ (46192/1000000)/omega := by
  have hω : 0 < omega := by norm_num [omega]
  have hhalf (z : ZeroCopy) (hz : z ∈ finite.toFinset) : (rho z).re = 1/2 := by
    apply critical
    have hh : |(rho z).im| ≤ 4 * 10^9 := finite.mem_toFinset.mp hz
    exact hh.trans (by norm_num)
  have hmass' := finite_mass_le finite.toFinset rho
    (fun z => ⟨z.property.2.1.le, z.property.2.2.1.le⟩) hhalf hmass.summable
  rw [hmass.tsum_eq] at hmass'
  have h := reweight_low_zeros finite.toFinset rho lowWeight omega hω (fun z _ => by
    change ‖criticalWave (rho z).im omega ell‖ ≤ _
    rw [criticalWave_norm]
    exact abs_ell_le_one mass _)
  have hh := div_le_div_of_nonneg_right (hmass'.trans hconst) hω.le
  dsimp [lowSum, publishedSum]
  linarith only [h, hh]

theorem window_coarse {u : ℝ} (hu : u ∈ window) : 495 ≤ u ∧ u ≤ 496 :=
  ⟨le_trans (by norm_num [lo]) hu.1.le, le_trans hu.2.le (by norm_num [hi])⟩

/-- The square-tail comparison uses Dusart only at t≥sqrt(exp u) on the
window. This transports his stated global estimate to the relative scale
of the Abel integral. -/
theorem relative_theta (dusart : ∀ t : ℝ, 7713133853 ≤ t →
    |chebyshevTheta t - t| ≤ (1/100) * t / (Real.log t)^2)
    {u t : ℝ} (hu : u ∈ window) (ht : Real.sqrt (Real.exp u) ≤ t) :
    |chebyshevTheta t - t| ≤ (1/(100 * 247^2)) * t := by
  have h495 := (window_coarse hu).1
  rw [← Real.exp_half] at ht
  have hcut : Real.exp (u/3) ≤ Real.exp (u/2) := Real.exp_le_exp.mpr (by linarith)
  have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
  have hh := dusart t ((dusart_range h495).1.le.trans (hcut.trans ht))
  have hlog : u/2 ≤ Real.log t := by simpa using Real.log_le_log (Real.exp_pos _) ht
  have hlog' : (247:ℝ) ≤ Real.log t := (dusart_range h495).2.le.trans hlog
  apply hh.trans
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log t))).2
  have hs : (247:ℝ)^2 ≤ (Real.log t)^2 := by nlinarith [sq_nonneg (Real.log t - 247)]
  calc
    1 / 100 * t = (1 / (100 * 247 ^ 2) * t) * 247^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Leaf-independent arithmetic and analytic assembly. The sharper source
interface in Main discharges the square, higher-power and decomposition
arguments from their definitions. -/
theorem transfer_to_witness (finite : lowBand.Finite)
    (mass : ∫ u in window, kernel u = 1)
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2)
    (hmass : HasSum (fun z : ZeroCopy => hadamardTerm (rho z))
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)))
    (hconst : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) ≤ 46192/1000000)
    (buthe : publishedSum finite.toFinset ≤ -(100015419/100000000 : ℝ))
    (mid : middle ≤ middleMajorant) (upper : high ≤ highMajorant)
    (sq : ∀ u ∈ window, squareAt u ≤ 1 + 3/(100*(247:ℝ)^2))
    (pow : ∀ u ∈ window, higherAt u ≤ 1/(10:ℝ)^29)
    (formula : weightedMean kernel lo hi = lowSum finite.toFinset + middle + high +
      avg squareAt + avg higherAt + avg trivialAt) :
    ∃ x : ℝ, 0 < x ∧ lo < Real.log x ∧ Real.log x < hi ∧
      Real.sqrt x * error x < -(605/10^7 : ℝ) := by
  have ht (u : ℝ) (hu : u ∈ window) : trivialAt u ≤ 1/(10:ℝ)^500 := by
    have h495 := (window_coarse hu).1
    exact (trivial_zero_tail_le (by linarith : 0 < u)).trans
      (by simpa only [neg_div, neg_mul, mul_div_assoc, div_mul_eq_mul_div] using
        (trivial_majorant_lt h495).le)
  have hcoeff := low_correction finite mass critical hmass hconst
  norm_num [omega] at hcoeff
  have hm := mean_lt_target formula.le buthe (by norm_num; exact hcoeff)
    (mid.trans middleMajorant_lt.le) (upper.trans highMajorant_lt.le)
    (avg_le mass squareAt_nonneg sq) (avg_le mass higherAt_nonneg pow)
    (avg_le mass trivialAt_nonneg ht)
  apply witness_of_mean_lt (fun u _ => kernel_nonneg u) mass (by norm_num)
  norm_num at hm ⊢
  exact hm

theorem consequences {x : ℝ} (hx : 0 < x) (hl : lo < Real.log x) (hr : Real.log x < hi)
    (hE : Real.sqrt x * error x < -(605/10^7:ℝ)) :
    x < (191/100 : ℝ)*10^215 ∧ (26/10:ℝ)*10^103 < (60/10^6)*Real.sqrt x ∧
      ∀ t ∈ Icc (x - (60/10^6)*Real.sqrt x) x, error t < 0 := by
  have hxr : x < Real.exp hi := by simpa [Real.exp_log hx] using Real.exp_lt_exp.mpr hr
  have hxl : Real.exp (lo/2) < Real.sqrt x := by
    have hh := Real.exp_lt_exp.mpr (show lo / 2 < Real.log x / 2 by linarith)
    simpa only [Real.exp_half, Real.exp_log hx] using hh
  have hs : 1 ≤ Real.sqrt x := by
    have h : Real.exp 0 ≤ Real.exp (lo/2) := Real.exp_le_exp.mpr (by norm_num [lo])
    exact (by simpa only [Real.exp_zero] using h : 1 ≤ Real.exp (lo/2)).trans hxl.le
  exact ⟨hxr.trans exp_upper_endpoint_lt,
    length_lower_endpoint_gt.trans (mul_lt_mul_of_pos_left hxl (by norm_num)),
    negative_left_interval hx hs hE⟩

end Mertens.Input
end
end

/-! ## Mertens/PrimePowers.lean -/
section
/-! Equation (1) for the actual von Mangoldt sum. Positive integer exponents
of at least two are indexed by k+2, including when the cutoff is a prime power. -/

noncomputable section
open scoped BigOperators
open ArithmeticFunction Set
namespace Mertens

def powerWeight (p : Nat.Primes) (k : ℕ) : ℝ := Real.log p / (p : ℝ) ^ (k + 2)

theorem powerWeight_nonneg (p : Nat.Primes) (k : ℕ) : 0 ≤ powerWeight p k := by
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
  exact div_nonneg (Real.log_nonneg hp) (pow_nonneg (by positivity) _)

/-- The geometric series at each prime is exactly its contribution to E. -/
theorem powerWeight_hasSum (p : Nat.Primes) : HasSum (powerWeight p) (constantTerm p) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hg := hasSum_geometric_of_lt_one (inv_nonneg.mpr hp0.le) ((inv_lt_one₀ hp0).mpr hp)
  convert hg.mul_left (Real.log p / (p : ℝ) ^ 2) using 1
  · ext k
    simp only [powerWeight, pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  · unfold constantTerm
    field_simp [hp0.ne', (by linarith : (p : ℝ) - 1 ≠ 0)]
    ring

private def inside (x : ℝ) (p : Nat.Primes) : Set ℕ :=
  {k | (p : ℕ) ^ (k + 2) ≤ ⌊x⌋₊}

def includedPowers (x : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' k, (inside x p).indicator (powerWeight p) k

def omittedPowers (x : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' k, (inside x p)ᶜ.indicator (powerWeight p) k

/-- P(x) in the paper. -/
def primePowerTail (x : ℝ) : ℝ := ∑' p : Nat.Primes, omittedPowers x p

theorem split_at_prime (x : ℝ) (p : Nat.Primes) :
    includedPowers x p + omittedPowers x p = constantTerm p := by
  have h := (powerWeight_hasSum p).summable
  unfold includedPowers omittedPowers
  rw [← (h.indicator (inside x p)).tsum_add (h.indicator (inside x p)ᶜ)]
  simpa only [Set.indicator_self_add_compl_apply] using (powerWeight_hasSum p).tsum_eq

theorem prime_power_partition (x : ℝ) :
    (∑' p : Nat.Primes, includedPowers x p) + primePowerTail x =
      ∑' p : Nat.Primes, constantTerm p := by
  have hi (p : Nat.Primes) : 0 ≤ includedPowers x p :=
    tsum_nonneg fun k => Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
  have ho (p : Nat.Primes) : 0 ≤ omittedPowers x p :=
    tsum_nonneg fun k => Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
  have his := constantTerm_summable.of_nonneg_of_le hi
    (fun p => by linarith [split_at_prime x p, ho p])
  have hos := constantTerm_summable.of_nonneg_of_le ho
    (fun p => by linarith [split_at_prime x p, hi p])
  rw [primePowerTail, ← his.tsum_add hos]
  exact tsum_congr (split_at_prime x)

def tailWeight (x : ℝ) (p : Nat.Primes) (k : ℕ) : ℝ :=
  if x < (p : ℝ) ^ (k + 2) then powerWeight p k else 0

private theorem tailWeight_indicator {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) (k : ℕ) :
    tailWeight x p k = (inside x p)ᶜ.indicator (powerWeight p) k := by
  classical
  simp [tailWeight, inside, Set.indicator, Nat.le_floor_iff hx, Nat.cast_pow, not_le]

theorem tails_by_exponent {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun k => ∑' p : Nat.Primes, tailWeight x p k) ∧
    primePowerTail x = ∑' k, ∑' p : Nat.Primes, tailWeight x p k := by
  have hrow (p : Nat.Primes) : Summable (tailWeight x p) := by
    simpa only [funext (tailWeight_indicator hx p)] using
      ((powerWeight_hasSum p).summable.indicator (inside x p)ᶜ)
  have hrowSum (p : Nat.Primes) : (∑' k, tailWeight x p k) = omittedPowers x p :=
    tsum_congr (tailWeight_indicator hx p)
  have hpos (p : Nat.Primes) (k : ℕ) : 0 ≤ tailWeight x p k := by
    rw [tailWeight_indicator hx p k]
    exact Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
  have hsum : Summable (fun p : Nat.Primes => ∑' k, tailWeight x p k) := by
    apply constantTerm_summable.of_nonneg_of_le (fun p => tsum_nonneg (hpos p))
    intro p
    rw [hrowSum]
    have h : 0 ≤ includedPowers x p :=
      tsum_nonneg fun k => Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
    linarith [split_at_prime x p]
  have hall : Summable (Function.uncurry (tailWeight x)) :=
    (summable_prod_of_nonneg (fun pk => hpos pk.1 pk.2)).mpr ⟨hrow, hsum⟩
  refine ⟨hall.prod_symm.prod, ?_⟩
  calc
    primePowerTail x = ∑' p : Nat.Primes, ∑' k, tailWeight x p k := (tsum_congr hrowSum).symm
    _ = _ := hall.tsum_comm.symm

/-- The sum A(x), including the weight at the endpoint. -/
def mangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), vonMangoldt n / (n : ℝ)

private def cutoffWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n ≤ ⌊x⌋₊ then vonMangoldt n / (n : ℝ) else 0

private theorem mangoldt_eq_tsum (x : ℝ) :
    HasSum (cutoffWeight x) (mangoldtSum x) := by
  let s := Finset.range (⌊x⌋₊ + 1)
  have hf (n : ℕ) (hn : n ∉ s) : cutoffWeight x n = 0 := by
    have : ¬ n ≤ ⌊x⌋₊ := by simpa [s, Nat.lt_succ_iff] using hn
    simp [cutoffWeight, this]
  convert hasSum_sum_of_ne_finset_zero hf using 1
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have h : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  simp [cutoffWeight, h]

private theorem primes_eq_tsum (x : ℝ) :
    (∑' p : Nat.Primes, cutoffWeight x p) = primeSum x := by
  classical
  change (∑' p : {n : ℕ | n.Prime}, cutoffWeight x p) = primeSum x
  rw [tsum_subtype]
  let s := Finset.range (⌊x⌋₊ + 1)
  rw [tsum_eq_sum (s := s)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have h : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    by_cases hp : n.Prime <;> simp [Set.indicator, hp, primeWeight, cutoffWeight, h,
      ArithmeticFunction.vonMangoldt_apply_prime]
  · intro n hn
    have h : ¬ n ≤ ⌊x⌋₊ := by simpa [s, Nat.lt_succ_iff] using hn
    by_cases hp : n.Prime <;> simp [Set.indicator, hp, cutoffWeight, h]

theorem mangoldt_split (x : ℝ) :
    mangoldtSum x = primeSum x + ∑' p : Nat.Primes, includedPowers x p := by
  have hf := mangoldt_eq_tsum x
  have hs : Function.support (cutoffWeight x) ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hp
    have h : vonMangoldt n = 0 := vonMangoldt_eq_zero_iff.mpr hp
    exact hn (by simp [cutoffWeight, h])
  rw [← hf.tsum_eq, tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers
    hf.summable hs, primes_eq_tsum]
  congr 1
  apply tsum_congr
  intro p
  apply tsum_congr
  intro k
  by_cases h : (p : ℕ) ^ (k + 2) ≤ ⌊x⌋₊ <;>
    simp [cutoffWeight, Set.indicator, inside, h, Nat.cast_pow, powerWeight,
      vonMangoldt_apply_pow (by omega : k + 2 ≠ 0), vonMangoldt_apply_prime p.prop]

/-- The signed decomposition used before applying the explicit formula. -/
theorem prime_power_identity (x : ℝ) :
    error x = mangoldtSum x - Real.log x + Real.eulerMascheroniConstant + primePowerTail x := by
  rw [error, mertensConstant, mangoldt_split]
  linarith [prime_power_partition x]

end Mertens
end
end

/-! ## Mertens/PrimeSplit.lean -/
section
noncomputable section
namespace Mertens

/-- The expression to which Landau's smoothed explicit formula is applied. -/
def normalizedMangoldt (u : ℝ) : ℝ :=
  Real.sqrt (Real.exp u) *
    (mangoldtSum (Real.exp u) - u + Real.eulerMascheroniConstant)

/-- Equation (1), normalised, with the prime squares and higher powers in exactly
the order used in the two estimates in section 4. -/
theorem normalized_prime_power_split (u : ℝ) :
    normalized u = normalizedMangoldt u + Input.squareAt u + Input.higherAt u := by
  have h := tails_by_exponent (Real.exp_pos u).le
  let row := fun k : ℕ => ∑' p : Nat.Primes, tailWeight (Real.exp u) p k
  have hzero :
      row 0 = ∑' p : Nat.Primes, if Real.sqrt (Real.exp u) < (p : ℝ)
        then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0 := by
    apply tsum_congr
    intro p
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    simp only [tailWeight, powerWeight, zero_add, Real.sqrt_lt' hp]
  have hsuc (k : ℕ) : row (k + 1) = Input.primePowerTail (k + 3) (Real.exp u) := by
    apply tsum_congr
    intro p
    simp only [tailWeight, powerWeight, Nat.add_assoc]
  have htail : primePowerTail (Real.exp u) = row 0 + ∑' k, Input.primePowerTail (k+3) (Real.exp u) := by
    calc
      _ = ∑' k, row k := h.2
      _ = row 0 + ∑' k : ℕ, row (k + 1) := h.1.tsum_eq_zero_add
      _ = _ := congrArg (row 0 + ·) (tsum_congr hsuc)
  rw [normalized, prime_power_identity, Real.log_exp, htail, hzero]
  unfold normalizedMangoldt Input.squareAt Input.higherAt
  ring

end Mertens
end
end

/-! ## Mertens/Averaging.lean -/
section
noncomputable section
open MeasureTheory Set ArithmeticFunction
open scoped BigOperators
namespace Mertens.Input

private def scale (u : ℝ) := Real.sqrt (Real.exp u)
private def bin (u : ℝ) := ⌊Real.exp u⌋₊
private def rowAt (n k : ℕ) : ℝ :=
  ∑' p : Nat.Primes, if n < p.val ^ k then Real.log (p : ℝ) / (p : ℝ)^k else 0

private theorem power_row (u : ℝ) (k : ℕ) :
    primePowerTail k (Real.exp u) = rowAt (bin u) k := by
  apply tsum_congr
  intro p
  have h : bin u < p.val^k ↔ Real.exp u < (p : ℝ)^k := by
    simpa [bin] using (Nat.floor_lt (a := Real.exp u) (n := p.val^k) (Real.exp_pos u).le)
  simp only [h]

private theorem square_row (u : ℝ) : squareAt u = scale u * rowAt (bin u) 2 := by
  unfold squareAt scale
  rw [← power_row]
  dsimp only
  apply congrArg (Real.sqrt (Real.exp u) * ·)
  unfold primePowerTail
  apply tsum_congr
  intro p
  simp only [Real.sqrt_lt' (by exact_mod_cast p.prop.pos : 0 < (p : ℝ))]

private theorem higher_row (u : ℝ) :
    higherAt u = scale u * (∑' j : ℕ, rowAt (bin u) (j+3)) := by
  unfold higherAt scale
  simp only [power_row]

private theorem weight_cont {g : ℝ → ℝ} (hg : IntegrableOn g window) (f : ℝ → ℝ)
    (hf : Continuous f) : IntegrableOn (fun u => g u * f u) window := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (α := ℝ) (a := lo) (b := hi)).bddAbove_image
    hf.norm.continuousOn
  have hb : ∀ᵐ u ∂volume.restrict window, ‖f u‖ ≤ C := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := lo) (b := hi))] with u hu
    exact hC ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩
  simpa only [mul_comm] using hg.bdd_mul' hf.measurable.aestronglyMeasurable hb

/-- A function of the integer cutoff takes only finitely many values on
this particular window, however large its endpoints are. -/
private theorem weight_bin {g : ℝ → ℝ} (hg : IntegrableOn g window) (a : ℕ → ℝ) :
    IntegrableOn (fun u => g u * a (bin u)) window := by
  let s := Finset.range (bin hi + 1)
  have hmeas : Measurable (fun u => a (bin u)) :=
    (measurable_of_countable a).comp (Real.continuous_exp.measurable.nat_floor)
  have hb : ∀ᵐ u ∂volume.restrict window, ‖a (bin u)‖ ≤ ∑ n ∈ s, ‖a n‖ := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := lo) (b := hi))] with u hu
    apply Finset.single_le_sum (f := fun n => ‖a n‖) (fun n _ => norm_nonneg _)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (Real.exp_le_exp.mpr hu.2.le)))
  simpa only [mul_comm] using hg.bdd_mul' hmeas.aestronglyMeasurable hb

theorem averaged_prime_power_split (mass : ∫ u in window, kernel u = 1) :
    weightedMean kernel lo hi = avg normalizedMangoldt + avg squareAt + avg higherAt := by
  have hk : IntegrableOn kernel window := integrable_of_integral_eq_one mass
  have hs : IntegrableOn (fun u => kernel u * scale u) window :=
    weight_cont hk scale (Real.continuous_sqrt.comp Real.continuous_exp)
  have hsquare : IntegrableOn (fun u => kernel u * squareAt u) window := by
    simpa only [square_row, ← mul_assoc] using weight_bin hs (fun n => rowAt n 2)
  have hhigher : IntegrableOn (fun u => kernel u * higherAt u) window := by
    simpa only [higher_row, ← mul_assoc] using weight_bin hs (fun n => ∑' j : ℕ, rowAt n (j+3))
  have hA := weight_bin hs (fun m => ∑ n ∈ Finset.range (m+1), vonMangoldt n / (n:ℝ))
  have hu := weight_cont hs id continuous_id
  have hM : IntegrableOn (fun u => kernel u * normalizedMangoldt u) window := by
    simpa only [normalizedMangoldt, mangoldtSum, bin, scale, mul_add, mul_sub, ← mul_assoc,
      id_eq, Pi.add_apply, Pi.sub_apply] using (hA.sub hu).add (hs.mul_const Real.eulerMascheroniConstant)
  unfold weightedMean avg
  change (∫ u in window, kernel u * normalized u) = _
  simp only [normalized_prime_power_split, mul_add]
  have hsum : IntegrableOn (fun u => kernel u * normalizedMangoldt u + kernel u * squareAt u) window := hM.add hsquare
  rw [integral_add hsum hhigher, integral_add hM hsquare]

end Mertens.Input
end
end

/-! ## Mertens/HigherPowers.lean -/
section
/-! A Rankin bound for all exponents at least three. This direct majorant
avoids a second appeal to a prime number theorem. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens

private def rankinWeight (n : ℕ) : ℝ := (n : ℝ) ^ (-101 / 100 : ℝ)

private theorem rankin_weight_nonneg (n : ℕ) : 0 ≤ rankinWeight n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

private theorem rankin_summable : Summable rankinWeight :=
  Real.summable_nat_rpow.mpr (by norm_num)

private theorem rankin_sum_le : (∑' n : ℕ, rankinWeight n) ≤ 101 := by
  let f (x : ℝ) := x ^ (-101 / 100 : ℝ)
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-101 / 100 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)
  have hI : ∫ t : ℝ in Set.Ioi 1, f t = 100 := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num
  have htail : (∑' n : ℕ, rankinWeight (n + 2)) ≤ 100 := by
    apply Real.tsum_le_of_sum_range_le (fun n => rankin_weight_nonneg _)
    intro N
    have ha : AntitoneOn f (Icc (1 : ℝ) (1 + (N : ℝ))) := by
      intro a ha b _ hab
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one ha.1) hab (by norm_num)
    calc
      (∑ i ∈ Finset.range N, rankinWeight (i + 2)) =
          ∑ i ∈ Finset.range N, f (1 + (i + 1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [rankinWeight, f]
        push_cast
        congr 1
        ring
      _ ≤ ∫ x in (1 : ℝ)..1 + N, f x := ha.sum_le_integral
      _ ≤ ∫ x in Set.Ioi 1, f x := by
        rw [intervalIntegral.integral_of_le (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ 1 + (N : ℝ))]
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with t ht
          exact Real.rpow_nonneg (le_trans zero_le_one ht.le) _
        · exact Filter.Eventually.of_forall (fun _ ht => ht.1)
      _ = 100 := hI
  have htwo : (∑ n ∈ Finset.range 2, rankinWeight n) = 1 := by
    norm_num [Finset.sum_range_succ, rankinWeight]
  have hsplit := rankin_summable.sum_add_tsum_nat_add 2
  linarith

/-- Decay from one extra power of any prime, uniform down to the prime 2. -/
private theorem rankin_ratio {p : ℝ} (hp : 2 ≤ p) :
    Real.exp (-(17 / 50) * Real.log p) ≤ 4 / 5 := by
  have hp₁ : 1 ≤ p := by linarith
  have h := Real.log_le_log (x := (5 / 4 : ℝ) ^ 3) (y := p) (by norm_num)
    ((by norm_num : (5 / 4 : ℝ) ^ 3 ≤ 2).trans hp)
  rw [Real.log_pow] at h
  have hlog : -(17 / 50) * Real.log p ≤ -Real.log (5 / 4) := by
    nlinarith [Real.log_nonneg hp₁]
  calc
    _ ≤ Real.exp (-Real.log (5 / 4)) := Real.exp_le_exp.mpr hlog
    _ = 4 / 5 := by rw [Real.exp_neg, Real.exp_log (by norm_num)] ; norm_num

/-- Estimate one prime power across the cutoff by splitting its exponent
between the cutoff, the geometric series in j and a convergent p-series. -/
private theorem rankin_term (u : ℝ) (j : ℕ) (p : Nat.Primes) :
    (if Real.exp u < (p : ℝ) ^ (j + 3)
      then Real.log (p : ℝ) / (p : ℝ) ^ (j + 3) else 0) ≤
      (100 * Real.exp (-(33 / 50) * u) * (4 / 5 : ℝ)^j) * rankinWeight p.val := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp₂ : 2 ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  let l := Real.log (p : ℝ)
  have hweight : rankinWeight p.val = Real.exp (l * (-101 / 100)) :=
    Real.rpow_def_of_pos hp _
  split_ifs with hcut
  · have hlog : u < ((j : ℝ) + 3) * l := by
      have h := Real.log_lt_log (Real.exp_pos u) hcut
      simpa [l, Real.log_pow] using h
    have hA : Real.exp (-(33 / 50) * (((j : ℝ) + 3) * l)) ≤
        Real.exp (-(33 / 50) * u) := Real.exp_le_exp.mpr (by linarith)
    have hB : (Real.exp (-(17 / 50) * l)) ^ j ≤ (4 / 5 : ℝ) ^ j :=
      pow_le_pow_left₀ (Real.exp_pos _).le (rankin_ratio hp₂) j
    have hl : l ≤ 100 * Real.exp (l / 100) := by linarith [Real.add_one_le_exp (l / 100)]
    have hpowers : (p : ℝ) ^ (j + 3) = Real.exp (((j : ℝ) + 3) * l) := by
      simpa [l, Real.exp_log hp] using (Real.exp_nat_mul l (j+3)).symm
    calc
      Real.log (p : ℝ) / (p : ℝ) ^ (j+3) =
          l * Real.exp (-(((j : ℝ) + 3) * l)) := by rw [hpowers, Real.exp_neg, div_eq_mul_inv]
      _ ≤ (100 * Real.exp (l/100)) * Real.exp (-(((j : ℝ) + 3) * l)) :=
        mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = (100 * Real.exp (-(33/50) * (((j : ℝ) + 3) * l)) *
          (Real.exp (-(17/50) * l))^j) * rankinWeight p.val := by
        rw [hweight, ← Real.exp_nat_mul]
        simp only [mul_assoc, ← Real.exp_add]
        congr 2; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (rankin_weight_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB
          (pow_nonneg (Real.exp_pos _).le _) (by positivity)
  · exact mul_nonneg (by positivity) (rankin_weight_nonneg _)

private theorem prime_weight_sum_le : (∑' p : Nat.Primes, rankinWeight p.val) ≤ 101 := by
  have h := rankin_summable.tsum_subtype_le (fun n : ℕ => rankinWeight n)
    {n : ℕ | n.Prime} rankin_weight_nonneg
  exact h.trans rankin_sum_le

/-- A uniform bound for the complete, normalized sum over all powers k ≥ 3,
with the exact prime cutoff of the manuscript. -/
theorem higher_rankin_majorant (u : ℝ) :
    Input.higherAt u ≤ 50500 * Real.exp (-(4 / 25) * u) := by
  let c := 100 * Real.exp (-(33/50) * u)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hweights : Summable (fun p : Nat.Primes => rankinWeight p.val) := rankin_summable.subtype _
  have hj (j : ℕ) : Input.primePowerTail (j+3) (Real.exp u) ≤
      (c * 101) * (4 / 5 : ℝ) ^ j := by
    have hq : 0 ≤ c * (4 / 5 : ℝ) ^ j := mul_nonneg hc (by positivity)
    let term (p : Nat.Primes) := if Real.exp u < (p : ℝ)^(j + 3)
      then Real.log (p : ℝ) / (p : ℝ)^(j + 3) else 0
    have hi : Summable term := Summable.of_nonneg_of_le (fun p => by
      dsimp [term]; split_ifs
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le))
          (pow_nonneg (Nat.cast_nonneg _) _)
      · rfl) (rankin_term u j) (hweights.mul_left (c * (4/5:ℝ)^j))
    change (∑' p, term p) ≤ _
    calc
      _ ≤ ∑' p : Nat.Primes, (c * (4/5:ℝ)^j) * rankinWeight p.val :=
        hi.tsum_le_tsum (rankin_term u j) (hweights.mul_left _)
      _ = (c * (4/5:ℝ)^j) * ∑' p : Nat.Primes, rankinWeight p.val := by rw [tsum_mul_left]
      _ ≤ (c * (4/5:ℝ)^j) * 101 :=
        mul_le_mul_of_nonneg_left prime_weight_sum_le hq
      _ = _ := by ring
  have hg := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (4/5:ℝ)) (by norm_num)).mul_left (c * 101)
  have hsum : (∑' j : ℕ, Input.primePowerTail (j+3) (Real.exp u)) ≤ (c * 101) * 5 := by
    have hs : Summable (fun j : ℕ => Input.primePowerTail (j+3) (Real.exp u)) := by
      apply Summable.of_nonneg_of_le _ hj hg.summable
      intro j
      apply tsum_nonneg
      intro p
      split_ifs
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le))
          (pow_nonneg (Nat.cast_nonneg _) _)
      · exact le_rfl
    calc
      _ ≤ _ := hs.tsum_le_tsum hj hg.summable
      _ = _ := by convert hg.tsum_eq using 1; norm_num
  have hsqrt : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
    rw [← Real.exp_half]
  calc
    Input.higherAt u ≤ Real.sqrt (Real.exp u) * ((c*101)*5) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = _ := by
      rw [hsqrt]
      dsimp [c]
      calc
        _ = 50500 * (Real.exp (u / 2) * Real.exp (-(33 / 50) * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem higher_tail_lt {u : ℝ} (hu : 495 ≤ u) :
    Input.higherAt u < 1 / (10 : ℝ)^29 :=
  (higher_rankin_majorant u).trans_lt <|
    (mul_le_mul_of_nonneg_right (by norm_num : (50500 : ℝ) ≤ 51000)
      (Real.exp_pos _).le).trans_lt (rankin_majorant_lt hu)

end Mertens
end
end

/-! ## Mertens/PrimeSquares.lean -/
section
/-! # A direct prime-square estimate
Integrating the finite counting function of primes in (y,t) gives an
upper bound for each finite subsum. This establishes convergence as well
as the prime-square estimate used in the transfer. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens.Input

private def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private theorem primeLog_nonneg (n : ℕ) : 0 ≤ primeLog n := by
  unfold primeLog
  split_ifs with hn
  · exact Real.log_nonneg (by exact_mod_cast hn.one_le)
  · exact le_rfl

private theorem count_between (s : Finset Nat.Primes) {y t : ℝ} (hy : 0 < y) (hyt : y < t) :
    chebyshevTheta y + (∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0)
      ≤ chebyshevTheta t := by
  classical
  let selected : Finset Nat.Primes := s.filter (fun p : Nat.Primes => y < (p : ℝ) ∧ (p : ℝ) < t)
  let a := selected.map (Function.Embedding.subtype Nat.Prime)
  let ry := Finset.range (⌊y⌋₊ + 1)
  let rt := Finset.range (⌊t⌋₊ + 1)
  have ha : ∀ n ∈ a, y < (n : ℝ) ∧ (n : ℝ) < t := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    exact (Finset.mem_filter.mp hp).2
  have hd : Disjoint ry a := by
    apply Finset.disjoint_left.mpr
    intro n hn hna
    have hn' : n ≤ ⌊y⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    exact (not_lt_of_ge ((Nat.le_floor_iff hy.le).mp hn')) (ha n hna).1
  have hs : ry ∪ a ⊆ rt := by
    intro n hn
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    rcases Finset.mem_union.mp hn with hl | hr
    · exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)).trans (Nat.floor_mono hyt.le)
    · exact Nat.le_floor (ha n hr).2.le
  have hsum : (∑ n ∈ a, primeLog n) =
      ∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    change (∑ n ∈ selected.map _, primeLog n) = ∑ p ∈ selected, _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p _
    exact if_pos p.prop
  change (∑ n ∈ ry, primeLog n) + _ ≤ ∑ n ∈ rt, primeLog n
  rw [← hsum, ← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => primeLog_nonneg i)

private theorem pow_int_three {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ in Ioi y, t ^ (-3 : ℝ)) = 1 / (2 * y^2) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hy]
  have hh : y ^ (-2 : ℝ) = (y^2)⁻¹ := by rw [Real.rpow_neg hy.le]; norm_num
  norm_num [hh]; ring

private theorem pow_int_two {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ in Ioi y, t ^ (-2 : ℝ)) = 1 / y := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy]
  have hh : y ^ (-1 : ℝ) = y⁻¹ := by rw [Real.rpow_neg hy.le, Real.rpow_one]
  norm_num [hh, one_div]

private def step (y : ℝ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  if y < (p : ℝ) then
    (Ioi (p : ℝ)).indicator (fun v : ℝ => Real.log (p : ℝ) * v ^ (-3 : ℝ)) t else 0

private theorem step_int {y : ℝ} (hy : 0 < y) (p : Nat.Primes) :
    IntegrableOn (step y p) (Ioi y) := by
  by_cases hp : y < (p : ℝ)
  · have he : step y p = (Ioi (p : ℝ)).indicator
        (fun v : ℝ => Real.log (p : ℝ) * v ^ (-3 : ℝ)) := funext fun _ => if_pos hp
    rw [he]
    exact (((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hy).const_mul
        (Real.log (p : ℝ))).indicator measurableSet_Ioi)
  · have he : step y p = (fun _ : ℝ => (0 : ℝ)) := funext fun _ => if_neg hp
    rw [he]
    exact integrable_zero _ _ _

private theorem step_value {y : ℝ} (hy : 0 < y) (p : Nat.Primes) :
    (∫ t in Ioi y, step y p t) =
      (if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0) / 2 := by
  by_cases hp : y < (p : ℝ)
  · simp only [step, hp, if_true, setIntegral_indicator measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_right hp.le, integral_const_mul, pow_int_three (hy.trans hp)]
    ring
  · simp [step, hp]

private theorem step_bound (s : Finset Nat.Primes) {y D t : ℝ} (hy : 0 < y) (hyt : y < t)
    (hθ : ∀ v, y ≤ v → |chebyshevTheta v - v| ≤ D*v) :
    (∑ p ∈ s, step y p t) ≤
      (1 + D) * t ^ (-2 : ℝ) - ((1 - D) * y) * t ^ (-3 : ℝ) := by
  classical
  have ht : 0 < t := hy.trans hyt
  have hcount := count_between s hy hyt
  have h1 := (abs_le.mp (hθ y le_rfl)).1
  have h2 := (abs_le.mp (hθ t hyt.le)).2
  have hcut : (∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0)
      ≤ (1+D)*t-(1-D)*y := by linarith
  have hm := mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg ht.le (-3 : ℝ))
  have heq : (∑ p ∈ s, step y p t) =
      (∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0) * t^(-3 : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : y < (p : ℝ) <;> by_cases k : (p : ℝ) < t <;> simp [step,h,k, Set.indicator, Set.mem_Ioi]
  have hpow : t * t ^ (-3 : ℝ) = t ^ (-2 : ℝ) := by
    calc t * t ^ (-3 : ℝ) = t ^ (1 : ℝ) * t ^ (-3 : ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [← Real.rpow_add ht]; norm_num
  rw [heq]
  apply hm.trans_eq
  rw [sub_mul, mul_assoc, hpow]

private theorem finite_square_bound {y D : ℝ} (hy : 0 < y)
    (hθ : ∀ t, y ≤ t → |chebyshevTheta t - t| ≤ D*t) (s : Finset Nat.Primes) :
    (∑ p ∈ s, if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0) ≤ (1+3*D)/y := by
  have hi2 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy).const_mul (1 + D)
  have hi3 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hy).const_mul ((1 - D) * y)
  have h := setIntegral_mono_on (integrable_finset_sum s (fun p _ => step_int hy p))
         (hi2.sub hi3) measurableSet_Ioi (fun t ht => step_bound s hy ht hθ)
  simp only [Pi.sub_apply] at h
  rw [integral_finset_sum s (fun p _ => step_int hy p), integral_sub hi2 hi3,
     integral_const_mul, integral_const_mul, pow_int_two hy, pow_int_three hy] at h
  simp_rw [step_value hy] at h
  rw [← Finset.sum_div] at h
  have heq : (1 + D) * (1 / y) - ((1-D)*y) * (1/(2*y^2)) = ((1+3*D)/y)/2 := by
    field_simp [hy.ne']; ring
  rw [heq] at h
  linarith

/-- Dusart's relative theta bound alone bounds the actual prime-square tail. -/
theorem square_le_of_theta {u D : ℝ} (_hD : 0 ≤ D)
    (hθ : ∀ t, Real.sqrt (Real.exp u) ≤ t → |chebyshevTheta t - t| ≤ D*t) :
    squareAt u ≤ 1+3*D := by
  let y := Real.sqrt (Real.exp u)
  have hy : 0 < y := Real.sqrt_pos.2 (Real.exp_pos _)
  let f (p : Nat.Primes) := if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0
  have hnon : 0 ≤ f := by
    intro p
    dsimp [f]
    split_ifs
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (sq_nonneg _)
    · exact le_rfl
  have hb (s : Finset Nat.Primes) : (∑ p ∈ s, f p) ≤ (1+3*D)/y :=
    finite_square_bound hy hθ s
  have h := (summable_of_sum_le hnon hb).tsum_le_of_sum_le hb
  change y * (∑' p, f p) ≤ _
  rw [mul_comm]
  exact (le_div_iff₀ hy).mp h

end Mertens.Input
end
end

/-! ## Mertens/EulerBound.lean -/
section
/-! # A numerical bound for the Hadamard constant
The midpoint correction reduces the required exact computation to 384
harmonic summands. The estimate of the logarithm uses dyadic reduction.
-/

open Filter Topology

namespace Mertens

private noncomputable def harmonicMidpoint (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2)

/-- Shifting the logarithm by a half gives decreasing upper bounds for γ. -/
theorem euler_le_harmonic_midpoint (n : ℕ) :
    Real.eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2) := by
  have hanti : Antitone harmonicMidpoint := by
    apply antitone_nat_of_succ_le
    intro k
    have hp : 0 < (k : ℝ) + 1 / 2 := by positivity
    have h := Real.le_log_one_add_of_nonneg (x := 1 / ((k : ℝ) + 1 / 2)) (by positivity)
    have hq : 2 * (1 / ((k : ℝ) + 1 / 2)) / (1 / ((k : ℝ) + 1 / 2) + 2) =
        1 / ((k : ℝ) + 1) := by
      field_simp
      ring
    have ha : 1 + 1 / ((k : ℝ) + 1 / 2) =
        ((k : ℝ) + 1 + 1 / 2) / ((k : ℝ) + 1 / 2) := by
      field_simp
      ring
    rw [hq, ha, Real.log_div (by positivity) hp.ne'] at h
    simp only [harmonicMidpoint, harmonic_succ, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast, Rat.cast_one, Nat.cast_add_one]
    rw [one_div] at h
    linarith [h]
  have hm : Tendsto harmonicMidpoint atTop (𝓝 Real.eulerMascheroniConstant) := by
    have hh := Real.tendsto_harmonic_sub_log.sub
      ((Real.tendsto_log_comp_add_sub_log (1 / 2)).comp tendsto_natCast_atTop_atTop)
    rw [sub_zero] at hh
    apply hh.congr
    intro k
    dsimp [harmonicMidpoint]
    ring
  exact hanti.le_of_tendsto hm n

private def harmonicRec : ℕ → ℚ
| 0 => 0
| n+1 => harmonicRec n + ((n+1:ℕ):ℚ)⁻¹
private theorem harmonic_eq_rec (n : ℕ) : harmonic n = harmonicRec n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [harmonic_succ, harmonicRec, ih, Nat.cast_add_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
private theorem harmonic_384_upper : harmonic 384 < (652915974 : ℚ) / 100000000 := by
  rw [harmonic_eq_rec]
  decide +kernel

private theorem log_product_lower :
    (84829679 : ℝ) / 10000000 < Real.log ((384 + 1 / 2 : ℝ) * (4 * Real.pi)) := by
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  have hr : (84829679 : ℝ) / 10000000 <
      ((12 : ℕ) : ℝ) * Real.log 2 + 16520175 / 100000000 := by
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  have ht : Real.exp ((16520175 : ℝ) / 100000000) < 11796311 / 10000000 := by
    have h := Real.exp_bound' (x := (16520175 : ℝ) / 100000000)
      (by norm_num) (by norm_num) (n := 8) (by decide)
    apply lt_of_le_of_lt h
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    _ < Real.exp (((12 : ℕ) : ℝ) * Real.log 2 + 16520175 / 100000000) :=
      Real.exp_lt_exp.mpr hr
    _ = (2 : ℝ) ^ 12 * Real.exp (16520175 / 100000000) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < (2 : ℝ) ^ 12 * (11796311 / 10000000) :=
      mul_lt_mul_of_pos_left ht (by norm_num)
    _ < _ := by linarith [Real.pi_gt_d20]

/-- The numerical input in the paper's Hadamard-mass estimate. -/
theorem hadamard_constant_lt :
    2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) < (46192 : ℝ) / 1000000 := by
  have hH : (harmonic 384 : ℝ) < (652915974 : ℝ) / 100000000 := by
    have hh := (Rat.cast_lt (K := ℝ)).2 harmonic_384_upper
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh.trans_le (by norm_num)
  have hγ := euler_le_harmonic_midpoint 384
  have hlog := log_product_lower
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hγ
  linarith

end Mertens
end

/-! ## Mertens/KernelSymmetry.lean -/
section
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
end
end

/-! ## Mertens/Spectral.lean -/
section
/-! Passage from the absolute, unweighted transforms in Büthe's tail
lemmas to the signed, phased sums appearing in the explicit formula. -/

noncomputable section

open MeasureTheory
namespace Mertens.Input

def rawMid (z : ZeroCopy) : ℝ :=
  if 4 * 10^9 < |(rho z).im| ∧ |(rho z).im| ≤ 10^10 then
    ‖transform ((rho z - 1/2) / Complex.I)‖ / |(rho z).im|
  else 0

/-- The real-ordinate form appearing literally on the left of Büthe 6.3. -/
def rawMidReal (z : ZeroCopy) : ℝ :=
  if 4 * 10^9 < |(rho z).im| ∧ |(rho z).im| ≤ 10^10 then
    |ell (rho z).im| / |(rho z).im|
  else 0

theorem rawMid_from_real (mass : ∫ u in window, kernel u = 1)
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2)
    (h : Summable rawMidReal ∧ (∑' z, rawMidReal z) ≤ middleMajorant) :
    Summable rawMid ∧ (∑' z, rawMid z) ≤ middleMajorant := by
  have heq : rawMid = rawMidReal := by
    funext z
    unfold rawMid rawMidReal
    split_ifs with hz
    · rw [frequency_on_critical_line z (critical z hz.2), transform_real mass]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    · rfl
  rwa [heq]

def rawHigh (z : ZeroCopy) : ℝ :=
  if 10^10 < |(rho z).im| then
    ‖transform ((rho z - 1/2) / Complex.I)‖ / |(rho z).im|
  else 0

private theorem wave_norm_bound (z : ZeroCopy) {C : ℝ} (hC : 0 ≤ C)
    (hγ : 0 < |(rho z).im|) (hp : Real.exp ((1/2 - (rho z).re) * omega) ≤ C) :
    ‖wave z‖ ≤ C * (‖transform ((rho z - 1/2) / Complex.I)‖ / |(rho z).im|) := by
  have hphase : ‖Complex.exp ((1/2 - rho z) * (omega : ℂ))‖ =
      Real.exp ((1/2 - (rho z).re) * omega) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [Complex.mul_re]
  calc
    ‖wave z‖ = Real.exp ((1/2 - (rho z).re) * omega) *
        ‖transform ((rho z - 1/2) / Complex.I)‖ / ‖rho z‖ := by
      rw [wave, norm_div, norm_mul, hphase]
    _ ≤ (C * ‖transform ((rho z - 1/2) / Complex.I)‖) / ‖rho z‖ := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (C * ‖transform ((rho z - 1/2) / Complex.I)‖) / |(rho z).im| :=
      div_le_div_of_nonneg_left (mul_nonneg hC (norm_nonneg _)) hγ (Complex.abs_im_le_norm _)
    _ = _ := by ring

private theorem middle_norm_on (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 →
    (rho z).re = 1/2) (z : ZeroCopy)
    (hz : 4 * 10^9 < |(rho z).im| ∧ |(rho z).im| ≤ 10^10) : ‖wave z‖ ≤ rawMid z := by
  have h := wave_norm_bound z (C := 1) (by norm_num)
    ((by norm_num : (0 : ℝ) < 4*10^9).trans hz.1) (by simp [critical z hz.2])
  simpa only [rawMid, if_pos hz, one_mul] using h

private theorem high_norm_on (z : ZeroCopy) (hz : 10^10 < |(rho z).im|) :
    ‖wave z‖ ≤ Real.exp (omega/2) * rawHigh z := by
  rw [rawHigh, if_pos hz]
  apply wave_norm_bound z (Real.exp_pos _).le ((by norm_num : (0 : ℝ) < 10^10).trans hz)
  apply Real.exp_le_exp.mpr
  have hb : 0 < (rho z).re := z.prop.2.1
  have hω : 0 ≤ omega := by norm_num [omega]
  nlinarith [mul_nonneg hb.le hω]

/-- Absolute convergence of the full complex waves, including the off-line tail.
This dominates the series after multiplication by a uniformly bounded complex
mollifier transform. -/
theorem summable_norm_wave (finite : lowBand.Finite)
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2)
    (mid : Summable rawMid) (high : Summable rawHigh) :
    Summable (fun z : ZeroCopy => ‖wave z‖) := by
  classical
  let lowNorm (z : ZeroCopy) := if z ∈ lowBand then ‖wave z‖ else 0
  have hl : Summable lowNorm := by
    apply summable_of_finite_support (finite.subset _)
    intro z hz
    by_contra hb
    exact hz (by simp [lowNorm, hb])
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg (wave z)) _
    ((hl.add mid).add (high.mul_left (Real.exp (omega/2))))
  intro z
  change ‖wave z‖ ≤ lowNorm z + rawMid z + Real.exp (omega/2) * rawHigh z
  by_cases hlo : z ∈ lowBand
  · have ht : |(rho z).im| ≤ 4*10^9 := hlo
    have ht' : |(rho z).im| ≤ 10^10 := ht.trans (by norm_num)
    simp [lowNorm, hlo, rawMid, rawHigh, not_lt.mpr ht, not_lt.mpr ht']
  · have ht : 4*10^9 < |(rho z).im| := lt_of_not_ge hlo
    by_cases hmid : |(rho z).im| ≤ 10^10
    · simpa only [lowNorm, if_neg hlo, zero_add, rawHigh, if_neg (not_lt.mpr hmid),
        mul_zero, add_zero] using middle_norm_on critical z ⟨ht, hmid⟩
    · simpa [lowNorm, hlo, rawMid, hmid] using high_norm_on z (lt_of_not_ge hmid)

private theorem band_tsum_le {f g : ZeroCopy → ℝ} {C : ℝ} (hg : Summable g)
    (h : ∀ z, |f z| ≤ C * g z) : ∑' z, f z ≤ C * ∑' z, g z := by
  have hs : Summable (fun z => C * g z) := hg.mul_left C
  have hf : Summable f := Summable.of_norm_bounded _ hs (by simpa only [Real.norm_eq_abs] using h)
  simpa only [tsum_mul_left] using hf.tsum_le_tsum (fun z => (le_abs_self _).trans (h z)) hs

theorem middle_bound_from_kernel
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2)
    (summ : Summable rawMid) (tail : (∑' z, rawMid z) ≤ middleMajorant) :
    middle ≤ middleMajorant := by
  have h (z : ZeroCopy) :
      |(if 4*10^9 < |(rho z).im| ∧ |(rho z).im| ≤ 10^10 then (wave z).re else 0)| ≤
        1 * rawMid z := by
    split_ifs with hz
    · simpa only [one_mul] using (Complex.abs_re_le_norm _).trans (middle_norm_on critical z hz)
    · simp [rawMid, hz]
  exact le_trans (by simpa only [middle, one_mul] using band_tsum_le summ h) tail

theorem high_bound_from_kernel (summ : Summable rawHigh)
    (tail : (∑' z, rawHigh z) ≤ highMajorant / Real.exp (omega/2)) :
    high ≤ highMajorant := by
  have h (z : ZeroCopy) :
      |(if 10^10 < |(rho z).im| then (wave z).re else 0)| ≤ Real.exp (omega/2) * rawHigh z := by
    split_ifs with hz
    · exact (Complex.abs_re_le_norm _).trans (high_norm_on z hz)
    · simp [rawHigh, hz]
  apply le_trans (show high ≤ Real.exp (omega/2) * ∑' z, rawHigh z from band_tsum_le summ h)
  simpa only [mul_comm] using (le_div_iff₀ (Real.exp_pos (omega/2))).mp tail

end Mertens.Input
end
end

/-! ## Mertens/ZeroBands.lean -/
section
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
end
end

/-! ## Mertens/FiniteZeros.lean -/
section
/-! Finiteness of the finite-height zero list follows from the same
Hadamard sum that controls the change of weight. -/

noncomputable section
namespace Mertens.Input
open Filter

theorem lowBand_finite
    (critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10 ^ 10 → (rho z).re = 1/2)
    (hs : Summable (fun z : ZeroCopy => hadamardTerm (rho z))) : lowBand.Finite := by
  let T : ℝ := 4 * 10^9
  let B : ℝ := 1/4 + T^2
  have hB : 0 < B := by dsimp [B]; positivity
  have he : ∀ᶠ z : ZeroCopy in cofinite, hadamardTerm (rho z) < B⁻¹ :=
    hs.tendsto_cofinite_zero.eventually_lt_const (inv_pos.mpr hB)
  apply (Filter.eventually_cofinite.mp he).subset
  intro z hz
  have him : |(rho z).im| ≤ T := hz
  have hT : T ≤ 10 ^ 10 := by norm_num [T]
  have hr := critical z (him.trans hT)
  have hn : ‖rho z‖ ^ 2 = (1/2 : ℝ)^2 + (rho z).im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr]
    ring
  have hnorm : ‖rho z‖ ^ 2 ≤ B := by
    rw [hn]
    have hA := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    rw [show (1/2 : ℝ)^2 = 1/4 by norm_num]
    exact add_le_add_left hA (1/4 : ℝ)
  have hpos : 0 < ‖rho z‖^2 := by rw [hn]; positivity
  change ¬ hadamardTerm (rho z) < B⁻¹
  rw [hadamard_mass_on_critical_line (rho z) hr]
  exact not_lt_of_ge (inv_anti₀ hpos hnorm)

end Mertens.Input
end
end

/-! ## Mertens/LoganMass.lean -/
section
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
end
end

/-! ## Mertens/Hadamard.lean -/
section
/-! # The logarithmic derivatives of the entire xi function
Multiplying the regular part of the completed zeta function by s(s-1)
keeps both endpoint values meaningful in Lean. The sole external input here
is the logarithmic derivative expansion of the genus-one Hadamard product. -/

noncomputable section
open scoped BigOperators
namespace Mertens.Input

/-- The entire xi function, with the removals at zero and one built into the definition. -/
def xi (s : ℂ) : ℂ := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

theorem xi_eq_completed {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [xi, completedRiemannZeta_eq]
  field_simp [hs₀, sub_ne_zero.mpr hs₁.symm]
  ring

theorem xi_one_sub (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

private theorem xi_derivative (s : ℂ) :
    deriv xi s = ((s - 1 + s) * completedRiemannZeta₀ s +
      s * (s - 1) * deriv completedRiemannZeta₀ s) / 2 := by
  have h := ((hasDerivAt_const s (1:ℂ)).add (((hasDerivAt_id s).mul
    ((hasDerivAt_id s).sub_const 1)).mul (differentiable_completedZeta₀ s).hasDerivAt)).div_const 2
  convert h.deriv using 1; simp [xi]

/-- The difference at the endpoints avoids the exponential factor of the canonical product. -/
theorem xi_logDeriv_difference :
    deriv xi 1 / xi 1 - deriv xi 0 / xi 0 =
      ((2 + Real.eulerMascheroniConstant - Real.log (4*Real.pi) : ℝ) : ℂ) := by
  have hsym : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
    simpa using completedRiemannZeta₀_one_sub 1
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = (Real.log (4*Real.pi) : ℂ) := by
    rw [Complex.ofReal_log (by positivity : 0 ≤ 4*Real.pi), Complex.ofReal_mul]
    norm_num
  rw [xi_derivative, xi_derivative, hsym, completedRiemannZeta₀_one, hlog]
  simp [xi]
  ring

/-- The logarithmic derivative of the genus-one product at its two regular
endpoints. Both expansions use the same constant b from exp(a+bs). -/
def HadamardLogDerivative : Prop :=
  ∃ b : ℂ, ∀ s : ℂ, s = 0 ∨ s = 1 →
    HasSum (fun z : ZeroCopy => (s - rho z)⁻¹ + (rho z)⁻¹)
      (deriv xi s / xi s - b)

theorem hadamard_mass_of_logDerivative (H : HadamardLogDerivative) :
    HasSum (fun z : ZeroCopy => hadamardTerm (rho z))
      (2 + Real.eulerMascheroniConstant - Real.log (4*Real.pi)) := by
  obtain ⟨b, h⟩ := H
  have hd := (h 1 (Or.inr rfl)).sub (h 0 (Or.inl rfl))
  have ht : HasSum (fun z : ZeroCopy => (rho z * (1 - rho z))⁻¹)
      (deriv xi 1 / xi 1 - deriv xi 0 / xi 0) := by
    convert hd using 1
    · funext z
      have hz : rho z ≠ 0 := by
        intro he
        have hpos := z.property.2.1
        change 0 < (rho z).re at hpos
        simp [he] at hpos
      have ho : (1:ℂ) ≠ rho z := by
        intro he
        have hlt := z.property.2.2.1
        change (rho z).re < 1 at hlt
        simp [← he] at hlt
      simp only [zero_sub, inv_neg]
      field_simp [hz, sub_ne_zero.mpr ho]
      ring
    · ring
  rw [xi_logDeriv_difference] at ht
  exact Complex.hasSum_re ht

end Mertens.Input
end
end

/-! ## Mertens/Mollifier.lean -/
section
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
end
end

/-! ## Mertens/PrimeConvergence.lean -/
section
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
end
end

/-! ## Mertens/Smoothing.lean -/
section
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
end
end

/-! ## Mertens/LandauTest.lean -/
section
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
end
end

/-! ## Mertens/InputProd.lean -/
section
/-! Absolute integrability of the double integral for the adjoint mollifier. -/
noncomputable section
open MeasureTheory
namespace Mertens.Input

theorem test_integrable_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {g : ℝ → E} (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => kernel p.1 • ((smoothBump n).normed volume (p.1 - p.2) • g p.2))
      ((volume.restrict window).prod volume) := by
  have hk : IntegrableOn kernel window := integrable_of_integral_eq_one kernel_mass
  obtain ⟨C, hC⟩ := ((smoothBump n).continuous_normed (μ := volume)).bounded_above_of_compact_support
    (smoothBump n).hasCompactSupport_normed
  have hφ : Continuous (fun p : ℝ × ℝ => (smoothBump n).normed volume (p.1-p.2)) :=
    (smoothBump n).continuous_normed.comp (continuous_fst.sub continuous_snd)
  apply ((hk.smul_prod hg).norm.const_mul C).mono'
    (hk.aestronglyMeasurable.fst.smul (hφ.aestronglyMeasurable.smul hg.aestronglyMeasurable.snd))
  exact ae_of_all _ (fun p => by
    simp only [norm_smul]
    calc
      ‖kernel p.1‖ * (‖(smoothBump n).normed volume (p.1 - p.2)‖ * ‖g p.2‖) ≤
          ‖kernel p.1‖ * (C * ‖g p.2‖) := by gcongr; exact hC _
      _ = C * (‖kernel p.1‖ * ‖g p.2‖) := by ring)

end Mertens.Input
end
end

/-! ## Mertens/TestPairing.lean -/
section
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
end
end

/-! ## Mertens/SmoothFourier.lean -/
section
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
end
end

/-! ## Mertens/Landau.lean -/
section
/-! Landau's explicit formula as a distribution on the positive logarithmic
axis. The hypothesis below applies uniformly to all smooth compact tests and
mentions neither the Logan kernel nor the witness interval. The hard number
theory is isolated in this source statement. -/
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff BigOperators
namespace Mertens.Input

/-- The normalized, real-test form of the explicit formula for the von Mangoldt
sum. This is the classical analytic source, including the absolutely summable
zero pairing for a smooth compact test; see Landau (1908), formula (39), and
Büthe (2015), the formula following (4.2), with r tending to 1. -/
def ClassicalSmoothLandau : Prop := ∀ φ : ℝ → ℝ,
  ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
  HasSum (fun z : ZeroCopy =>
    (∫ t : ℝ, (φ t : ℂ) * Complex.exp ((1/2 - rho z) * (t : ℂ)) / rho z).re)
    ((∫ t : ℝ, φ t * normalizedMangoldt t) - (∫ t : ℝ, φ t * trivialAt t))

theorem smooth_landau_of_classical (mass : ∫ u in window, kernel u = 1)
    (landau : ClassicalSmoothLandau) : SmoothLandauPairings := by
  intro n
  have h := landau (loganTest n) (loganTest_smooth mass n)
    (loganTest_compact n) (loganTest_positive_support n)
  simpa only [smooth_test_fourier n, testPair_mangoldt n, testPair_trivial n] using h

end Mertens.Input
end
end

/-! ## Mertens/Main.lean -/
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens
open Input

/-- Analytic facts at the interface with the literature. All quantities are
fixed by the paper. The mean of E₁, a negative value, and the location of a
witness are never allowed as inputs. -/
structure SourceInputs : Prop where
  /-- Finite-height checking of the critical line (Platt--Trudgian). -/
  critical : ∀ z : ZeroCopy, |(rho z).im| ≤ 10^10 → (rho z).re = 1/2
  /-- Logarithmic derivative of the Hadamard product for completed zeta. -/
  hadamard : HadamardLogDerivative
  /-- The numerical computation (8.1) of Büthe. The cutoff is proved finite. -/
  buthe : ∀ (f : lowBand.Finite), publishedSum f.toFinset ≤ -(100015419/100000000 : ℝ)
  /-- Absolute middle tail in Büthe, Lemma 6.3. -/
  middleTail : Summable rawMidReal ∧ (∑' z, rawMidReal z) ≤ middleMajorant
  /-- Absolute high tail in Büthe, Lemma 6.2, before multiplication by the
  maximal phase exp(omega/2). -/
  highTail : Summable rawHigh ∧ (∑' z, rawHigh z) ≤ highMajorant / Real.exp (omega/2)
  /-- The theta estimate in Dusart, Theorem 4.2. -/
  dusart : ∀ t : ℝ, 7713133853 ≤ t →
    |chebyshevTheta t - t| ≤ (1/100) * t / (Real.log t)^2
  /-- Landau's general distributional formula on the positive log axis, for
  every smooth compactly supported test. The specialization is proved. -/
  landau : ClassicalSmoothLandau

/-- The exact statement of the paper, from explicit analytic source facts.
The same witness supplies the strict margin, both log endpoints, the decimal
upper bound in Johnston's problem and the interval in Corollary 2. -/
theorem johnston_from_sources (H : SourceInputs) :
    ∃ x : ℝ, 0 < x ∧ 495702833109/10^9 < Real.log x ∧
      Real.log x < 495702833165/10^9 ∧ Real.sqrt x * error x < -(605/10^7:ℝ) ∧
      x < (191/100 : ℝ)*10^215 ∧ (26/10:ℝ)*10^103 < (60/10^6)*Real.sqrt x ∧
      ∀ t ∈ Icc (x - (60/10^6)*Real.sqrt x) x, error t < 0 := by
  have mass := kernel_mass
  have hmass := hadamard_mass_of_logDerivative H.hadamard
  have fin := lowBand_finite H.critical hmass.summable
  have mid := rawMid_from_real mass H.critical H.middleTail
  have hsquare (u : ℝ) (hu : u ∈ window) : squareAt u ≤ 1+3/(100*(247:ℝ)^2) := by
    have h := square_le_of_theta (u := u) (D := 1/(100*247^2)) (by norm_num)
      (fun _ ht => relative_theta H.dusart hu ht)
    convert h using 1
    ring
  have habs := summable_norm_wave fin H.critical mid.1 H.highTail.1
  have hlandau := smoothed_landau_hasSum mass habs (smooth_landau_of_classical mass H.landau)
  have hformula := explicit_formula_bands fin mass H.critical hlandau
  have heq : weightedMean kernel lo hi = lowSum fin.toFinset + middle + high +
      avg squareAt + avg higherAt + avg trivialAt := by
    rw [averaged_prime_power_split mass, hformula]
    ring
  obtain ⟨x,hx,hl,hr,he⟩ := transfer_to_witness fin mass H.critical hmass
    hadamard_constant_lt.le (H.buthe fin)
    (middle_bound_from_kernel H.critical mid.1 mid.2)
    (high_bound_from_kernel H.highTail.1 H.highTail.2) hsquare
    (fun _ hu => (higher_tail_lt (window_coarse hu).1).le) heq
  exact ⟨x,hx,hl,hr,he,consequences hx hl hr he⟩

end Mertens
end
end

/-! ## Mertens/Examples.lean -/
section
/-! Exact small-scale checks for the numerical examples in the proof map. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace Mertens

/-- The contribution of 2 to the constant cancels the deficit at x=2.
The Euler constant already exceeds 1/2. -/
theorem error_two_gt_half : (1/2 : ℝ) < error 2 := by
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  have h := constantTerm_summable.sum_le_tsum {two} (fun p _ => by
    have hp : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
    exact div_nonneg (Real.log_nonneg hp)
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp)))
  have hc : Real.log 2 / 2 ≤ ∑' p, constantTerm p := by
    convert h using 1; norm_num [two, constantTerm]
  have hs : primeSum 2 = Real.log 2 / 2 := by
    norm_num [primeSum, primeWeight, Finset.sum_range_succ, Nat.prime_two]
  rw [error, hs, mertensConstant]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- The value approached by the error from below at a positive integer. -/
def leftValue (p : ℕ) : ℝ :=
  (∑ i ∈ Finset.range p, primeWeight i) - Real.log p - mertensConstant

theorem error_left_limit {p : ℕ} (hp : 0 < p) :
    Tendsto error (𝓝[<] (p : ℝ)) (𝓝 (leftValue p)) := by
  cases p with
  | zero => omega
  | succ n =>
    have hstep : ∀ᶠ x : ℝ in 𝓝[<] (↑(n+1:ℕ) : ℝ),
        primeSum x = ∑ i ∈ Finset.range (n+1), primeWeight i := by
      have hlt : (n:ℝ) < (↑(n+1:ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
      filter_upwards [Ioo_mem_nhdsLT hlt] with x hx
      have hf : ⌊x⌋₊ = n := (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hx.1.le)).mpr
        ⟨hx.1.le, by simpa using hx.2⟩
      simp [primeSum, hf]
    have hcut := (tendsto_congr' hstep).mpr tendsto_const_nhds
    have hlog := (Real.continuousAt_log (by positivity : (↑(n+1:ℕ) : ℝ) ≠ 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (↑(n+1:ℕ) : ℝ)))
    exact (hcut.sub hlog).sub tendsto_const_nhds

/-- The logarithmic main term is continuous, so the entire jump is one prime weight. -/
theorem error_jump_at_prime {p : ℕ} (hp : p.Prime) :
    error (p : ℝ) - leftValue p = Real.log p / p := by
  simp [error, primeSum, leftValue, Finset.sum_range_succ, primeWeight, hp]

theorem error_jump_97 :
    error 97 - leftValue 97 = Real.log 97 / 97 := by
  exact_mod_cast error_jump_at_prime (p := 97) (by decide)

end Mertens
end
end

#check Mertens.error_two_gt_half
#check Mertens.error_left_limit
#check Mertens.error_jump_97
#check Mertens.johnston_from_sources
#print Mertens.SourceInputs
#print axioms Mertens.johnston_from_sources
