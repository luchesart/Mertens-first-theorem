import Mathlib

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
