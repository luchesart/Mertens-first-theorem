import Mertens.KernelSymmetry
import Mertens.ZeroTailBounds

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
