import Mertens.Analysis
import Mertens.Components
import Mertens.Concrete
import Mertens.RealBudget
import Mertens.Exponential
import Mertens.ZeroTailBounds

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
