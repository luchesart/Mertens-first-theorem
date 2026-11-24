import Mertens.Transfer
import Mertens.Averaging
import Mertens.HigherPowers
import Mertens.PrimeSquares
import Mertens.EulerBound
import Mertens.Spectral
import Mertens.ZeroBands
import Mertens.FiniteZeros
import Mertens.LoganMass
import Mertens.Hadamard
import Mertens.Landau

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
