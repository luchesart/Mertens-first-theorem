import Mertens.Smoothing
import Mertens.SmoothFourier
import Mertens.TestPairing

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
