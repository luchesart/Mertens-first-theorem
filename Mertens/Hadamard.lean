import Mertens.Concrete
import Mertens.Components
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

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
