import Mertens.Concrete
import Mertens.Components

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
