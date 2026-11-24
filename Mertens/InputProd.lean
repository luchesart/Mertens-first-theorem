import Mertens.LoganMass
import Mertens.Mollifier

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
