import Mertens.PrimeSplit

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
