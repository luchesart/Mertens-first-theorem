import Mertens.Analysis

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
