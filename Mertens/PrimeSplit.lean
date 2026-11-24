import Mertens.Concrete
import Mertens.PrimePowers

noncomputable section
namespace Mertens

/-- The expression to which Landau's smoothed explicit formula is applied. -/
def normalizedMangoldt (u : ℝ) : ℝ :=
  Real.sqrt (Real.exp u) *
    (mangoldtSum (Real.exp u) - u + Real.eulerMascheroniConstant)

/-- Equation (1), normalised, with the prime squares and higher powers in exactly
the order used in the two estimates in section 4. -/
theorem normalized_prime_power_split (u : ℝ) :
    normalized u = normalizedMangoldt u + Input.squareAt u + Input.higherAt u := by
  have h := tails_by_exponent (Real.exp_pos u).le
  let row := fun k : ℕ => ∑' p : Nat.Primes, tailWeight (Real.exp u) p k
  have hzero :
      row 0 = ∑' p : Nat.Primes, if Real.sqrt (Real.exp u) < (p : ℝ)
        then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0 := by
    apply tsum_congr
    intro p
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    simp only [tailWeight, powerWeight, zero_add, Real.sqrt_lt' hp]
  have hsuc (k : ℕ) : row (k + 1) = Input.primePowerTail (k + 3) (Real.exp u) := by
    apply tsum_congr
    intro p
    simp only [tailWeight, powerWeight, Nat.add_assoc]
  have htail : primePowerTail (Real.exp u) = row 0 + ∑' k, Input.primePowerTail (k+3) (Real.exp u) := by
    calc
      _ = ∑' k, row k := h.2
      _ = row 0 + ∑' k : ℕ, row (k + 1) := h.1.tsum_eq_zero_add
      _ = _ := congrArg (row 0 + ·) (tsum_congr hsuc)
  rw [normalized, prime_power_identity, Real.log_exp, htail, hzero]
  unfold normalizedMangoldt Input.squareAt Input.higherAt
  ring

end Mertens
