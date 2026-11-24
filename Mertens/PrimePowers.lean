import Mertens.Analysis
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Equation (1) for the actual von Mangoldt sum. Positive integer exponents
of at least two are indexed by k+2, including when the cutoff is a prime power. -/

noncomputable section
open scoped BigOperators
open ArithmeticFunction Set
namespace Mertens

def powerWeight (p : Nat.Primes) (k : ℕ) : ℝ := Real.log p / (p : ℝ) ^ (k + 2)

theorem powerWeight_nonneg (p : Nat.Primes) (k : ℕ) : 0 ≤ powerWeight p k := by
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
  exact div_nonneg (Real.log_nonneg hp) (pow_nonneg (by positivity) _)

/-- The geometric series at each prime is exactly its contribution to E. -/
theorem powerWeight_hasSum (p : Nat.Primes) : HasSum (powerWeight p) (constantTerm p) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hg := hasSum_geometric_of_lt_one (inv_nonneg.mpr hp0.le) ((inv_lt_one₀ hp0).mpr hp)
  convert hg.mul_left (Real.log p / (p : ℝ) ^ 2) using 1
  · ext k
    simp only [powerWeight, pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  · unfold constantTerm
    field_simp [hp0.ne', (by linarith : (p : ℝ) - 1 ≠ 0)]
    ring

private def inside (x : ℝ) (p : Nat.Primes) : Set ℕ :=
  {k | (p : ℕ) ^ (k + 2) ≤ ⌊x⌋₊}

def includedPowers (x : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' k, (inside x p).indicator (powerWeight p) k

def omittedPowers (x : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' k, (inside x p)ᶜ.indicator (powerWeight p) k

/-- P(x) in the paper. -/
def primePowerTail (x : ℝ) : ℝ := ∑' p : Nat.Primes, omittedPowers x p

theorem split_at_prime (x : ℝ) (p : Nat.Primes) :
    includedPowers x p + omittedPowers x p = constantTerm p := by
  have h := (powerWeight_hasSum p).summable
  unfold includedPowers omittedPowers
  rw [← (h.indicator (inside x p)).tsum_add (h.indicator (inside x p)ᶜ)]
  simpa only [Set.indicator_self_add_compl_apply] using (powerWeight_hasSum p).tsum_eq

theorem prime_power_partition (x : ℝ) :
    (∑' p : Nat.Primes, includedPowers x p) + primePowerTail x =
      ∑' p : Nat.Primes, constantTerm p := by
  have hi (p : Nat.Primes) : 0 ≤ includedPowers x p :=
    tsum_nonneg fun k => Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
  have ho (p : Nat.Primes) : 0 ≤ omittedPowers x p :=
    tsum_nonneg fun k => Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
  have his := constantTerm_summable.of_nonneg_of_le hi
    (fun p => by linarith [split_at_prime x p, ho p])
  have hos := constantTerm_summable.of_nonneg_of_le ho
    (fun p => by linarith [split_at_prime x p, hi p])
  rw [primePowerTail, ← his.tsum_add hos]
  exact tsum_congr (split_at_prime x)

def tailWeight (x : ℝ) (p : Nat.Primes) (k : ℕ) : ℝ :=
  if x < (p : ℝ) ^ (k + 2) then powerWeight p k else 0

private theorem tailWeight_indicator {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) (k : ℕ) :
    tailWeight x p k = (inside x p)ᶜ.indicator (powerWeight p) k := by
  classical
  simp [tailWeight, inside, Set.indicator, Nat.le_floor_iff hx, Nat.cast_pow, not_le]

theorem tails_by_exponent {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun k => ∑' p : Nat.Primes, tailWeight x p k) ∧
    primePowerTail x = ∑' k, ∑' p : Nat.Primes, tailWeight x p k := by
  have hrow (p : Nat.Primes) : Summable (tailWeight x p) := by
    simpa only [funext (tailWeight_indicator hx p)] using
      ((powerWeight_hasSum p).summable.indicator (inside x p)ᶜ)
  have hrowSum (p : Nat.Primes) : (∑' k, tailWeight x p k) = omittedPowers x p :=
    tsum_congr (tailWeight_indicator hx p)
  have hpos (p : Nat.Primes) (k : ℕ) : 0 ≤ tailWeight x p k := by
    rw [tailWeight_indicator hx p k]
    exact Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
  have hsum : Summable (fun p : Nat.Primes => ∑' k, tailWeight x p k) := by
    apply constantTerm_summable.of_nonneg_of_le (fun p => tsum_nonneg (hpos p))
    intro p
    rw [hrowSum]
    have h : 0 ≤ includedPowers x p :=
      tsum_nonneg fun k => Set.indicator_nonneg (fun k _ => powerWeight_nonneg p k) _
    linarith [split_at_prime x p]
  have hall : Summable (Function.uncurry (tailWeight x)) :=
    (summable_prod_of_nonneg (fun pk => hpos pk.1 pk.2)).mpr ⟨hrow, hsum⟩
  refine ⟨hall.prod_symm.prod, ?_⟩
  calc
    primePowerTail x = ∑' p : Nat.Primes, ∑' k, tailWeight x p k := (tsum_congr hrowSum).symm
    _ = _ := hall.tsum_comm.symm

/-- The sum A(x), including the weight at the endpoint. -/
def mangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), vonMangoldt n / (n : ℝ)

private def cutoffWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n ≤ ⌊x⌋₊ then vonMangoldt n / (n : ℝ) else 0

private theorem mangoldt_eq_tsum (x : ℝ) :
    HasSum (cutoffWeight x) (mangoldtSum x) := by
  let s := Finset.range (⌊x⌋₊ + 1)
  have hf (n : ℕ) (hn : n ∉ s) : cutoffWeight x n = 0 := by
    have : ¬ n ≤ ⌊x⌋₊ := by simpa [s, Nat.lt_succ_iff] using hn
    simp [cutoffWeight, this]
  convert hasSum_sum_of_ne_finset_zero hf using 1
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have h : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  simp [cutoffWeight, h]

private theorem primes_eq_tsum (x : ℝ) :
    (∑' p : Nat.Primes, cutoffWeight x p) = primeSum x := by
  classical
  change (∑' p : {n : ℕ | n.Prime}, cutoffWeight x p) = primeSum x
  rw [tsum_subtype]
  let s := Finset.range (⌊x⌋₊ + 1)
  rw [tsum_eq_sum (s := s)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have h : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    by_cases hp : n.Prime <;> simp [Set.indicator, hp, primeWeight, cutoffWeight, h,
      ArithmeticFunction.vonMangoldt_apply_prime]
  · intro n hn
    have h : ¬ n ≤ ⌊x⌋₊ := by simpa [s, Nat.lt_succ_iff] using hn
    by_cases hp : n.Prime <;> simp [Set.indicator, hp, cutoffWeight, h]

theorem mangoldt_split (x : ℝ) :
    mangoldtSum x = primeSum x + ∑' p : Nat.Primes, includedPowers x p := by
  have hf := mangoldt_eq_tsum x
  have hs : Function.support (cutoffWeight x) ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hp
    have h : vonMangoldt n = 0 := vonMangoldt_eq_zero_iff.mpr hp
    exact hn (by simp [cutoffWeight, h])
  rw [← hf.tsum_eq, tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers
    hf.summable hs, primes_eq_tsum]
  congr 1
  apply tsum_congr
  intro p
  apply tsum_congr
  intro k
  by_cases h : (p : ℕ) ^ (k + 2) ≤ ⌊x⌋₊ <;>
    simp [cutoffWeight, Set.indicator, inside, h, Nat.cast_pow, powerWeight,
      vonMangoldt_apply_pow (by omega : k + 2 ≠ 0), vonMangoldt_apply_prime p.prop]

/-- The signed decomposition used before applying the explicit formula. -/
theorem prime_power_identity (x : ℝ) :
    error x = mangoldtSum x - Real.log x + Real.eulerMascheroniConstant + primePowerTail x := by
  rw [error, mertensConstant, mangoldt_split]
  linarith [prime_power_partition x]

end Mertens
