import Mertens.Concrete

/-! # A direct prime-square estimate
Integrating the finite counting function of primes in (y,t) gives an
upper bound for each finite subsum. This establishes convergence as well
as the prime-square estimate used in the transfer. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Mertens.Input

private def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private theorem primeLog_nonneg (n : ℕ) : 0 ≤ primeLog n := by
  unfold primeLog
  split_ifs with hn
  · exact Real.log_nonneg (by exact_mod_cast hn.one_le)
  · exact le_rfl

private theorem count_between (s : Finset Nat.Primes) {y t : ℝ} (hy : 0 < y) (hyt : y < t) :
    chebyshevTheta y + (∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0)
      ≤ chebyshevTheta t := by
  classical
  let selected : Finset Nat.Primes := s.filter (fun p : Nat.Primes => y < (p : ℝ) ∧ (p : ℝ) < t)
  let a := selected.map (Function.Embedding.subtype Nat.Prime)
  let ry := Finset.range (⌊y⌋₊ + 1)
  let rt := Finset.range (⌊t⌋₊ + 1)
  have ha : ∀ n ∈ a, y < (n : ℝ) ∧ (n : ℝ) < t := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    exact (Finset.mem_filter.mp hp).2
  have hd : Disjoint ry a := by
    apply Finset.disjoint_left.mpr
    intro n hn hna
    have hn' : n ≤ ⌊y⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    exact (not_lt_of_ge ((Nat.le_floor_iff hy.le).mp hn')) (ha n hna).1
  have hs : ry ∪ a ⊆ rt := by
    intro n hn
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    rcases Finset.mem_union.mp hn with hl | hr
    · exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)).trans (Nat.floor_mono hyt.le)
    · exact Nat.le_floor (ha n hr).2.le
  have hsum : (∑ n ∈ a, primeLog n) =
      ∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    change (∑ n ∈ selected.map _, primeLog n) = ∑ p ∈ selected, _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p _
    exact if_pos p.prop
  change (∑ n ∈ ry, primeLog n) + _ ≤ ∑ n ∈ rt, primeLog n
  rw [← hsum, ← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => primeLog_nonneg i)

private theorem pow_int_three {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ in Ioi y, t ^ (-3 : ℝ)) = 1 / (2 * y^2) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hy]
  have hh : y ^ (-2 : ℝ) = (y^2)⁻¹ := by rw [Real.rpow_neg hy.le]; norm_num
  norm_num [hh]; ring

private theorem pow_int_two {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ in Ioi y, t ^ (-2 : ℝ)) = 1 / y := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy]
  have hh : y ^ (-1 : ℝ) = y⁻¹ := by rw [Real.rpow_neg hy.le, Real.rpow_one]
  norm_num [hh, one_div]

private def step (y : ℝ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  if y < (p : ℝ) then
    (Ioi (p : ℝ)).indicator (fun v : ℝ => Real.log (p : ℝ) * v ^ (-3 : ℝ)) t else 0

private theorem step_int {y : ℝ} (hy : 0 < y) (p : Nat.Primes) :
    IntegrableOn (step y p) (Ioi y) := by
  by_cases hp : y < (p : ℝ)
  · have he : step y p = (Ioi (p : ℝ)).indicator
        (fun v : ℝ => Real.log (p : ℝ) * v ^ (-3 : ℝ)) := funext fun _ => if_pos hp
    rw [he]
    exact (((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hy).const_mul
        (Real.log (p : ℝ))).indicator measurableSet_Ioi)
  · have he : step y p = (fun _ : ℝ => (0 : ℝ)) := funext fun _ => if_neg hp
    rw [he]
    exact integrable_zero _ _ _

private theorem step_value {y : ℝ} (hy : 0 < y) (p : Nat.Primes) :
    (∫ t in Ioi y, step y p t) =
      (if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0) / 2 := by
  by_cases hp : y < (p : ℝ)
  · simp only [step, hp, if_true, setIntegral_indicator measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_right hp.le, integral_const_mul, pow_int_three (hy.trans hp)]
    ring
  · simp [step, hp]

private theorem step_bound (s : Finset Nat.Primes) {y D t : ℝ} (hy : 0 < y) (hyt : y < t)
    (hθ : ∀ v, y ≤ v → |chebyshevTheta v - v| ≤ D*v) :
    (∑ p ∈ s, step y p t) ≤
      (1 + D) * t ^ (-2 : ℝ) - ((1 - D) * y) * t ^ (-3 : ℝ) := by
  classical
  have ht : 0 < t := hy.trans hyt
  have hcount := count_between s hy hyt
  have h1 := (abs_le.mp (hθ y le_rfl)).1
  have h2 := (abs_le.mp (hθ t hyt.le)).2
  have hcut : (∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0)
      ≤ (1+D)*t-(1-D)*y := by linarith
  have hm := mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg ht.le (-3 : ℝ))
  have heq : (∑ p ∈ s, step y p t) =
      (∑ p ∈ s, if y < (p : ℝ) ∧ (p : ℝ) < t then Real.log (p : ℝ) else 0) * t^(-3 : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : y < (p : ℝ) <;> by_cases k : (p : ℝ) < t <;> simp [step,h,k, Set.indicator, Set.mem_Ioi]
  have hpow : t * t ^ (-3 : ℝ) = t ^ (-2 : ℝ) := by
    calc t * t ^ (-3 : ℝ) = t ^ (1 : ℝ) * t ^ (-3 : ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [← Real.rpow_add ht]; norm_num
  rw [heq]
  apply hm.trans_eq
  rw [sub_mul, mul_assoc, hpow]

private theorem finite_square_bound {y D : ℝ} (hy : 0 < y)
    (hθ : ∀ t, y ≤ t → |chebyshevTheta t - t| ≤ D*t) (s : Finset Nat.Primes) :
    (∑ p ∈ s, if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0) ≤ (1+3*D)/y := by
  have hi2 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hy).const_mul (1 + D)
  have hi3 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hy).const_mul ((1 - D) * y)
  have h := setIntegral_mono_on (integrable_finset_sum s (fun p _ => step_int hy p))
         (hi2.sub hi3) measurableSet_Ioi (fun t ht => step_bound s hy ht hθ)
  simp only [Pi.sub_apply] at h
  rw [integral_finset_sum s (fun p _ => step_int hy p), integral_sub hi2 hi3,
     integral_const_mul, integral_const_mul, pow_int_two hy, pow_int_three hy] at h
  simp_rw [step_value hy] at h
  rw [← Finset.sum_div] at h
  have heq : (1 + D) * (1 / y) - ((1-D)*y) * (1/(2*y^2)) = ((1+3*D)/y)/2 := by
    field_simp [hy.ne']; ring
  rw [heq] at h
  linarith

/-- Dusart's relative theta bound alone bounds the actual prime-square tail. -/
theorem square_le_of_theta {u D : ℝ} (_hD : 0 ≤ D)
    (hθ : ∀ t, Real.sqrt (Real.exp u) ≤ t → |chebyshevTheta t - t| ≤ D*t) :
    squareAt u ≤ 1+3*D := by
  let y := Real.sqrt (Real.exp u)
  have hy : 0 < y := Real.sqrt_pos.2 (Real.exp_pos _)
  let f (p : Nat.Primes) := if y < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ)^2 else 0
  have hnon : 0 ≤ f := by
    intro p
    dsimp [f]
    split_ifs
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (sq_nonneg _)
    · exact le_rfl
  have hb (s : Finset Nat.Primes) : (∑ p ∈ s, f p) ≤ (1+3*D)/y :=
    finite_square_bound hy hθ s
  have h := (summable_of_sum_le hnon hb).tsum_le_of_sum_le hb
  change y * (∑' p, f p) ≤ _
  rw [mul_comm]
  exact (le_div_iff₀ hy).mp h

end Mertens.Input
