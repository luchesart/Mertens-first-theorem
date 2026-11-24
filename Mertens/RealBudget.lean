import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mertens.Budget

set_option exponentiation.threshold 1024

namespace Mertens.Budget

/-- Interpret a positive-denominator fraction as an actual real number. -/
noncomputable def toReal (q : Fraction) : ℝ := (q.num : ℝ) / (q.den : ℝ)

theorem toReal_add (a b : Fraction) :
    toReal (a + b) = toReal a + toReal b := by
  have ha : (0 : ℝ) < a.den := by exact_mod_cast a.positive
  have hb : (0 : ℝ) < b.den := by exact_mod_cast b.positive
  change (((a.num * (b.den : ℤ) + b.num * (a.den : ℤ) : ℤ) : ℝ) /
    ((a.den * b.den : ℕ) : ℝ)) = (a.num : ℝ) / a.den + (b.num : ℝ) / b.den
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]

theorem toReal_lt {a b : Fraction} (h : less a b) : toReal a < toReal b := by
  have ha : (0 : ℝ) < a.den := by exact_mod_cast a.positive
  have hb : (0 : ℝ) < b.den := by exact_mod_cast b.positive
  apply (div_lt_div_iff₀ ha hb).2
  change a.num * (b.den : ℤ) < b.num * (a.den : ℤ) at h
  exact_mod_cast h

/-- The real form of the exact common-denominator computation. -/
theorem real_upperBound_lt : toReal upperBound < -(6051/100000000 : ℝ) := by
  calc
    toReal upperBound < toReal meanTarget := toReal_lt upperBound_lt
    _ = -(6051/100000000 : ℝ) := by norm_num [toReal, meanTarget, frac]

end Mertens.Budget

namespace Mertens

open Budget

/-- Add the individual analytic estimates and Büthe's published input.
The argument uses one-sided errors throughout, as the goal is an upper
bound. The scalar comparisons are proved in the standard library module. -/
theorem mean_lt_target {I published low middle high squares higher trivial : ℝ}
    (hsplit : I ≤ low + middle + high + squares + higher + trivial)
    (hpub : published ≤ -(100015419/100000000 : ℝ))
    (hlow : low - published ≤ (46192/1000000 : ℝ)/(495702833137/1000000000 : ℝ))
    (hmiddle : middle ≤ 116/(10 : ℝ)^13)
    (hhigh : high ≤ 109/(10 : ℝ)^14)
    (hsquares : squares ≤ 1 + 3/(100*(247 : ℝ)^2))
    (hhigher : higher ≤ 1/(10 : ℝ)^29)
    (htrivial : trivial ≤ 1/(10 : ℝ)^500) :
    I < -(605/10000000 : ℝ) := by
  have hlow' : low ≤ toReal publishedCap + toReal coefficientCap := by
    norm_num [toReal, publishedCap, coefficientCap, frac] at hpub hlow ⊢
    linarith only [hpub, hlow]
  have hm : middle ≤ toReal middleCap := by
    norm_num [toReal, middleCap, frac] at hmiddle ⊢
    exact hmiddle
  have hh : high ≤ toReal highCap := by
    norm_num [toReal, highCap, frac] at hhigh ⊢
    exact hhigh
  have hs : squares ≤ toReal squareCap := by
    unfold squareCap
    rw [toReal_add]
    norm_num [toReal, squareExcess, frac] at hsquares ⊢
    exact hsquares
  have hp : higher ≤ toReal higherCap := by
    norm_num [toReal, higherCap, frac] at hhigher ⊢
    exact hhigher
  have ht : trivial ≤ toReal trivialCap := by
    norm_num [toReal, trivialCap, frac] at htrivial ⊢
    exact htrivial
  have hi : I ≤ toReal upperBound := by
    unfold upperBound
    simp only [toReal_add]
    exact le_trans hsplit
      (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hlow' hm) hh) hs) hp) ht)
  have tight := lt_of_le_of_lt hi (toReal_lt upperBound_lt)
  have hw := lt_trans tight (toReal_lt meanTarget_lt_witnessTarget)
  norm_num [toReal, witnessTarget, frac] at hw ⊢
  exact hw

end Mertens
