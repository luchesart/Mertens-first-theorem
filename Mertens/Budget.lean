import Std

/-!
# Exact arithmetic for the first Mertens error

All decimals in the paper are rational numbers. This module uses signed
numerators and positive denominators, without any floating point arithmetic
or dependencies beyond Lean's standard library. There is no need to reduce
fractions to lowest terms: their cross products determine equality and order.
The companion real-valued proof interprets these same expressions in ℝ.
-/

set_option exponentiation.threshold 1024
set_option maxRecDepth 4096

namespace Mertens.Budget

structure Fraction where
  num : Int
  den : Nat
  positive : 0 < den

def frac (n : Int) (d : Nat) (h : 0 < d := by decide) : Fraction :=
  ⟨n, d, h⟩

instance : Add Fraction where
  add a b :=
    ⟨a.num * (b.den : Int) + b.num * (a.den : Int),
     a.den * b.den, Nat.mul_pos a.positive b.positive⟩

instance : Mul Fraction where
  mul a b :=
    ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.positive b.positive⟩

/-- Equality as numbers, irrespective of the chosen denominators. -/
abbrev same (a b : Fraction) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

/-- Strict order by cross multiplication. -/
abbrev less (a b : Fraction) : Prop :=
  a.num * (b.den : Int) < b.num * (a.den : Int)

def center         := frac 495702833137 1000000000
def radius         := frac 28 1000000000
def leftEndpoint   := frac 495702833109 1000000000
def rightEndpoint  := frac 495702833165 1000000000

/-- The window uses exactly the center and radius of Büthe's computation. -/
theorem window_endpoints :
    same (leftEndpoint + radius) center ∧ same (center + radius) rightEndpoint := by
  decide

theorem cutoff_parameters :
    same (radius * frac (10^10) 1) (frac 280 1) ∧
    same (frac 4 10 * frac (10^10) 1) (frac (4 * 10^9) 1) := by
  decide

def publishedCap   := frac (-100015419) 100000000
def massCap        := frac 46192 1000000
def coefficientCap := frac 46192000 495702833137
def middleCap      := frac 116 (10^13)
def highCap        := frac 109 (10^14)
def squareExcess   := frac 3 (100 * 247^2)
def squareCap      := frac 1 1 + squareExcess
def higherCap      := frac 1 (10^29)
def trivialCap     := frac 1 (10^500)
def meanTarget     := frac (-6051) (10^8)
def witnessTarget  := frac (-605) (10^7)

/-- The cap for the removed coefficient is the mass cap divided by ω. -/
theorem coefficient_cap_scaling : same (coefficientCap * center) massCap := by
  decide

/-- The square-tail bound is 1 + 3D, with D = 0.01/247². -/
theorem square_excess_scaling :
    same squareExcess (frac 3 1 * frac 1 (100 * 247^2)) := by
  decide

/-- The exact upper bound after combining all seven estimates. -/
def upperBound : Fraction :=
  publishedCap + coefficientCap + middleCap + highCap + squareCap + higherCap + trivialCap

/-- Even the upward-rounded inputs leave a mean strictly below −0.00006051. -/
theorem upperBound_lt : less upperBound meanTarget := by
  decide

theorem meanTarget_lt_witnessTarget : less meanTarget witnessTarget := by
  decide

end Mertens.Budget
