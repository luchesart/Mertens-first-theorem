# A negative value in Mertens' first theorem

Lean 4 companion to Latchezar P. Tomov, *An explicit upper bound for the first sign change in Mertens' first theorem* (24 November 2026). The main declaration is `Mertens.johnston_from_sources` in `Mertens/Main.lean`. Its conclusion concerns the finite sum of `Real.log p / p` over genuine primes up to a real argument, with the convergent first Mertens constant.

For a single witness it gives both strict log endpoints 495.702833109 and 495.702833165, a normalized error less than −0.0000605, and the interval of negative values extending 0.000060√x to its left. The absolute length exceeds 2.6 × 10¹⁰³. Earlier sign changes are possible.

## Run the checks

Unzip the project and open the folder containing `lakefile.toml`. With elan installed, run these commands.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The toolchain is Lean 4.19.0. The manifest pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Fetching these dependencies for the first time requires network access. Open `index.html` in a browser for the proof map and the graphical examples in Appendices A-C: prime cutoffs and prime powers, kernel smoothing and changes in zero weights, the sign budget, and the interval of negativity. The Live folder contains the same proof concatenated as one independently checked Lean file, importing only Mathlib. It can also be downloaded from the interactive map.

## What Lean checks

The arithmetic functions use the right-continuous prime cutoff. Two small examples in `Mertens/Examples.lean` certify that the error exceeds one half at x = 2 and that its jump at 97 is exactly log(97)/97. The project proves convergence of the constant and the exact prime-power decomposition of the finite von Mangoldt sum. The result is averaged against the specific shifted Logan kernel. Its unit mass is proved by integrating the Bessel power series term by term, using exact polynomial moments. The square estimate is applied to the actual infinite tail of primes. Higher powers are bounded by a convergent comparison series, using a Rankin estimate in place of the paper's split at the cube root. The source-level tail estimates for the zeta zeros are converted into bounds on the phased contributions, including ordinates above the verified critical-line height.

Lean checks the Hadamard-constant enclosure, both hyperbolic numerical bounds, the inequalities involving 10⁻²⁹ and 10⁻⁵⁰⁰, and the final rational subtraction. It then extracts a negative value from a strict bound on the actual Bochner integral. Monotonicity of the finite prime sum extends the margin to the whole interval. `Mertens.Budget` also runs with Lean's standard library alone.

## Analytic inputs

The main theorem takes an explicit proposition, `Mertens.SourceInputs`. Its type can be inspected directly in the proof map or with `#print Mertens.SourceInputs`. The seven fields fix the following mathematical statements.

| Field | What the argument uses |
| --- | --- |
| `critical` | Verification that the actual zeta zeros up to 10¹⁰ lie on the critical line. |
| `hadamard` | The common regularized logarithmic derivative of the canonical product at 0 and 1. Lean derives the mass identity, preserving multiplicity, and proves the numerical enclosure of the resulting constant. |
| `buthe` | The value ≤ −1.00015419 of Büthe's weighted finite sum in equation (8.1), through height 4 × 10⁹. Finiteness of this band is proved before this input is used. |
| `middleTail`, `highTail` | The absolute unphased estimates in Büthe's Lemmas 6.3 and 6.2. Their numerical evaluations and the passage to signed, phased sums are checked. |
| `dusart` | The bound on the Chebyshev theta function, with coefficient 0.01, for t ≥ 7,713,133,853. |
| `landau` | The distributional form of Landau's explicit formula for every smooth compactly supported test on the positive log axis. Lean constructs the smoothed Logan tests, evaluates their pairings by Fubini, proves the limiting passage on both sides, and separates the three bands of zeros. Deriving the classical smooth-test identity itself from the pointwise formula is outside this project. |

The development proves an implication from these stated inputs. Büthe's finite sum and the finite-height zero verification enter as published results. The full Riemann hypothesis plays no role. The axiom audit checks logical foundations separately from the seven explicit mathematical hypotheses.

## References

- A. Hamieh, H. Kadiri, G. Martin and N. Ng, *Comparative prime number theory problem list*, problem 14 (D. R. Johnston). [arXiv:2407.03530](https://arxiv.org/abs/2407.03530)
- J. Büthe, *On the first sign change in Mertens' theorem*, Acta Arithmetica 171 (2015), 183–195, especially pp. 186, 190 and 194. [doi:10.4064/aa171-2-5](https://doi.org/10.4064/aa171-2-5)
- E. Landau, *Nouvelle démonstration pour la formule de Riemann…*, Annales scientifiques de l'École Normale Supérieure 25 (1908), 399–442, formula (39). [doi:10.24033/asens.595](https://doi.org/10.24033/asens.595)
- D. Platt and T. Trudgian, *The Riemann hypothesis is true up to 3·10¹²*, Bulletin of the London Mathematical Society 53 (2021), 792–797. [doi:10.1112/blms.12460](https://doi.org/10.1112/blms.12460)
- P. Dusart, *Explicit estimates of some functions over primes*, Ramanujan Journal 45 (2018), 227–251, Theorem 4.2. [doi:10.1007/s11139-016-9839-4](https://doi.org/10.1007/s11139-016-9839-4)
