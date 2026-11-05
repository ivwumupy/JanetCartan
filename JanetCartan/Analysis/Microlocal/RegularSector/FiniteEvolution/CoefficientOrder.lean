module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution

/-!
# One finite original coefficient order for the actual sector factors

The low graph order alone need not control the coefficient term at output
order one. Fix one larger original order before the varying fields. It covers
both retarded orientations' `L² → H¹` and `H⁻¹ → L²` constants, as well as
all four direct PDO low budgets. No arbitrarily high low norm is inferred
from the original `C¹⁰` amplitude construction.
Consumer: `FixedDomainInverse.exists_fixed_cutoffs_localSobolevInverse`, via
the complete residual of `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic.UniformEvolution FourierIntegral.FullLowBounds
open scoped Matrix.Norms.Frobenius

/-- A single order covering the retarded low construction, its gain-one
coefficient term, and the algebraic and endpoint PDOs (`finite-gap-theorem`). -/
def sectorLowOrder (d : ℕ) : ℕ :=
  max (retardedCoefficientOrder d) (max (fullLowReserve (d+1) + 13) (2 * (d+2) + 11))

/-- All three low requirements follow from the fixed sector order; the
algebraic PDO order `2*(d+2)+2` is smaller than the last one. -/
theorem sectorLowOrder_bounds (d : ℕ) :
    retardedCoefficientOrder d ≤ sectorLowOrder d ∧
      fullLowReserve (d+1) + 13 ≤ sectorLowOrder d ∧
      2 * (d+2) + 11 ≤ sectorLowOrder d := by
  unfold sectorLowOrder
  omega

/-- The gain-one coefficient term is uniformly controlled on this fixed
neighborhood. It is the SAME profile and order used in the signed retarded
and genuine restriction `H¹` estimates (`finite-gap-theorem`). -/
theorem retarded_gain_one_profile_le {d : ℕ} (KQ : Set (Euclidean (d+1)))
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (B : Euclidean (d+1) → MetricTensor (d+1)) {M : ℝ}
    (hQ : cNorm KQ (sectorLowOrder d) Q ≤ M)
    (hB : cNorm KQ (sectorLowOrder d) B ≤ M) :
    1 + retardedCoefficientProfile KQ Q B (1 + (fullLowReserve (d+1) + 2)) ≤
      2 + 2 * M := by
  have hq := (cNorm_mono_order (show 1 + (fullLowReserve (d+1) + 2) + 10 ≤
    sectorLowOrder d by have := (sectorLowOrder_bounds d).2.1; omega)).trans hQ
  have hb := (cNorm_mono_order (show 1 + (fullLowReserve (d+1) + 2) + 9 ≤
    sectorLowOrder d by have := (sectorLowOrder_bounds d).2.1; omega)).trans hB
  dsimp only [retardedCoefficientProfile]
  linarith

end JanetCartan.RegularSector.FiniteEvolution
