module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets.DominatedIntegral
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets.JetBounds

/-!
# Off-diagonal smoothness and rapid decay of the Bessel heat integral

For `app:ch_background:prop:bg-frame`, Step 1, the explicit normalized heat
integral is integrable off the diagonal and has uniform exponential decay
outside every positive gap. Its positive-time spatial jets are jointly smooth
and measurable. The Gaussian estimates in `JetBounds` give integrable time
majorants for every polynomially weighted spatial jet. Substituting these
majorants into `DominatedIntegral` proves off-diagonal smoothness and rapid
decay of every kernel derivative. These unconditional results supply the
heat-integral input for the lattice-remainder construction.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The explicit normalized Bessel heat integral is smooth away from the origin
(`app:ch_background:prop:bg-frame`, Step 1). Differentiation under the integral
is justified by the integrable Gaussian jet majorants in `JetBounds`. This is
the smoothness input for the nonzero-translate lattice remainder. -/
theorem contDiffOn_imageBesselKernel_offDiagonal :
    ContDiffOn ℝ ∞ (imageBesselKernel (d := d)) {x : E | x ≠ 0} :=
  (imageBesselKernel_offDiagonal_of_integrable_jet_bounds
    (exists_imageBesselKernel_integrand_jet_majorant (d := d))).1

/-- Every spatial derivative of the actual Bessel kernel decays faster than
any polynomial outside a positive gap (`app:ch_background:prop:bg-frame`,
Step 1). This supplies the uniform jet estimates for differentiating the
nonzero-translate lattice series. -/
theorem exists_imageBesselKernel_offDiagonal_jet_decay (δ : ℝ) (hδ : 0 < δ)
    (n m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, δ ≤ ‖x‖ →
      (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ n imageBesselKernel x‖ ≤ C :=
  (imageBesselKernel_offDiagonal_of_integrable_jet_bounds
    (exists_imageBesselKernel_integrand_jet_majorant (d := d))).2 δ hδ n m

end JanetCartan.ContinuumNormalReduction.ImageNormal
