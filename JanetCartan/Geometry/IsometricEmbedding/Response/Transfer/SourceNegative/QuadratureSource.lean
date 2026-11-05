module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureNorm
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.SupportedSource
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Pairing
/-!
# Original supported source and its real quadratures

Restriction and zero extension commute with the two literal real quadratures
of the original cutoff source. Combined with the constant-one Fourier comparison,
this supplies the exact source norm in `app:ch_regular:eq:inverse-remainder`.
The cutoff, measure and original amplitude are unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace JanetCartan.ResponseTransfer.SourceNegative
open RegularSector.Characteristic.RetardedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)

/-- A real quadrature is one fixed fiber map on the original L² source
(`app:ch_response:eq:response-actual-solver-formula`). -/
private theorem quadrature_eq_compLp {μ : Measure E} (c : ℂ) (u : Lp F 2 μ) :
    l2RealPart μ (c • u) =
      (euclideanRealPart.comp ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ)).compLp u := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (c • u), Lp.coeFn_smul c u,
    (euclideanRealPart.comp ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ)).coeFn_compLp u]
    with x hr hs hc
  change (l2RealPart μ (c • u)) x = euclideanRealPart ((c • u) x) at hr
  simp only [hr, hs, Pi.smul_apply, hc]
  rfl

/-- The real source used by the local inverse extends to exactly the original
real quadrature, with no new source projection. The support is supplied by the
original cutoff (`app:ch_regular:eq:inverse-remainder`). -/
theorem zeroExtend_restrictL2_modulatedSource_real_quadrature
    {W : Set E} (hW : MeasurableSet W) (χ φ : E → ℝ)
    (f : E → F) (lam : ℝ) (hs : tsupport χ ⊆ W)
    (hm : MemLp (modulatedSource χ φ f lam) 2 volume) (c : ℂ) :
    SmallSupport.zeroExtend hW
        (l2RealPart (volume.restrict W)
          (c • restrictL2 W (hm.toLp (modulatedSource χ φ f lam)))) =
      l2RealPart volume (c • hm.toLp (modulatedSource χ φ f lam)) := by
  rw [quadrature_eq_compLp, ← ArbitraryAccuracy.ResidualLocalization.compLp_zeroExtend,
    zeroExtend_restrictL2_modulatedSource hW χ φ f lam hs hm, ← quadrature_eq_compLp]

/-- Both original real quadratures satisfy the inverse consumer's negative
component norm bound with the SAME vector-source norm and constant one. Take
`c = 1` or `c = -Complex.I` for the real and imaginary parts in
`app:ch_response:eq:response-actual-solver-formula`. No residual output is used
as a negative-order datum (`app:ch_regular:eq:inverse-remainder`). -/
theorem modulatedSource_real_quadrature_negative_norm_le
    {W : Set E} (hW : MeasurableSet W) (χ φ : E → ℝ)
    (f : E → F) (lam : ℝ) (hs : tsupport χ ⊆ W)
    (hm : MemLp (modulatedSource χ φ f lam) 2 volume) (N : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    ArbitraryAccuracy.componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin q) ℝ)
        (-(N : ℝ)) (SmallSupport.zeroExtend hW
          (l2RealPart (volume.restrict W)
            (c • restrictL2 W (hm.toLp (modulatedSource χ φ f lam))))) ≤
      Pseudodifferential.vectorFourierSobolevNorm (-(N : ℝ))
        (hm.toLp (modulatedSource χ φ f lam)) := by
  rw [zeroExtend_restrictL2_modulatedSource_real_quadrature hW χ φ f lam hs hm c]
  exact (real_quadrature_fourierSobolev_bound
    (fun _ ↦ Pseudodifferential.memFourierSobolev_of_nonpos
      (neg_nonpos.mpr (Nat.cast_nonneg N)) _) c hc).2
end JanetCartan.ResponseTransfer.SourceNegative
