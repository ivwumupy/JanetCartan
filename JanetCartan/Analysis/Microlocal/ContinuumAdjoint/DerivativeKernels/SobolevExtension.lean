module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SobolevExtension.Limits
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Density
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization

/-!
# Extending the compact raw adjoint bound to all Sobolev data

For `app:ch_background:prop:bg-adjoint`, compact smooth density and lower
semicontinuity of the shared physical Fourier norm extend the raw estimate
for the same bounded measurement-to-carrier operator. Both constants and
the partial unitary radian inverse are unchanged.

The compact-test premise is supplied by
`exists_chartAdjoint_compact_raw_bound` in `DerivativeKernels/Assembly/Compact`.
The bounded operator is supplied by `exists_modifiedAdjoint_L2_bound` in
`DerivativeKernels/LowBounds/Assembly`. The parent derivative-kernel assembly
must identify their compact-test representatives and instantiate this
implication; this module does not assert the unconditional adjoint estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential

variable {n : ℕ}

/-- Extend the compact smooth raw estimate in
`app:ch_background:prop:bg-adjoint` to every Euclidean measurement Hˢ datum
for the same bounded operator `U`. Output membership is proved, and the
constants `C` and `H`, the carrier measure, and the shared partial inverse
are preserved. The parent assembly supplies `htest` by identifying the
representatives from `exists_chartAdjoint_compact_raw_bound` and
`exists_modifiedAdjoint_L2_bound`. -/
theorem memPhysicalSobolev_partialUnitaryInverse_of_compactSmooth_bound
    (U : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n) (s : ℕ) (C H : ℝ)
    (htest : ∀ (v : Euclidean n → ℂ) (hv : ContDiff ℝ ∞ v)
      (hvs : HasCompactSupport v),
      let f : Lp (α := Euclidean n) ℂ 2 :=
        (hv.continuous.memLp_of_hasCompactSupport hvs).toLp v
      MemPhysicalSobolev s (partialUnitaryInverse n (U f)) ∧
        physicalSobolevNorm s (partialUnitaryInverse n (U f)) ≤
          C * (fourierSobolevNorm s f + H * ‖f‖))
    (f : Lp (α := Euclidean n) ℂ 2) (hf : MemFourierSobolev s f) :
    MemPhysicalSobolev s (partialUnitaryInverse n (U f)) ∧
      physicalSobolevNorm s (partialUnitaryInverse n (U f)) ≤
        C * (fourierSobolevNorm s f + H * ‖f‖) := by
  obtain ⟨g, hg, hc, hu, hlim, hL2⟩ :=
    exists_compactSmooth_fourierSobolev_nat_tendsto s f hf
  apply memPhysicalSobolev_and_norm_le_of_tendsto s
    ((partialUnitaryInverse n).continuous.continuousAt.tendsto.comp
      (U.continuous.continuousAt.tendsto.comp hL2))
    (fun k ↦ (htest (g k) (hg k) (hc k)).1)
    ((tendsto_fourierSobolevNorm_of_sub hu hf hlim).add
      (hL2.norm.const_mul H) |>.const_mul C)
  exact fun k ↦ (htest (g k) (hg k) (hc k)).2

end JanetCartan.ContinuumAdjoint.DerivativeKernels
