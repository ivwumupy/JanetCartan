module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.PhysicalKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.Prefixes
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.ColoredWeights

/-!
# Exact smooth-band reassembly of sampling normals

The literal `Sampling.refinedKernelPrefix` of
`app:ch_waves:eq:sampling-prefix-normal` reassembles to synthesis of the original
columns on `RawInputPartition.wideBand`, using the published Hilbert refinement
and unchanged prefixes. Its full two-position normal kernel has the original
wide-band frequency integral followed by physical Lebesgue integration. Both
quadratures, the half-scale first band, the original coefficients and factor four
are retained. No radial mask or high-pass transition is changed.

The consumer is the final assembly of `app:ch_waves:eq:colored-normal-comparison`.
It must still construct the actual raw-wave `BandKernelData` and identify these
kernels with the quotient homotopy. Reassembly does not assume either a normal
comparison or an analytic-output record, and is independent of disintegration.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling.ColoredNormalComparison
open RawInputRealization RawInputPartition SamplingKernelBounds

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n J : ℕ}

/-- Full two-position representation of every literal refined sampling prefix,
with both sharp pieces already reassembled before kernel calculus. The output
is the entire vector-valued Lebesgue space; the only finite sums are the
original bands and physical fiber coordinates
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem refinedKernelPrefix_normal_ae_wideKernel (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) (f : SamplingKernelBounds.Output n) :
    atomNormal (refinedKernelPrefix D L z) f =ᵐ[volume]
      fun x ↦ ∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
        WithLp.toLp 2 (fun i ↦ ∑ k : Fin n, ∫ y,
          (∫ η in wideBand n j.val,
            D.kernel (j, z) η x i * star (D.kernel (j, z) η y k)) * f y k) := by
  classical
  rw [refinedKernelPrefix_normal_eq_wide, sum_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h := ae_all_iff.mpr (fun j : Fin J ↦
    wideKernelOperator_normal_ae_integral D j.val (j, z) f)
  filter_upwards [h] with x hx
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ ↦ hx j)

end JanetCartan.Sampling.ColoredNormalComparison
