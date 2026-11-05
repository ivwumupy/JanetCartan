module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.IntegratedComparison

/-!
# Transfer to the kernel witness returned by the retained constructor

Only the phase, mask and amplitude formulas matter for the literal sampling
prefix. This connects the kernel returned by
`exists_full_retained_measuredKernel_mean` to the same concrete kernel in
`exists_retained_integrated_prefix_transport_bound`, without identifying its
independently chosen scalar bound witnesses
(`app:ch_waves:eq:colored-normal-comparison`).
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open SamplingKernelBounds

/-- Primitive phase, mask and amplitude equalities identify every literal
grouped prefix on full output. These are the exported fields of the retained
constructor; an operator or normal identity is not an input
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem refinedKernelPrefix_eq_of_fields
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    {n J : ℕ} (D D' : BandKernelData (Fin J × P) n)
    (hp : D.phase = D'.phase) (hm : D.mask = D'.mask) (ha : D.amplitude = D'.amplitude)
    (L : ℕ) (z : P) : refinedKernelPrefix D L z = refinedKernelPrefix D' L z := by
  have hk (q : Fin J × P) (η : Euclidean (n - 1)) (x : Euclidean n) :
      D.kernel q η x = D'.kernel q η x := by
    simp only [BandKernelData.kernel, bandKernel, hp, hm, ha]
  have hc (q : Fin J × P) (η : Euclidean (n - 1)) : D.column q η = D'.column q η := by
    apply Lp.ext
    filter_upwards [D.column_coe q η, D'.column_coe q η] with x hx hx'
    exact hx.trans ((hk q η x).trans hx'.symm)
  ext1 f
  simp only [refinedKernelPrefix_apply, hc]

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
