module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates
public import JanetCartan.Analysis.Microlocal.SelectedSectorProtection.SelectedBuffers

/-!
# Original support times inside the retained flow interval

Consumer: `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`,
for `app:ch_regular:thm:no-return` and `app:ch_regular:lem:finite-chain`.
The physical supports and the original retarded elapsed interval are unchanged.
-/

@[expose] public noncomputable section
open Set Metric
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open FiniteMasks FiniteMasks.ActualFamily Characteristic Characteristic.AlgebraicChart
open JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The full common physical elapsed bound fits every selected flow time,
using the actual local producer's source/time comparison. This is the `Δ<T`
input of the protected-mask construction (`app:ch_regular:lem:finite-chain`). -/
theorem selected_common_elapsed_lt_evolutionTime
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hc : LocalProtectionCertificate (f.chart p) evolutionTime speedGap rootSize rootCost) :
    0 < 6 * f.physicalRadius ∧
      6 * f.physicalRadius < (f.chart p).sourceRadius ∧
      6 * f.physicalRadius < evolutionTime := by
  obtain ⟨hpos, _, hsource⟩ := selected_common_elapsed_lt_source_radii f p
  have htime := hc.2.2.2.2.2.1
  exact ⟨hpos, hsource, by linarith⟩

/-- Every segment between the original physical support times stays in the
same common time bound, hence in the selected ODE interval. This includes
both orientations and every intermediate elapsed time
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem selected_supported_segment_lt_evolutionTime
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hc : LocalProtectionCertificate (f.chart p) evolutionTime speedGap rootSize rootCost)
    {y z : Euclidean (d+1)}
    (hy : y ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    (hz : z ∈ tsupport f.inputMask ∪ tsupport f.outputMask)
    {u : ℝ} (hu : u ∈ uIcc (coordinateSplit (f.chart p).index z).1
      (coordinateSplit (f.chart p).index y).1) :
    |u - (coordinateSplit (f.chart p).index z).1| < 6 * f.physicalRadius ∧
      |u - (coordinateSplit (f.chart p).index z).1| < evolutionTime := by
  have ht := selected_physical_support_elapsed_bound f p hy hz
  have hle : |u - (coordinateSplit (f.chart p).index z).1| ≤
      |(coordinateSplit (f.chart p).index y).1 - (coordinateSplit (f.chart p).index z).1| := by
    rcases mem_uIcc.mp hu with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2))]
      linarith [h.2]
    · rw [abs_of_nonpos (sub_nonpos.mpr h.2), abs_of_nonpos (sub_nonpos.mpr (h.1.trans h.2))]
      linarith [h.1]
  exact ⟨hle.trans_lt ht, (hle.trans_lt ht).trans
    (selected_common_elapsed_lt_evolutionTime f p hc).2.2⟩

/-- The full original retarded interval also fits the retained ODE time;
no part of `3*maskRadius/4` is discarded (`retarded-kernel` in `paper-v2.tex`,
`app:ch_regular:lem:finite-chain` in `paper.tex`). -/
theorem selected_retarded_elapsed_lt_evolutionTime
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hc : LocalProtectionCertificate (f.chart p) evolutionTime speedGap rootSize rootCost) :
    3 * (f.chart p).maskRadius / 4 < evolutionTime := by
  have htime := hc.2.2.2.2.2.1
  have hmask := (f.chart p).maskRadius_lt_sourceRadius
  have hpos := (f.chart p).maskRadius_pos
  linarith

end JanetCartan.RegularSector.FiniteAssembly
