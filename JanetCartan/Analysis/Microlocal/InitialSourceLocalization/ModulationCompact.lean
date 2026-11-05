module
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FrozenCovectorShift

/-!
# One original full-source compact for all small modulations

The covector shift in the original Fourier synthesis is `τ • η`.
The fixed carrier cube and a closed shift ball produce a compact before
frequencies and samples. The source graph is then contained in the SAME
frequency compact for every admitted current phase.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.InitialSourceLocalization
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ProtectedFlow

/-- Construct the parameter compact needed by the original full reduced
source from the literal carrier cube and its independent modulation shifts.
The radius, current-frame margin and symmetric frequency compact precede
`τ`, the input Fourier radius, the sample and the current coefficients.
Consumer: the first-mask application of the retained reduced source
(`app:ch_regular:eq:source-tail`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_retained_modulatedSource_frequency_compact
    {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {S : Set (Euclidean (d+1))} (hS : IsCompact S)
    (hSball : S ⊆ ball (0 : Euclidean (d+1)) T.physicalRadius)
    {Ω : Set (Euclidean (d+1))} (hΩsym : ∀ ξ ∈ Ω, -ξ ∈ Ω)
    (hangular : ∀ z ∈ parameterCube P.radius,
      normalizedCovector (P.toFun z) ∈ interior Ω) :
    ∃ ε > (0 : ℝ),
    ∃ Cpar : Set (Euclidean 3 × Euclidean (d+1-1)), IsCompact Cpar ∧
      S ×ˢ Cpar ⊆ LeadingWave.FullModulation.domain T ∧
      (∀ w ∈ S ×ˢ Cpar,
        normalizedCovector (T.reference.chart.chartMomentum (w.1,(0,w.2.2))) ∈ interior Ω) ∧
      (∀ (τ K : ℝ), |τ| * K ≤ ε → ∀ z ∈ parameterCube P.radius,
        ∀ η ∈ closedBall (0 : Euclidean (d+1-1)) K,
          (z,T.reference.spatialPatch z + τ • η) ∈ Cpar) ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ Ksource : Set (Euclidean (d+1)), IsCompact Ksource ∧
      (∀ ξ ∈ Ksource, -ξ ∈ Ksource) ∧
      (∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω) ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean (d+1)) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ x ∈ S, ∀ c ∈ Cpar,
        (x, gradient (fun y ↦ LeadingWave.FullModulation.phase T Q y c.2) x) ∈
          S ×ˢ Ksource := by
  obtain ⟨ε,hε,hcompact⟩ := exists_retained_fullPhase_source_compact_for_covector_shifts
    T hP hS hSball hΩsym hangular
  let Kpar := parameterCube P.radius ×ˢ closedBall (0 : Euclidean (d+1-1)) ε
  let shift := fun w : Euclidean 3 × Euclidean (d+1-1) ↦
    (w.1,T.reference.spatialPatch w.1+w.2)
  let Cpar := shift '' Kpar
  have hpatch : ContinuousOn T.reference.spatialPatch (parameterCube P.radius) :=
    (T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1)
  have hshift : ContinuousOn shift Kpar :=
    continuousOn_fst.prodMk ((hpatch.comp continuousOn_fst (fun _ hw ↦ hw.1)).add
      continuousOn_snd)
  have hCpar : IsCompact Cpar :=
    ((isCompact_parameterCube _).prod (isCompact_closedBall _ _)).image_of_continuousOn hshift
  have hpar : ∀ c ∈ Cpar, c.1 ∈ parameterCube P.radius ∧
      ‖c.2 - T.reference.spatialPatch c.1‖ ≤ ε := by
    rintro _ ⟨⟨z,v⟩,⟨hz,hv⟩,rfl⟩
    refine ⟨hz,?_⟩
    simpa only [shift,add_sub_cancel_left,mem_closedBall,dist_zero_right] using hv
  obtain ⟨hsource,hfrozen,hgraph⟩ := hcompact Cpar hCpar hpar
  refine ⟨ε,hε,Cpar,hCpar,hsource,hfrozen,?_,hgraph⟩
  intro τ K hsmall z hz η hη
  refine ⟨(z,τ • η),⟨hz,?_⟩,rfl⟩
  rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hη) (abs_nonneg τ)).trans hsmall

end JanetCartan.InitialSourceLocalization
