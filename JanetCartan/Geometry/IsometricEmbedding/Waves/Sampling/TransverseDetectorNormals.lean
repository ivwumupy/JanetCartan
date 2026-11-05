module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.TransverseDetectorCover

/-!
# Full-support refinement of the original transverse kernel normals

Construct the cover and carrier bumps from the primitive buffered incidence
domain, then apply exact weighted reassembly to the ORIGINAL transverse
detector and high-pass. The carrier support and every grouped prefix remain
unchanged. No normal identity or successful event is an input.

The local analytic constructors must supply the radii on the same retained
cells. Their primitive chart-domain inclusion and final finite-family event
application remain obligations of the sampling assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff Classical

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic SeparatedSampling SamplingKernelBounds
open RawPrimary.MaskProfiles

/-- Select one finite full-support refinement before the band ceiling and
raw kernels. For each original kernel with the literal detector/high-pass,
the constructed weighted local normals sum to its SAME grouped-prefix
normal, with both real quadratures and the factor four
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem exists_transverseDetector_normal_refinement
    {Param : Type*} [TopologicalSpace Param] [FirstCountableTopology Param]
    [LocallyCompactSpace Param]
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean (n - 1) → ℂ)
    (hchart : ∀ z ∈ Z, ∀ θ ∈ detectorDirectionSupport a,
      normalize (frozenInputCovector T z θ) ∈ O)
    (ha : ∀ t : ℝ, 0 < t → ∀ η, a (t • η) = a η)
    (r d : transverseDetectorIncidenceSupport T Z a → ℝ)
    (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (localWeight : transverseDetectorIncidenceSupport T Z a → Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → localWeight w z = 1) :
    ∃ labels : Finset (transverseDetectorIncidenceSupport T Z a),
    let ηb := fun i : labels ↦ T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2
    let r' := fun i : labels ↦ r i.1
    ∃ hηb : ∀ i, ηb i ≠ 0,
    ∃ b : labels → Point → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i)) ∧
      (∀ i z, b i z ∈ Icc (0 : ℝ) 1) ∧
      (∀ i z, b i z ≠ 0 → localWeight i.1 z = 1) ∧
    ∀ (H : Euclidean (n - 1) → ℝ) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
      (J : ℕ) (D : BandKernelData (Fin J × Param) n)
      (hmask : D.mask = detectorMask a H)
      (ψ : Point → ℝ) (_hψZ : ∀ z, ψ z ≠ 0 → WithLp.toLp 2 z ∈ Z),
    let D' := jointSubsetKernel ηb r' hηb (fun i ↦ hr i.1) D
      (mask_floor_of_eq_detectorMask a H hH₀ D hmask)
    ∀ (L : ℕ) (p : Param) (z : Point),
      (∑ s : Finset labels, ∑ i : s, carrierSubsetWeight ψ b s z •
        atomNormal (refinedKernelPrefix (D' s i) L p)) =
          ψ z • atomNormal (refinedKernelPrefix D L p) ∧
      (∑ s : Finset labels, ∑ i : s, carrierSubsetWeight ψ b s z •
        ((realQuadratureChannel (refinedKernelPrefix (D' s i) L p)) ∘L
          (realQuadratureChannel (refinedKernelPrefix (D' s i) L p)).adjoint)) =
        (4 : ℝ) • realOutputCompression (ψ z • atomNormal (refinedKernelPrefix D L p)) := by
  classical
  obtain ⟨labels, hηb, b, hbs, hb, hlocal, hcover⟩ :=
    exists_transverseDetector_carrier_cover T hP hZ hZP hroot a hchart ha
      r d hr hd localWeight hplateau
  refine ⟨labels, hηb, b, hbs, hb, hlocal, ?_⟩
  intro H hH₀ J D hmask ψ hψZ D' L p z
  have hfloor := mask_floor_of_eq_detectorMask a H hH₀ D hmask
  have hcover' : ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ i : labels,
      b i z = 1 ∧ normalize η ∈ ball
        (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
        (angularWidth (n := n)
          (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) := by
    intro hz η hη
    have hne : η ≠ 0 := by
      rintro rfl
      exact hη (hfloor 0 (by simp))
    have haη : a η ≠ 0 := by
      intro hzero
      apply hη
      simp only [hmask, detectorMask, hzero, zero_mul]
    exact hcover (WithLp.toLp 2 z) (hψZ z hz) η hne haη
  exact ⟨sum_carrierSubsetWeight_jointSubsetKernel_prefix_normal _ _ hηb
      (fun i ↦ hr i.1) D hfloor ψ b z hcover' L p,
    sum_carrierSubsetWeight_jointSubsetKernel_realPrefix_normal _ _ hηb
      (fun i ↦ hr i.1) D hfloor ψ b z hcover' L p⟩

end JanetCartan.Sampling
