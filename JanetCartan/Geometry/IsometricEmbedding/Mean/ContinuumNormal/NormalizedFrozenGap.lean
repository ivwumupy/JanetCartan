module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedFrozenGap.UniformFamily

/-!
# One frozen gap before the normalized source scale

Apply the supplied-family spectral and Fourier construction once to the seed
of `normalizedCarrierData`, then construct the nonconstant initial multipliers
on that SAME row. The resulting `InitializedFrozenSeedGap` keeps its unit
operators, measurement, inner cutoff, full density interval and exterior
square. In particular the reference map in this theorem is fixed BEFORE the
normalization scale; applying it separately to `sourceDilation F σ` would not
prove the required uniformity.

The primitive geometry and unit realization are the retained outputs of
`RetainedFrozen.Row`; the seed identity is produced by `SeedCovector` (and
`NormalizedFrozenGap.Normalization`). The compatible leading cells provide
the graph buffers, inverse-flow range and identities used by `RetainedLabels`.
The normalized selection owner retains these witnesses. The positive-scale
normal comparison remains with `ContinuumNormal` and its variation producer.
The concrete consumers are `ContinuumNormal.augmented_half_gap_of_channel_comparison`
and the uniform coercivity input of
`PositiveBackground.exists_small_uncorrectedDensity_of_normal_estimates`.
Sources: `app:ch_background:prop:bg-normalized`, `bg-frame`, `bg-Nsigma`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedFrozenGap
open RetainedFrozen FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement LeadingPrimitive
open ContinuumNormalReduction TransportSymbol ConicChart CarrierNormalRealization
open NullTransport FlowAmplitude ActualFlow ProjectedStressFrame
open RetainedFrozen.UnitRealization PeriodicLocalL2
open FrozenCoercivity FrozenImageComparison AmplitudeBound FrozenModel.InitialMultiplier

variable {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (centers : Finset (IncidenceCenter D))


variable (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ j, cNorm (closedBall (0 : Euclidean n) ((retainedIncidenceFamily T centers) j).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < ((retainedIncidenceFamily T centers) j).family.threshold)
    (F : Euclidean n → Euclidean (embeddingDimension n)) (row col : (RetainedIncidenceChannel D centers) → Fin n)
    (Φ Y : (RetainedIncidenceChannel D centers) → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (ηb : (RetainedIncidenceChannel D centers) → Euclidean (n - 1)) (r a r' a' : (RetainedIncidenceChannel D centers) → ℝ)
    (hηb : ∀ j, ηb j ≠ 0) (hr : ∀ j, 0 < r j) (ha : ∀ j, 0 < a j)
    (hr' : ∀ j, 0 < r' j) (ha' : ∀ j, 0 < a' j)
    (hrr : ∀ j, r' j ≤ r j) (haa : ∀ j, a' j ≤ a j)

include hD hr ha hrr haa

/-- Construct the full positive-density frozen gap from the supplied normalized
seed, without choosing another cover, flow, null column, mask or measurement.
The null relation is derived from the characteristic patch; the selected
column's nonvanishing is the retained leading-wave minor. Spectral positivity,
Fourier energy and both operator gaps are conclusions. The original scalar
`L/4` domain and full `L/8` density interval are unchanged. The existing
`InitializedFrozenSeedGap` places all gap and cutoff choices before the density,
so they also precede every scale-indexed density family
(`app:ch_background:prop:bg-normalized`, `bg-local-bound`, `bg-global-bound`). -/
theorem initializedFrozenSeedGap_of_retained_normalized_family
    (hn : 5 ≤ n)
    (εcover : centers → ℝ)
    (hcover : sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j))
    (hdomain : ∀ j : centers, ball j.1.1.2 (εcover j) ⊆ D.domain j.1.1.1)
    (hgram : ∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
      c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
        ∑ l, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 l).toFun
          (D.roots j.1.1.1 l q))) s ^ 2)
    (har' : ∀ i : (RetainedIncidenceChannel D centers), a' i ≤ r' i)
    (hQzero : Q 0 = cubeStress n)
    (hproject : Q 0 = projectedStress F 0)
    (hF : ContDiffAt ℝ 2 F 0)
    (himm : Function.Injective (fderiv ℝ F 0))
    (hrank : Set.range (normalMap F 0) =
      (normalSpace F 0 : Set (Euclidean (embeddingDimension n))))
    (hseed : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        ((retainedIncidenceFamily T centers) ⟨j, l⟩).carrierGradient ⟨Q, hQ, hlow ⟨j, l⟩⟩ 0 (D.roots j.1.1.1 l q) =
          (D.patches j.1.1.1 l).toFun (D.roots j.1.1.1 l q))
    (hplateau : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        angularMask ((retainedIncidenceCenters centers) ⟨j, l⟩) (NormedSpace.normalize (ηb ⟨j, l⟩))
          (ha' ⟨j, l⟩) (angularWidth_spec (hηb ⟨j, l⟩) (hr' ⟨j, l⟩)).1
          (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))
          (NormedSpace.normalize (((retainedIncidenceFamily T centers) ⟨j, l⟩).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1)
    (hcol : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        carrierNullvector ((retainedIncidenceFamily T centers) ⟨j, l⟩) ⟨Q, hQ, hlow ⟨j, l⟩⟩ (col ⟨j, l⟩)
          (0, D.roots j.1.1.1 l q) ≠ 0)
    (hgeometry : ∀ i, RetainedSpectralGeometry (retainedIncidenceFamily T centers i)
      ⟨Q, hQ, hlow i⟩ (retainedIncidenceCenters centers i) (ηb i) (r i) (a i))
    (hcell : ∀ i, 4 * a' i < 1 / 2)
    (hunit : ∀ i, UnitCarrierOutput (retainedIncidenceFamily T centers i)
      ⟨Q, hQ, hlow i⟩ F (row i) (col i) (Φ i) (Y i)
      (retainedIncidenceCenters centers i) (ηb i) (r i) (a i) (r' i) (a' i)
      (hr' i) (ha' i) (hcell i) (hηb i) (2 * (n + 1)) le_rfl)
    (zc : RetainedIncidenceChannel D centers → Euclidean 3)
    (L τ ρ : RetainedIncidenceChannel D centers → ℝ)
    (hL : ∀ i, 0 < L i) (hρ : ∀ i, 0 < ρ i)
    (E : RetainedIncidenceChannel D centers → Set (Euclidean n × CarrierParameter))
    (houter : ∀ i, coefficientDomain (retainedIncidenceCenters centers i) (r i) (6 * a i) ⊆ E i)
    (hgraph : ∀ i, MapsTo (carrierGraph (retainedIncidenceFamily T centers i)) (E i)
      (closedBall ((0 : Euclidean n), (zc i,
        (retainedIncidenceFamily T centers i).reference.spatialPatch (zc i))) (ρ i)))
    (hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zc i,
        (retainedIncidenceFamily T centers i).reference.spatialPatch (zc i))) (2 * ρ i) ⊆
      (coordinates (adaptedCoordinates (retainedIncidenceFamily T centers i).data.adapted)).symm ''
        (Icc (-τ i / 2) (τ i / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zc i,
            (retainedIncidenceFamily T centers i).reference.spatialPatch (zc i))) (L i / 64)))
    (Vcomp Dc : RetainedIncidenceChannel D centers →
      Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
    (hcoords : ∀ i, MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates (retainedIncidenceFamily T centers i).data.adapted)
        (p.1, parameter p.2)) (E i) (Vcomp i))
    (hcompat : ∀ i, Vcomp i ⊆ Dc i)
    (I : RetainedIncidenceChannel D centers → Set ℝ)
    (Dinitial : RetainedIncidenceChannel D centers → Set (Euclidean (n - 1) × Euclidean 3))
    (hrange : ∀ i, MapsTo (fun q ↦ (q.1, Y i q)) (Dc i) (I i ×ˢ Dinitial i))
    (hΦ0 : ∀ i p, p ∈ Dinitial i → Φ i (0, p) = p)
    (hΦY : ∀ i q, q ∈ Dc i → Φ i (q.1, Y i q) = q.2) :
    InitializedFrozenSeedGap (retainedIncidenceFamily T centers)
      (fun i ↦ ⟨Q, hQ, hlow i⟩) F row col Φ Y (retainedIncidenceCenters centers)
      ηb r' a' hr' ha' hcell hηb zc L := by
  classical
  have hnull (j : centers) (q : Euclidean n) (hq : q ∈ ball j.1.1.2 (εcover j))
      (l : Fin (D.patchCount j.1.1.1)) :
      pencil (projectedStress F 0)
        ((retainedIncidenceFamily T centers ⟨j, l⟩).carrierGradient
          ⟨Q, hQ, hlow ⟨j, l⟩⟩ 0 (D.roots j.1.1.1 l q)) *ᵥ
        (fun k ↦ carrierNullvector (retainedIncidenceFamily T centers ⟨j, l⟩)
          ⟨Q, hQ, hlow ⟨j, l⟩⟩ (col ⟨j, l⟩) (0, D.roots j.1.1.1 l q) k) = 0 := by
    rw [← hproject]
    exact seed_carrierNullvector_null_of_patch _ _ (hD.2.2.2.2.1 j.1.1.1 l).1
      hQzero (col ⟨j, l⟩)
      (fun m ↦ (((hD.2.2.2.2.1 j.1.1.1 l).2.2.1 q (hdomain j hq)).1 m).le)
      (hseed j q hq l)
  obtain ⟨γ, hγ, V, htest, hadj, hgaps⟩ :=
    exists_retained_frozen_row_gap hD T centers Q hQ hlow F row col Φ Y
      ηb r a r' a' hηb hr ha hr' ha' hrr haa hn εcover hcover hdomain hgram
      har' hQzero hproject hF himm hrank hseed hplateau hnull hcol hgeometry hcell hunit
  refine ⟨γ, hγ, V, htest, hadj, ?_⟩
  intro μ hμ hμcell hμa
  obtain ⟨rInner, hrInner, hInnerCell, hrμ, hlocal, hglobalPos, hglobal, hext⟩ :=
    hgaps μ hμ hμcell hμa
  rw [hproject] at hlocal hglobalPos hglobal
  refine ⟨rInner, hrInner, hInnerCell, hrμ, hlocal, hglobalPos, hglobal, hext, ?_⟩
  intro v hv hden
  have hreal i := RetainedLabels.exists_sqrt_initial_realization_of_retained_cell
    (retainedIncidenceFamily T centers i) (zc i) (retainedIncidenceCenters centers i)
    (hL i) (hρ i) (ha' i) ((har' i).trans (hrr i)) (haa i)
    (houter i) (hgraph i) (hworking i) (hcoords i) (hcompat i)
    (Φ i) (Y i) (hrange i) (hΦ0 i) (hΦY i) (v i) (hv i) (hden i)
    ⟨Q, hQ, hlow i⟩ F (row i) (col i) (ha' i) (hcell i)
    (NormedSpace.normalize (ηb i)) (angularWidth_spec (hηb i) (hr' i)).1
    FixedCutoffs.highFrequency (V i) (htest i) (fun w ↦ (hadj i w).2)
  choose β hβ hβBound _hcompact _hnonneg heq hlabel hM hself _hnorm htestβ _hsupp
    _huniq hadjβ hcomparison hnormal hrealNormal using hreal
  have hchannels i (w : OutputL2 n) :
      (1 / 16 : ℝ) * ‖(realQuadratureChannel
        (restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (V i))).adjoint w‖ ^ 2 ≤
      ‖(realQuadratureChannel (restrictCarrier (FixedCutoffs.periodic hμ hμcell 1)
        (V i ∘L labelMultiplier (β i) (hβ i).continuous (hβBound i)))).adjoint w‖ ^ 2 := by
    change (1 / 16 : ℝ) * ‖(carrierChannel _).adjoint w‖ ^ 2 ≤
      ‖(carrierChannel _).adjoint w‖ ^ 2
    simp only [carrierChannel_restrictCarrier, ContinuousLinearMap.adjoint_comp,
      cutoffMultiplier_adjoint, ContinuousLinearMap.comp_apply]
    exact hcomparison i (cutoffMultiplier (FixedCutoffs.periodic hμ hμcell 1) w)
  exact ⟨β, hβ, hβBound,
    fun i ↦ ⟨heq i, hlabel i, hM i, hself i, htestβ i, hadjβ i, hnormal i, hrealNormal i⟩,
    (supported_physicalRow_gap_of_initial_comparison _ _ _ hchannels
      (half_pos hγ) hlocal).2,
    (augmentedNormal_gap_of_initial_comparison _ _ _ hchannels
      (innerCutoff hrInner hInnerCell) hglobalPos hglobal).2⟩

end JanetCartan.ContinuumNormal.NormalizedFrozenGap
