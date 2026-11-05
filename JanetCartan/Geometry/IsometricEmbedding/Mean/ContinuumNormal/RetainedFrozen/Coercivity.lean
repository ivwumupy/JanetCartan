module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Energy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenCoercivity

/-!
# Frozen coercivity on the supplied retained family

The common initialized construction consumes this specialized assembly. Its
joint local outputs supply the original outer inverse and literal unit carrier;
the seed and retained leading cell supply exact patch covectors and null columns.
We apply the actual spectral and Fourier producers, including the periodic
image comparison, before choosing the inner support. No spectral or operator
coercivity is an input. The parent still instantiates the seed/leading evidence
and compares with the positive-scale current normal.
Sources: `app:ch_background:prop:bg-frame`, `bg-local-bound`, `bg-global-bound`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement
open ContinuumNormalReduction TransportSymbol ConicChart CarrierNormalRealization
open NullTransport ProjectedStressFrame UnitRealization PeriodicLocalL2
open FrozenCoercivity FrozenImageComparison AmplitudeBound

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

/-- Apply the spectral, literal carrier-energy, image-comparison and exterior
completion producers on the SAME supplied masks (`app:ch_background:prop:bg-frame`).
The explicit geometric/seed/null inputs are outputs of the retained initializer. -/
theorem exists_retained_frozen_row_gap
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
    (hnull : ∀ (j : centers) (q : Euclidean n), q ∈ ball j.1.1.2 (εcover j) →
      ∀ l : Fin (D.patchCount j.1.1.1),
        pencil (projectedStress F 0)
          (((retainedIncidenceFamily T centers) ⟨j, l⟩).carrierGradient ⟨Q, hQ, hlow ⟨j, l⟩⟩ 0 (D.roots j.1.1.1 l q)) *ᵥ
          (fun k ↦ carrierNullvector ((retainedIncidenceFamily T centers) ⟨j, l⟩) ⟨Q, hQ, hlow ⟨j, l⟩⟩ (col ⟨j, l⟩)
            (0, D.roots j.1.1.1 l q) k) = 0)
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
      (hr' i) (ha' i) (hcell i) (hηb i) (2 * (n + 1)) le_rfl) :
    let e := fun i ↦ normalizedCarrierData (retainedIncidenceFamily T centers i)
      ⟨Q, hQ, hlow i⟩ F (row i) (col i) (Φ i) (Y i) (fun _ ↦ 1)
      (ha' i) (hcell i)
      (angularMask (retainedIncidenceCenters centers i) (NormedSpace.normalize (ηb i))
        (ha' i) (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0
    ∃ γ > (0 : ℝ), ∃ V : RetainedIncidenceChannel D centers → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i v, V i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (e i) v.val) ∧
      (∀ i (w : ComplexOutputL2 n), MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
        (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
      ∀ (μ : ℝ) (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2), (∀ i, 6 * μ < a' i) →
        let W := fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (V i)
        let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays (Q 0))
        ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2), rInner ≤ μ ∧
          (∀ w : OutputL2 n,
            (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w z = 0) →
            γ / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image W).adjoint w‖ ^ 2) ∧
          0 < NormalAugmentation.globalGap (γ / 2) ‖physicalRow image W‖ ∧
          (∀ w : OutputL2 n,
            NormalAugmentation.globalGap (γ / 2) ‖physicalRow image W‖ * ‖w‖ ^ 2 ≤
              inner ℝ (augmentedNormal image W (innerCutoff hrInner hInnerCell) w) w) ∧
          (∀ w : OutputL2 n, ∀ᵐ z ∂volume,
            centeredTorusRepresentative z ∈ closedBall 0 (rInner / 2) →
              exteriorChannel (innerCutoff hrInner hInnerCell) w z = 0) := by
  classical
  have hgeometryCopy := hgeometry
  have hunitCopy := hunit
  choose har hcarrier G b cJ Vgeom L hcJ hVgeom hLV hf hInv htrans hgap using hgeometryCopy
  obtain ⟨hecont, ⟨B, _hB, hbound⟩, hnonneg, γ, hγ, hspectral⟩ :=
    retained_incidence_spectral_bounds hD T centers G Q hQ hlow F row col Φ Y
      ηb r a r' a' hηb hr ha hr' ha' hrr haa har hcarrier hf hInv htrans hcJ hVgeom hLV
      hn εcover hcover hdomain hgram har' hQzero hproject hF himm hrank hgap
      hseed hplateau hnull hcol
  choose hn' hsupport Bamp hBamp hb hA V htest hsupp huniq hadj hnormal hsep using hunitCopy
  refine ⟨γ, hγ, V, htest, hadj, ?_⟩
  intro μ hμ hμcell hμa
  let W := fun i ↦ restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (V i)
  let carrier := fun i ↦ retainedFrozenCarrierSymbol (retainedIncidenceFamily T centers i)
    ⟨Q, hQ, hlow i⟩ F (row i) (col i) (Φ i) (Y i) (fun _ ↦ 1)
    (retainedIncidenceCenters centers i) (r i) (a i) (hηb i) (hr' i) (ha' i)
  have hP (i : RetainedIncidenceChannel D centers) := (hD.2.2.2.2.1 i.1.1.1.1 i.2).1
  have hcont i : Continuous (carrier i) :=
    retainedFrozenCarrierSymbol_unit_continuous _ _ _ _ _ _ _ (hP i) (hηb i)
      (hr i) (ha i) (hr' i) (ha' i) (hrr i) (haa i) (har i) (hcarrier i)
      (hf i) (hInv i) (htrans i) (hcJ i) (hVgeom i) (hLV i)
  choose M hM hMb using fun i ↦ retainedFrozenCarrierSymbol_unit_bounded
    (retainedIncidenceFamily T centers i) ⟨Q, hQ, hlow i⟩ F (row i) (col i) (Φ i) (Y i)
    (hP i) (hηb i) (hr i) (hr' i) (ha' i) (haa i) (har i) (hcarrier i)
    (hf i) (hInv i) (htrans i) (hcJ i)
  have henergy i w : ‖(realQuadratureChannel (W i)).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy (carrier i) (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x)) :=
    unitCarrierOutput_commonMeasurement_energy _ _ _ _ _ _ _ (hP i) (hηb i)
      (hr i) (ha i) (hr' i) (ha' i) (hcell i) (hrr i) (haa i) (hgeometry i)
      le_rfl (hunit i) (V i) (htest i) hμ hμcell (hμa i) w
  apply exists_frozen_row_gap_of_spectral_energy (by omega : 0 < n)
    (Q 0) _ hecont hγ hbound hnonneg hspectral hμ hμcell W
  intro w
  obtain ⟨hf₁, hf₂, _⟩ := frozen_measured_zero_extension_integrable_memLp_support hμ w
  have he := euclideanFrozenEnergy_image_add_sum (Q 0) carrier hcont M hMb _ hf₁ hf₂
  simp_rw [← henergy] at he
  exact he

end JanetCartan.ContinuumNormal.RetainedFrozen
