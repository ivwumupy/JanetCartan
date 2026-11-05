module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.PointwiseRealization

/-!
# Uniform estimates independent of auxiliary bound choices

The corrected canonical kernel is already fixed before its quantitative estimates
are applied. Its compactness proof chooses an auxiliary amplitude bound; that
choice need not equal the uniform bound supplied by the retained profiles.
Use the latter directly on the SAME columns and grouped rows. In the concentration
application only the evidence in `BandKernelData` is replaced, so every operator,
prefix, sample and deterministic background realization remains literal.

Consumer: the corrected whole-source family in
`app:ch_waves:eq:sampling-all-prefixes`. The sharp band and mean estimates still
belong to their analytic producers; this file makes no claim to construct them.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace JanetCartan.Sampling
open SamplingKernelBounds SeparatedSampling Realization RawInputPartition RawInputRealization
open LatticeQuadrature BackgroundQuadrature AsymptoticRealization

/-- A uniform coefficient estimate controls the original squared-kernel
integral, irrespective of the auxiliary bound chosen when forming its data.
The physical support, detector and annular measure stay explicit
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem integral_norm_column_sq_le_of_uniform_bounds
    {P : Type*} [TopologicalSpace P] {n : ℕ}
    (D : BandKernelData P n) (hn : 1 ≤ n)
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {R M Md : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    (hs : ∀ p η x, x ∉ S → D.amplitude ((p, η), x) = 0)
    (ha : ∀ p η x, ‖D.amplitude ((p, η), x)‖ ≤ M)
    (hm : ∀ η, ‖D.mask η‖ ≤ Md) (p : P) :
    (∫ η, ‖D.column p η‖ ^ 2 ∂annularMeasure n R) ≤
      (volume.real S * Md ^ 2 * M ^ 2 * unitBallVolume n) * R ^ n := by
  simp_rw [D.norm_column_sq]
  exact double_integral_norm_bandKernel_sq_le hn _ _ _ hS hR hM hMd hm (ha p) (hs p)

/-- The SAME grouped prefix has its uniform trace bound from coefficient
estimates. No comparison with an arbitrary chosen `amplitudeBound` is used
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem hilbertSchmidtSq_refinedKernelPrefix_le_of_uniform_bounds
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P] {n J : ℕ}
    (D : BandKernelData (Fin J × P) n) (hn : 1 ≤ n)
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {M Md : ℝ} (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    (hs : ∀ p η x, x ∉ S → D.amplitude ((p, η), x) = 0)
    (ha : ∀ p η x, ‖D.amplitude ((p, η), x)‖ ≤ M)
    (hm : ∀ η, ‖D.mask η‖ ≤ Md)
    {δ : Type*} (b : HilbertBasis δ ℂ (RefinedInput n J)) (L : ℕ) (p : P) :
    hilbertSchmidtSq b (refinedKernelPrefix D L p) ≤
      ((volume.real S * Md ^ 2 * M ^ 2 * unitBallVolume n) *
        (1 + (2 : ℝ) ^ n)) * ((2 : ℝ) ^ J) ^ n := by
  let E : BandKernelData (Fin J × P) n :=
    { D with
      physicalSupport := S
      physicalSupport_compact := hS
      amplitude_eq_zero := hs
      amplitudeBound := M
      amplitudeBound_nonneg := hM
      amplitude_le := ha
      maskBound := Md
      maskBound_nonneg := hMd
      mask_le := hm }
  exact hilbertSchmidtSq_refinedKernelPrefix_le E b hn L p

/-- Choose one threshold from uniform coefficient bounds, then apply the
existing all-prefix event to the literal kernels selected at that frequency.
Updating the support/bound evidence leaves the operators definitionally equal;
the resulting event and every background estimate use the ORIGINAL data and
one shared realization (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem exists_uniform_refinedKernelPrefix_threshold_of_amplitude
    {A : Type*} [Fintype A] {n p : ℕ} (hn : 1 ≤ n)
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    {ψ : A → Point → ℝ} {B C_op C_mean ε : ℝ} {P M Md : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hε : 0 < ε) (hM : ∀ a, 0 ≤ M a) (hMd : ∀ a, 0 ≤ Md a)
    (hC_op : 0 ≤ C_op) (S : A → Set (Euclidean n)) (hS : ∀ a, IsCompact (S a))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ ≥ Λ₀,
      ∀ D : A → BandKernelData
        (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n,
      (∀ a q η x, x ∉ S a → (D a).amplitude ((q, η), x) = 0) →
      (∀ a q η x, ‖(D a).amplitude ((q, η), x)‖ ≤ M a) →
      (∀ a η, ‖(D a).mask η‖ ≤ Md a) →
      (∀ a (i : RefinedIndex (cutoffCount Λ)) c z,
        ψ a z ≠ 0 → ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤
          C_op * refinedRadius i) →
      ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) (samplingMesh ε Λ)
        (fun c z ↦ refinedKernelPrefix (D a) (cutoffCount Λ) (c, z))‖ ≤ C_mean →
      ∃ ξ : A → ShiftSpace p B (samplingMesh ε Λ),
        (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧
          extendedShift (ξ a) q i < samplingMesh ε Λ) ∧
        (∀ L ≤ cutoffCount Λ,
          ‖familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤
              samplingTolerance ε Λ) ∧
        (∀ a, SampleGeometry p B (P a) 1 (ψ a) (convolvedBoxWindow κ p)
          (samplingMesh ε Λ) (extendedShift (ξ a))) ∧
        (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Q_bg : A → ℝ),
          (∀ a c, ContDiff ℝ p (fun z ↦ ψ a z • G a c z)) →
          (∀ a, 0 ≤ Q_bg a) →
          (∀ a c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a c z) z‖ ≤ Q_bg a) →
          ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a ↦ extendedShift (ξ a)) G‖ ≤
              backgroundQuadratureConstant p B * (∑ a, Q_bg a) * samplingMesh ε Λ ^ p) := by
  let Q a := volume.real (S a) * Md a ^ 2 * M a ^ 2 * unitBallVolume n
  have hQ (a) : 0 ≤ Q a := by dsimp [Q, unitBallVolume]; positivity
  obtain ⟨Λ₀, hΛ₀, hsample⟩ := exists_uniform_refinedKernelPrefix_threshold_of_support
    (C_mean := C_mean) (V := V) hn hc hs hm hkpos hk hp hψ hψc hε hQ hC_op
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ D hsupport hamplitude hmask hband hmean ↦ ?_⟩
  let E a : BandKernelData
      (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n :=
    { D a with
      physicalSupport := S a
      physicalSupport_compact := hS a
      amplitude_eq_zero := hsupport a
      amplitudeBound := M a
      amplitudeBound_nonneg := hM a
      amplitude_le := hamplitude a
      maskBound := Md a
      maskBound_nonneg := hMd a
      mask_le := hmask a }
  exact hsample Λ hΛ E (fun _ ↦ le_rfl) hband hmean

end JanetCartan.Sampling
