module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.SameSolver
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.PrimaryAmplitudeBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ReducedFourierClassical
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Displacement
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.SourceEnvelope

/-!
# The original primary response from the same reduced envelopes

Apply the full-source identity and the fixed smooth solver to the literal
primary atom. The resulting joint estimates are stated in the existing
displacement and physical-derivative amplitudes, with their original phase.
The source cutoff, observation core, scalar, carrier and solver are unchanged.

The initialized source constructor supplies the complete strain envelope and
its source profiles. The normalized inverse supplies the mixed reduced-solution
profiles of `fixedSolverParameterEnvelope`; `ReducedFourierClassical` converts
them with the fixed total reserve `m+n+3`. Their actual uniform instantiation
remains an obligation of the initializer, rather than an assumed estimate of
the desired ambient response.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CanonicalAtomRealization

open CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse ResponseTransfer
  ResponsePrimarySources
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (χ η : Euclidean n → ℝ) (hη : ContDiff ℝ ∞ η) (hχU : tsupport χ ⊆ U)
    {W core chart : Set (Euclidean n)}
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (τ : ℝ) (scalar : Euclidean (n-1) × Euclidean 3 → ℝ)
    (V : Set (Euclidean 3 × Euclidean (n-1)))
    (φ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)

set_option quotPrecheck false in
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F Q.1 η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ

set_option quotPrecheck false in
local notation "primaryTensor" =>
  (fun c : Euclidean 3 × Euclidean (n-1) ↦ complexAtomicSource F χ
    (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ scalar c.1 (x,c.2)))

variable
    (hre : ∀ c ∈ V, tensorFieldRealPart (complexAtomicSource F χ
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ scalar c.1 (x,c.2))) ∈
        compactSmoothSources (tsupport χ))
    (him : ∀ c ∈ V, tensorFieldImagPart (complexAtomicSource F χ
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ scalar c.1 (x,c.2))) ∈
        compactSmoothSources (tsupport χ))
    {sourceCore sourceChart : Set (Euclidean n)} (χenv : OutputCutoff sourceCore sourceChart)
    (hs : tsupport χ ⊆ sourceCore)

set_option quotPrecheck false in
local notation "primaryReduced" => fixedSolverParameterEnvelope Q.1 η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver V primaryTensor hre him τ φ

set_option quotPrecheck false in
local notation "primaryEnvelope" =>
  (fun p : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
    fullStrainEnvelope T Q F row col Φ Y scalar χenv τ p.2 p.1)

include hs hre him hsolver

/-- The existing primary amplitudes have the sharp joint profiles of the
same initialized inverse. Source identification and physical reconstruction
are proved for the actual atom, including both quadratures and all Frobenius
entries. These are exactly the norms consumed by finite preparation and the
original sampling event
(`app:ch_mean_pairs:eq:mean-prepared-scalar`,
`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem fullPrimaryResponse_fixedSolver_joint_graded
    (hφsource : ∀ c ∈ V, EqOn (fun x ↦ φ (x,c)) (fun x ↦ phase T Q x c.2) (tsupport χ))
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hΩ : IsOpen Ω) (hΩcore : Ω ⊆ core ×ˢ V)
    (hphase : ∀ p ∈ Ω, (p.1,p.2.2) ∈ phaseDomain T)
    (hφobs : ∀ p ∈ Ω, φ p = phase T Q p.1 p.2.2)
    (hφjoint : ContDiffOn ℝ ∞ φ Ω)
    (hφsp : ∀ c ∈ V, ContDiff ℝ ∞ (fun x ↦ φ (x,c)))
    (hg : ContDiffOn ℝ ∞ primaryReduced Ω)
    (ha : ∀ ij : Fin n × Fin n,
      ContDiffOn ℝ ∞ (fun q ↦ primaryEnvelope q ij.1 ij.2) Ω)
    (hχ : ContDiffOn ℝ ∞
      (fun q : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ (χ q.1 : ℂ)) Ω)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (fun q ↦
      ((partialDeriv (fun x ↦ φ (x,q.2)) q.1 i : ℝ) : ℂ)) Ω)
    (hV : ∀ l j, ContDiffOn ℝ ∞
      (fun q : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        reconstructionValueEntry F l j q.1) Ω)
    (hD : ∀ l ij, ContDiffOn ℝ ∞
      (fun q : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        reconstructionDerivativeEntry F l ij q.1) Ω)
    (hS : ∀ l ij, ContDiffOn ℝ ∞
      (fun q : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        reconstructionSourceEntry F l ij q.1) Ω)
    (C B : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {size K : ℝ} (hsize : 0 ≤ size) (hτ : 0 < τ) (hK : 1 ≤ K) (hKτ : K ≤ τ⁻¹)
    (reserve m : ℕ)
    (hχB : ∀ r ≤ m+1, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r
        (fun p : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ (χ p.1 : ℂ)) q‖ ≤
          C r * K^(r-reserve))
    (hφB : ∀ i r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦
        ((partialDeriv (fun x ↦ φ (x,p.2)) p.1 i : ℝ) : ℂ)) q‖ ≤ C r * K^(r-reserve))
    (hVB : ∀ l j r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r
        (fun p : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          reconstructionValueEntry F l j p.1) q‖ ≤ C r * K^(r-reserve))
    (hDB : ∀ l ij r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r
        (fun p : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          reconstructionDerivativeEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hSB : ∀ l ij r, r ≤ m+1 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r
        (fun p : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          reconstructionSourceEntry F l ij p.1) q‖ ≤ C r * K^(r-reserve))
    (hgB : ∀ j r, r ≤ m+2 → ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ primaryReduced p j) q‖ ≤
        B r * (τ^3*size) * K^(r-reserve))
    (haB : ∀ ij : Fin n × Fin n, ∀ r ≤ m+1, ∀ q ∈ Ω,
      ‖iteratedFDeriv ℝ r (fun p ↦ primaryEnvelope p ij.1 ij.2) q‖ ≤
        B r * (τ^3*size) * K^(r-reserve)) :
    ContDiffOn ℝ ∞ (fun p ↦ fullPrimaryResponse T Q F row col Φ Y χ Bfixed τ scalar p.2 p.1) Ω ∧
      ContDiffOn ℝ ∞ (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ Bfixed scalar τ) Ω ∧
      ∀ J : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1))), J ⊆ Ω →
        (∀ r ≤ m+1, cNorm J r
          (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ Bfixed scalar τ) ≤
            ((N : ℝ) * ∑ j ∈ Finset.range (r+1), jointReconstructionDisplacementBudget n C B j) *
              (τ^2*size) * K^(r-reserve)) ∧
        (∀ r ≤ m, ∀ p ∈ J, ‖iteratedFDeriv ℝ r
          (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ Bfixed scalar τ) p‖ ≤
            (N*n : ℕ) * jointReconstructionPhysicalBudget n C B r * (τ*size) * K^(r-reserve)) ∧
        (∀ r ≤ m, cNorm J r
          (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ Bfixed scalar τ) ≤
            ((N*n : ℕ) * ∑ j ∈ Finset.range (r+1), jointReconstructionPhysicalBudget n C B j) *
              (τ*size) * K^(r-reserve)) := by
  have hsource c (hc : c ∈ V) : primaryTensor c = fun x ↦
      waveCarrier τ⁻¹ (fun y ↦ φ (y,c)) x • ((χ x : ℂ) • primaryEnvelope (x,c)) := by
    have he := cutoff_fullPrimaryStrain_eq_modulatedSource_of_phase_eq T Q F row col Φ Y
      scalar χenv χ (fun x ↦ φ (x,c)) hs τ c (hφsource c hc)
    apply he.trans
    funext x
    simp only [SourceNegative.modulatedSource, carrier_eq_waveCarrier]
    rw [smul_comm]
    rfl
  obtain ⟨hresponse,hdisp,hderiv⟩ := fixedSolverParameterResponse_joint_graded Q.1 η hU
    (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver V primaryTensor hre him τ φ
    F hsolver Ξ χ primaryEnvelope hsource hΩ hΩcore hφjoint hφsp hg ha hχ hφ
    hV hD hS C B hC hB hsize hτ hK hKτ reserve m hχB hφB hVB hDB hSB hgB haB
  have hresponse' : ContDiffOn ℝ ∞
      (fun p ↦ fullPrimaryResponse T Q F row col Φ Y χ Bfixed τ scalar p.2 p.1) Ω := by
    simpa only [fullPrimaryResponse] using hresponse
  refine ⟨hresponse', ?_⟩
  exact fullPrimaryResponse_amplitudes_of_coordinate_profiles T Q F row col Φ Y
    χ Bfixed scalar τ φ hΩ hphase hφobs hresponse'
    (jointReconstructionDisplacementBudget n C B) (jointReconstructionPhysicalBudget n C B)
    (jointReconstructionDisplacementBudget_nonneg hC hB n)
    (jointReconstructionPhysicalBudget_nonneg hC hB n) hsize hτ hK reserve m
    (by simpa only [fullPrimaryResponse] using hdisp)
    (by simpa only [fullPrimaryResponse] using hderiv)

end JanetCartan.CanonicalAtomRealization
