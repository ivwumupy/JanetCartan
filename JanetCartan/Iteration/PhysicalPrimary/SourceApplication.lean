module

public import JanetCartan.Iteration.PhysicalPrimary.SourceEnvelope
public import JanetCartan.Iteration.PhysicalPrimary.SourceCoefficients
public import JanetCartan.Iteration.PhysicalPrimary.SourceJets
public import JanetCartan.Iteration.PhysicalPrimary.SourceFourier

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReservedSourceEnvelopes.TameJointProfiles

/-!
# The actual raw primary's cubic source on a physical history

Paper-v2 `app:ch_response:eq:response-graded-source`: instantiate the proved
homogeneous WKB full-strain formula on the SAME real Schwartz prefix. The
original scalar, full/carrier transports, frame, and source cutoff are unchanged.
The literal source envelope has its cubic `τ³` factor, and an arbitrary fixed
natural derivative reserve is preserved. All geometric inputs are produced
from actual revised physical admissibility; no current-frame or output-source
size estimate is assumed.

The scalar's primitive transport equation and correction tame estimate are
precisely outputs of the original generic leading callback retained by
`PhysicalSeed` and its fullCorrection construction. They remain explicit here
until that SAME callback is instantiated; no new row or flow is selected.
Consumer: the normalized same-source inverse and
`CanonicalAtomRealization.fullPrimaryResponse_fixedSolver_joint_graded`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary

open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open RawPrimary NullTransport HamiltonPhase ResponsePrimarySources CorrectedAtoms
open ResponseSourceExtension LeadingWave.FullModulation PrimarySourceAdmission
open ResponseTransfer Sampling.BackgroundModulation Pseudodifferential

/-- Construct the literal parameter-localized half-stress source and its
reserved Fourier profile on the SAME physical history, preserving the raw
`τ³` size, every supplied cutoff and the chosen natural reserve. Only the
original scalar/transport equations and their lower-level correction profile
are supplied by the same generic leading producer; no full-strain or response
profile is a premise (`main:prop:current-waves`). -/
theorem exists_history_reducedSource_reserved_fourier_profiles
    {n : ℕ} (hn : 5 ≤ n) (G : FlatReference n) {rGeom RGeom : ℝ}
    (hrGeom : 0 < rGeom) (hrR : rGeom < RGeom) (hRGeom : RGeom < G.domain.chartRadius)
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) rGeom) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < ambientStrainFrameThreshold hn / 2)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball (0 : Euclidean n) RGeom) isOpen_ball)
    (center : Euclidean n × (Euclidean 3 × Euclidean (n-1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hphysical : MapsTo Prod.fst (closedBall center ρ) (closedBall (0 : Euclidean n) rGeom))
    (z₀ : Euclidean 3) {Rscalar Mscalar mscalar : ℝ}
    (hRscalar : 0 < Rscalar) (hmscalar : 0 ≤ mscalar) (hgap : mscalar < Mscalar)
    (Γ Ar : ℕ → ℝ) (hΓ : ∀ k, 0 < Γ k) (hAr : ∀ k, 0 ≤ Ar k)
    {core chart : Set (Euclidean n)} (χenv : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set (Euclidean 3 × Euclidean (n-1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall center ρ)
    (hχphysical : tsupport χenv.toFun ⊆ closedBall (0 : Euclidean n) rGeom)
    (χsrc η : Euclidean n → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc) (hη : ContDiff ℝ ∞ η)
    (θ : (Euclidean 3 × Euclidean (n-1)) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ V)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar reserve kMin : ℕ}
    (hreserve : 16 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ)/2) + 2 < kMin) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Csource : ℕ → ℕ → ℝ, (∀ k s, 0 ≤ Csource k s) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ K : ℝ, currentCoefficientScale R₀ j ≤ K →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) RGeom) ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
        Q.1 = projectedStress F →
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
          Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))),
        IsOpen Ω → closedBall center ρ ⊆ Ω →
        MapsTo Prod.fst Ω (closedBall (0 : Euclidean n) rGeom) →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ Rscalar Mscalar mscalar,
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ Rscalar Mscalar mscalar, ∀ w ∈ Ω,
          conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
              nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ r ∈ primitiveInitialScalars (n := n) z₀ Rscalar Mscalar mscalar, ∀ k,
          cNorm (closedBall center ρ) k (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ k * (1 + cNorm (closedBall (0 : Euclidean n) rGeom) (k+14) F +
              cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (Rscalar/8)) (k+14) r)) →
        ∀ τ : ℝ, 0 < τ →
        ∀ scalar : initialScalarSpan (n := n) z₀ Rscalar Mscalar mscalar,
        ∀ size : ℝ, 0 ≤ size →
          (∀ k, cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (Rscalar/8))
            (k+16) (scalar : _ → ℝ) ≤ Ar k * size * K^(k-reserve)) →
        let astrain := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          fullStrainEnvelope T Q F row col Φ Y scalar χenv τ w.2 w.1
        let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          θ w.2 • (χsrc w.1 • (η w.1 • ((1/2 : ℝ) • complexStressContraction (Q.1 w.1) (astrain w))))
        ContDiff ℝ ∞ a ∧ (∀ w, w.1 ∉ tsupport χenv.toFun → a w = 0) ∧
          ∀ c k (v : Fin k → (Euclidean 3 × Euclidean (n-1))), (∀ j, ‖v j‖ ≤ 1) → ∀ s : ℕ,
            let f := fun x ↦ iteratedFDeriv ℝ k (fun b ↦ a (x,b)) c v
            ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
              vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
                Csource k s * (τ^3*size) * K^(s+k-reserve) := by
  obtain ⟨SA,hSA,Ca,hCa,hstrain⟩ := exists_history_fullStrain_reserved_profiles
    hn G hrGeom hrR hRGeom hreference T center hρ hphysical z₀ hRscalar hmscalar hgap
    Γ Ar hΓ hAr χenv hchart hV hproduct hBband hreserve horder
  obtain ⟨SQ,hSQ,AQ,hAQ,hstress⟩ := exists_history_rawStress_reserved_profiles
    G hrGeom hrR hRGeom hBband (by omega) (by omega : 2+reserve ≤ rStar) horder
  obtain ⟨Cb,hCb,hcontract⟩ := exists_reducedSource_reserved_joint_constants
    χenv.compact isOpen_ball (fun x hx ↦ closedBall_subset_ball hrR (hχphysical hx))
    hV χsrc η hχsrc hη θ hθ hcθ hsθ AQ Ca hAQ hCa
  obtain ⟨Csource,hCsource,hfourier⟩ := exists_reserved_source_fourier_constants
    (d := n-1) (r := n) χenv.compact Cb hCb
  refine ⟨max SA SQ,hSA.trans (le_max_left _ _),Csource,hCsource,?_⟩
  intro R₀ hR₀ j u ell hu K hK F Q hQ row col Φ Y Ω hΩ hball hΩK hphase
    hnonzero hα htransport hcorrection τ hτ scalar size hsize hscalar astrain a
  have hSAi : SA ≤ R₀ := (le_max_left _ _).trans hR₀
  have hSQi : SQ ≤ R₀ := (le_max_right _ _).trans hR₀
  obtain ⟨hstrainSmooth,hstrainJets⟩ := hstrain R₀ hSAi j u ell hu K hK Q hQ
    row col Φ Y Ω hΩ hball hΩK hphase hnonzero hα htransport hcorrection
    τ hτ scalar size hsize hscalar
  obtain ⟨hQsm,hQjet⟩ := hstress R₀ hSQi j u ell hu
  have hL : 1 ≤ currentCoefficientScale R₀ j :=
    one_le_currentCoefficientScale (by linarith [hSA.trans hSAi]) j
  have hK1 : 1 ≤ K := hL.trans hK
  have hQsm' : ContDiffOn ℝ ∞ Q.1 (ball (0 : Euclidean n) RGeom) := by
    simpa only [hQ] using hQsm
  have hQjet' : ∀ x ∈ tsupport χenv.toFun, ∀ k,
      ‖iteratedFDeriv ℝ k Q.1 x‖ ≤ AQ k*K^(k-reserve) := by
    intro x hx k
    rw [hQ]
    exact (hQjet x (hχphysical hx) k).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hL) hK _) (hAQ k))
  have hstrainZero : ∀ w, w.1 ∉ tsupport χenv.toFun → astrain w = 0 := by
    intro w hw
    simp only [astrain,fullStrainEnvelope_eq,image_eq_zero_of_notMem_tsupport hw,zero_smul]
  have hsize' : 0 ≤ τ^3*size := mul_nonneg (pow_nonneg hτ.le _) hsize
  obtain ⟨ha,has,hajet⟩ := hcontract Q.1 astrain (τ^3*size) K reserve hsize' hK1
    hQsm' hstrainSmooth hstrainZero hQjet' (fun w hw k ↦ hstrainJets k w hw)
  exact ⟨ha,has,hfourier a ha has (τ^3*size) K reserve hsize' hK1 hajet⟩

end JanetCartan.PhysicalPrimary
