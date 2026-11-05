module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrection
public import JanetCartan.Iteration.PhysicalPrimary.SourceApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.LeadingSourceTemplate

/-!
# The full reduced source of the retained physical cell

Close the primitive scalar, transport, correction, and moving-domain inputs of
`exists_history_reducedSource_reserved_fourier_profiles` using the SAME retained
leading tuple. The fixed correction profile and the Fourier profile precede
every physical history. The source is literally the original cutoff times the
half-stress of its full raw strain, not a replacement datum or principal-only
wave (`app:ch_response:eq:response-graded-source`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open RawPrimary NullTransport HamiltonPhase ResponsePrimarySources CorrectedAtoms
open ResponseSourceExtension LeadingWave.FullModulation PrimarySourceAdmission
open ResponseTransfer Sampling.BackgroundModulation Pseudodifferential FlowAmplitude ActualFlow

/-- The literal output of
`exists_history_leading_reducedSource_reserved_fourier_profiles`, only named to
elaborate its typed function argument before inserting the cached leading tuple.
No source or estimate is assumed; unfolding gives exactly the all-order physical
Fourier conclusion (`app:ch_response:eq:response-graded-source`). -/
def LeadingReducedSourceFourierBounds {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n))
    (χ : Euclidean n → ℝ) (C : ℕ → ℕ → ℝ) (size K : ℝ) (reserve : ℕ) : Prop :=
  ContDiff ℝ ∞ a ∧ (∀ w, w.1 ∉ tsupport χ → a w = 0) ∧
    ∀ (z : Euclidean 3 × Euclidean (n-1)) (k : ℕ)
      (v : Fin k → (Euclidean 3 × Euclidean (n-1))), (∀ j, ‖v j‖ ≤ 1) → ∀ s : ℕ,
      let f : Euclidean n → EuclideanSpace ℂ (Fin n) :=
        fun y ↦ iteratedFDeriv ℝ k (fun q ↦ a (y,q)) z v
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (MemLp.toLp f hm) ∧
        vectorFourierSobolevNorm (s : ℝ) (MemLp.toLp f hm) ≤ C k s*size*K^(s+k-reserve)


/-- The actual original full-strain half-stress source has all reserved
parameter-jet Fourier norms. All primitive scalar, source-transport and
correction-profile obligations are discharged from the SAME retained leading
data. The only varying norm input is the prescribed original initial scalar's
reserved profile, not a source or inverse-response bound
(`main:prop:current-waves`, `app:ch_response:eq:response-graded-source`). -/
theorem exists_history_leading_reducedSource_reserved_fourier_profiles
    {n : ℕ} (hn : 5 ≤ n) (G : FlatReference n)
    {rGeom RGeom : ℝ} (hrGeom : 0 < rGeom) (hrR : rGeom < RGeom)
    (hRGeom : RGeom < G.domain.chartRadius)
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) rGeom) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < ambientStrainFrameThreshold hn / 2)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 RGeom) isOpen_ball)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ closedBall 0 rGeom)
    (centers : Finset (parameterCube P.radius)) (row col : centers → Fin n)
    (ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ)
    (Ωc : centers → Set (Euclidean n × Euclidean 3)) (ρc Bc gc Bfull : centers → ℝ)
    (Mscalar m c : ℝ) (hm : 0 ≤ m) (hgap : m < Mscalar) (hc : 0 < c)
    (E : ℕ → ℝ) (A H B : centers → ℕ → ℝ)
    (cell : centers) (hρ : 0 < ρ cell) (hR : 0 < R cell) (hτ : 0 < τ cell) (hσ : 0 < σ cell)
    (hworking : let a := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
      closedBall a (2*σ cell) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ cell/2) (τ cell/2) ×ˢ
            closedBall ((0 : Euclidean (n-1)),(cell.1.1,T.reference.spatialPatch cell.1.1)) (R cell/64)))
    (hcoeff : let a := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
      closedBall a (2*σ cell) ⊆ closedBall a (ρ cell))
    (Ar : ℕ → ℝ) (hAr : ∀ k, 0 ≤ Ar k)
    {core chart : Set (Euclidean n)} (χenv : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set (Euclidean 3 × Euclidean (n-1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆
      closedBall ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1)) (2*σ cell))
    (hχphysical : tsupport χenv.toFun ⊆ closedBall (0 : Euclidean n) rGeom)
    (χsrc η : Euclidean n → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc) (hη : ContDiff ℝ ∞ η)
    (θ : (Euclidean 3 × Euclidean (n-1)) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcθ : HasCompactSupport θ) (hsθ : tsupport θ ⊆ V)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar reserve kMin : ℕ}
    (hreserve : 16+reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Csource : ℕ → ℕ → ℝ, (∀ k s, 0 ≤ Csource k s) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      ∀ K : ℝ, currentCoefficientScale R₀ stage ≤ K →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ (hF : ContDiffOn ℝ ∞ F (ball 0 RGeom))
        (hi : IsImmersionOn F (ball 0 RGeom)) (hrank : HasFullNormalRankOn F (ball 0 RGeom))
        (hdata : RetainedLeadingData T (K := closedBall (0 : Euclidean n) rGeom)
          centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank),
      let Q := LeadingData.Q (K := closedBall (0 : Euclidean n) rGeom) T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata
      let Φ := LeadingCell.Φ (K := closedBall (0 : Euclidean n) rGeom) T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let Y := LeadingCell.Y (K := closedBall (0 : Euclidean n) rGeom) T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      ∀ τsource : ℝ, 0 < τsource →
      ∀ scalar : initialScalarSpan (n := n) cell.1.1 (R cell) Mscalar m,
      ∀ size : ℝ, 0 ≤ size →
        (∀ k, cNorm (closedBall ((0 : Euclidean (n-1)),cell.1.1) (R cell/8))
          (k+16) scalar.val ≤ Ar k*size*K^(k-reserve)) →
      let astrain : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → Matrix (Fin n) (Fin n) ℂ :=
        fun w ↦ fullStrainEnvelope T Q F (row cell) (col cell) Φ Y scalar.val χenv τsource w.2 w.1
      let a : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → EuclideanSpace ℂ (Fin n) :=
        fun w ↦ θ w.2 • (χsrc w.1 • (η w.1 • ((1/2 : ℝ) •
          complexStressContraction (Q.1 w.1) (astrain w))))
      LeadingReducedSourceFourierBounds a χenv.toFun Csource (τsource^3*size) K reserve := by
  classical
  let center := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
  obtain ⟨SΓ,hSΓ,Γ,hΓ,hcorrection⟩ := exists_history_leading_correction_profiles
    G hrGeom hrR hRGeom T hball centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c hc E A H B cell hρ hR hτ hσ hworking hcoeff
    hBband (by omega) horder
  by_cases hphysical : MapsTo Prod.fst (closedBall center (2*σ cell)) (closedBall 0 rGeom)
  · obtain ⟨SS,hSS,Csource,hCsource,hsource⟩ := exists_history_reducedSource_reserved_fourier_profiles
      hn G hrGeom hrR hRGeom hreference T center (by positivity : 0 < 2*σ cell) hphysical
      cell.1.1 hR hm hgap Γ Ar hΓ hAr χenv hchart hV hproduct hχphysical
      χsrc η hχsrc hη θ hθ hcθ hsθ hBband hreserve horder
    refine ⟨max SΓ SS,hSΓ.trans (le_max_left _ _),Csource,hCsource,?_⟩
    intro R₀ hR₀ stage u ell hu K hK F hF hi hrank hdata Q Φ Y
    let C := LeadingCell.C T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
      Mscalar m c E A H B F hF hi hrank hdata cell
    let D := LeadingCell.D T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
      Mscalar m c E A H B F hF hi hrank hdata cell
    let W := LeadingCell.W T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
      Mscalar m c E A H B F hF hi hrank hdata cell
    have hdom := LeadingCell.fact0 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    have hphysK := LeadingCell.fact1 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    have hD := LeadingCell.fact15 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    have hcover := LeadingCell.fact16 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    have hphys := LeadingCell.fact18 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
    have hWΩ : W ⊆ C ⁻¹' D := by
      rintro w ⟨q,hq,rfl⟩
      change C (C.symm q) ∈ D
      rw [C.apply_symm_apply]
      apply hcover
      have hqt : -τ cell/2 ≤ q.1 ∧ q.1 ≤ τ cell/2 := hq.1
      change q.1 ∈ Ioo (-(τ cell)) (τ cell) ∧
        q.2 ∈ ball ((0 : Euclidean (n-1)),(cell.1.1,T.reference.spatialPatch cell.1.1)) (R cell/32)
      exact ⟨⟨by linarith only [hqt.1,hτ],by linarith only [hqt.2,hτ]⟩,
        (closedBall_subset_ball (by linarith only [hR] : R cell/64 < R cell/32)) hq.2⟩
    have hballΩ : closedBall center (2*σ cell) ⊆ C ⁻¹' D := hworking.trans hWΩ
    have hΩK : MapsTo Prod.fst (C ⁻¹' D) (closedBall (0 : Euclidean n) rGeom) :=
      fun w hw ↦ interior_subset (hphysK (ball_subset_closedBall (hphys hw))).2.2
    have hphase : ∀ w ∈ C ⁻¹' D, (w.1,w.2.2) ∈ phaseDomain T :=
      fun w hw ↦ hdom (ball_subset_closedBall (hphys hw))
    have hconst := lowerConstant_mem_primitiveInitialScalars (n := n) cell.1.1 (R cell) hm hgap.le
    have hnonzero := LeadingCell.scalar_nonzero T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
      (fun _ ↦ m) hconst.1 hconst.2.1 hconst.2.2
    have hα r (hr : r ∈ primitiveInitialScalars (n := n) cell.1.1 (R cell) Mscalar m) :=
      LeadingCell.scalar_regular T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
        Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell r hr.1 hr.2.1 hr.2.2
    have htransport r (hr : r ∈ primitiveInitialScalars (n := n) cell.1.1 (R cell) Mscalar m) :=
      LeadingCell.scalar_transport T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
        Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell r hr.1 hr.2.1 hr.2.2
    have hcorrect r (hr : r ∈ primitiveInitialScalars (n := n) cell.1.1 (R cell) Mscalar m) :=
      (hcorrection R₀ ((le_max_left _ _).trans hR₀) stage u ell hu hF hi hrank hdata
        r hr.1 hr.2.1 hr.2.2).2
    have hSS0 : SS ≤ R₀ := (le_max_right _ _).trans hR₀
    have hQsource : Q.1 = projectedStress F := rfl
    close_cached_leading_source_application hsource
      [R₀,hSS0,stage,u,ell,hu,K,hK,Q,hQsource,row cell,col cell,Φ,Y,C ⁻¹' D,
        hΩ,hballΩ,hΩK,hphase,hnonzero,hα,htransport,hcorrect]
  · refine ⟨2,le_rfl,fun _ _ ↦ 0,fun _ _ ↦ le_rfl,?_⟩
    intro R₀ _ stage u ell _ K _ F hF hi hrank hdata
    exfalso
    apply hphysical
    have hphys := LeadingCell.fact1 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
      Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    have hρ2 : ρ cell ≤ 2*ρ cell := by linarith only [hρ]
    intro w hw
    exact interior_subset (hphys ((hcoeff.trans (closedBall_subset_closedBall hρ2)) hw)).2.2

end JanetCartan.PhysicalPrimary
