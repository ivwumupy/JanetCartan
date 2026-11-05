module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometry
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongGeometry
public import JanetCartan.Iteration.PhysicalPrimary.SourceEnvelope
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalFullStrainProfilesTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles

/-!
# The original uncontracted full-strain profile

Retain the matrix estimate before the half-stress contraction in the original
Source39/53 construction. Its scalar k+16 profile remains exactly the original
positive-density producer's input; no full-strain or response bound is assumed.
The same source dilation, finite physical history, retained leading transports,
original χenv and natural reserve are used throughout.

Consumer: `fullPrimaryResponse_fixedSolver_joint_graded`, followed by task13's
literal uncut reconstruction (`app:ch_response:eq:response-graded-source`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalFullStrainProfiles
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open RawPrimary NullTransport HamiltonPhase ResponsePrimarySources CorrectedAtoms
open ResponseSourceExtension LeadingWave.FullModulation PrimarySourceAdmission
open ResponseTransfer Sampling.BackgroundModulation Pseudodifferential FlowAmplitude ActualFlow

/-- The native fixed physical-ball certificate also controls the first
coordinate of the full working product ball, without selecting a new chart. -/
theorem working_ball_mapsTo_fst {n : ℕ}
    {a : Euclidean 3 × Euclidean (n-1)} {ρ b : ℝ}
    (h : closedBall (0 : Euclidean n) ρ ⊆ closedBall 0 b) :
    MapsTo Prod.fst (closedBall ((0 : Euclidean n),a) ρ) (closedBall 0 b) := by
  intro w hw
  rw [← closedBall_prod_same] at hw
  exact h hw.1

/-- Apply the actual retained correction and primitive scalar transport to the
uncontracted homogeneous source estimate. Unlike stress contraction this keeps
every entry of the full strain matrix, with the exact cubic size and reserve.
The original-data application below discharges the fixed geometry and the
retained leading tuple; only the original scalar budget remains explicit. -/
theorem exists_leading_profiles
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
    (hphysical : MapsTo Prod.fst
      (closedBall ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1)) (2*σ cell))
      (closedBall (0 : Euclidean n) rGeom))
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar reserve kMin : ℕ}
    (hreserve : 16+reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
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
      let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
        fullStrainEnvelope T Q F (row cell) (col cell) Φ Y scalar.val χenv τsource w.2 w.1
      ContDiffOn ℝ ∞ a (univ ×ˢ V) ∧
        ∀ k w, w.2 ∈ V → ‖iteratedFDeriv ℝ k a w‖ ≤ C k*(τsource^3*size)*K^(k-reserve) := by
  let center := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
  obtain ⟨SΓ,hSΓ,Γ,hΓ,hcorrection⟩ := exists_history_leading_correction_profiles
    G hrGeom hrR hRGeom T hball centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c hc E A H B cell hρ hR hτ hσ hworking hcoeff
    hBband (by omega) horder
  obtain ⟨SS,hSS,Csource,hCsource,hsource⟩ := exists_history_fullStrain_reserved_profiles
    hn G hrGeom hrR hRGeom hreference T center (by positivity : 0 < 2*σ cell) hphysical
    cell.1.1 hR hm hgap Γ Ar hΓ hAr χenv hchart hV hproduct hBband hreserve horder
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

end JanetCartan.PhysicalPrimary.OriginalFullStrainProfiles

construct_original_full_strain_profiles
apply_original_full_strain_profiles
