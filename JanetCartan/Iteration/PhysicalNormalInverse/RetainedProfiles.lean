module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrection
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RetainedCoefficientProfiles

/-!
# The five corrected-normal coefficient profiles on the retained physical cell

For `app:ch_waves:eq:WKB-grading` and the deterministic middle mean-normal term,
apply the actual physical-history correction producer to the SAME retained
leading tuple.  Its fixed doubled sigma-cover window gives the coefficient
profiles on the original sigma-cover window.  The source normal gap and all
profile functions precede the history and initial scalar.  The separate full
inverse response `Cresp` is not asserted here.

The remaining original-data application supplies `RetainedLeadingData` from
`CurrentLeading.AtPatch.fact0` and the initial scalar's profile from the actual
positive-density constructor.  No coefficient-profile estimate or desired
normal-comparison estimate is a premise of this physical producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000
set_option maxRecDepth 8000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalNormalInverse
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
  LeadingWave.FullModulation PhysicalPrimary CorrectedAtoms RawPrimary
  RawPrimary.AmplitudeGrades.Polynomial NullTransport ActualFlow

/-- Construct the literal phase-gradient, two normal and two reconstruction
profiles used by `FullComparison` on the actual physical history.  The original
leading solution and correction producer discharge the amplitude budgets;
`RF,Rr >= rpar+16` retains exactly their differential reserve.  Static window
geometry is derived from the supplied retained tuple, not reselected. -/
theorem exists_history_retained_normal_coefficient_profiles
    {n : ℕ} (G : FlatReference n)
    {rGeom RGeom : ℝ} (hrGeom : 0 < rGeom) (hrR : rGeom < RGeom)
    (hRGeom : RGeom < G.domain.chartRadius)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 RGeom) isOpen_ball)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ closedBall 0 rGeom)
    (centers : Finset (parameterCube P.radius)) (row col : centers → Fin n)
    (ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ)
    (Ωc : centers → Set (Euclidean n × Euclidean 3)) (ρc Bc gc Bfull : centers → ℝ)
    (Mscalar m c : ℝ) (hc : 0 < c) (E : ℕ → ℝ) (A H B : centers → ℕ → ℝ)
    (hE : ∀ j, 0 < E j) (Ar : ℕ → ℝ) (hAr : ∀ j, 0 ≤ Ar j)
    (cell : centers) (hρ : 0 < ρ cell) (hR : 0 < R cell)
    (hτ : 0 < τ cell) (hσ : 0 < σ cell)
    (hworking : let a := ((0 : Euclidean n), (cell.1.1, T.reference.spatialPatch cell.1.1))
      closedBall a (2 * σ cell) ⊆
        (NullTransport.FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ cell / 2) (τ cell / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)),
              (cell.1.1, T.reference.spatialPatch cell.1.1)) (R cell / 64)))
    (hcoeff : let a := ((0 : Euclidean n), (cell.1.1, T.reference.spatialPatch cell.1.1))
      closedBall a (2 * σ cell) ⊆ closedBall a (ρ cell))
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Mgeom > (0 : ℝ), ∃ gnormal > (0 : ℝ),
      ∃ Pξ Pζ Clead Ccorr : ℕ → ℝ,
        (∀ j, 0 < Pξ j) ∧ (∀ j, 0 < Pζ j) ∧
        (∀ j, 0 < Clead j) ∧ (∀ j, 0 < Ccorr j) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ (hF : ContDiffOn ℝ ∞ F (ball 0 RGeom))
        (hi : IsImmersionOn F (ball 0 RGeom))
        (hrank : HasFullNormalRankOn F (ball 0 RGeom))
        (hdata : RetainedLeadingData T (K := closedBall (0 : Euclidean n) rGeom)
          centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
          Mscalar m c E A H B F hF hi hrank),
      let Q := LeadingData.Q T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata
      let Φ := LeadingCell.Φ T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let Y := LeadingCell.Y T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let a := ((0 : Euclidean n), (cell.1.1, T.reference.spatialPatch cell.1.1))
      let I := closedBall ((0 : Euclidean (n - 1)), cell.1.1) (R cell / 8)
      let J := closedBall a (σ cell)
      let O := ball a (2 * σ cell)
      let L := currentCoefficientScale R₀ stage
      ∀ (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
        ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), cell.1.1) (R cell / 4)) →
        cNorm I 14 initial ≤ Mscalar →
        (∀ p ∈ ball ((0 : Euclidean (n - 1)), cell.1.1) (R cell / 8), m ≤ initial p) →
      ∀ (rpar Rr : ℕ), 20 * (n + 1) + 1 ≤ rpar →
        14 + (rpar + 2) ≤ rStar → 14 + (rpar + 2) ≤ Rr →
        HasDerivativeProfile I initial Rr L Ar →
        cNorm (closedBall (0 : Euclidean n) rGeom) (20 * (n + 1) + 5) F ≤ Mgeom ∧
        (∀ x ∈ closedBall (0 : Euclidean n) rGeom, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ closedBall (0 : Euclidean n) rGeom, ∀ w ∈ normalSpace F x,
          gnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        (∀ w ∈ O, (w.1, w.2.2) ∈ phaseDomain T) ∧
        ContDiffOn ℝ ∞ (fullLeadingNormal T Q F (row cell) (col cell) Φ Y initial) O ∧
        ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F (row cell) (col cell) Φ Y initial) O ∧
        ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F (row cell) (col cell) Φ Y initial) O ∧
        ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F (row cell) (col cell) Φ Y initial) O ∧
        HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Pξ ∧
        HasDerivativeProfile J (fullLeadingNormal T Q F (row cell) (col cell) Φ Y initial)
          (rpar + 2) L Clead ∧
        HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F (row cell) (col cell) Φ Y initial)
          (rpar + 1) L Ccorr ∧
        HasDerivativeProfile J (fullLeadingReconstruction T Q F (row cell) (col cell) Φ Y initial)
          (rpar + 2) L Clead ∧
        HasDerivativeProfile J (fullCorrectionReconstruction T Q F (row cell) (col cell) Φ Y initial)
          (rpar + 1) L Ccorr ∧
        ∀ j, ∀ w ∈ J,
          ‖iteratedFDeriv ℝ j (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            fderiv ℝ (phase T Q w.1) w.2.2) w‖ ≤ Pζ j * L ^ (j - 1 - (rpar + 2)) := by
  classical
  let a := ((0 : Euclidean n), (cell.1.1, T.reference.spatialPatch cell.1.1))
  let I := closedBall ((0 : Euclidean (n - 1)), cell.1.1) (R cell / 8)
  obtain ⟨SΓ, hSΓ, Γ, hΓ, hcorrection⟩ := exists_history_leading_correction_profiles
    G hrGeom hrR hRGeom T hball centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c hc E A H B cell hρ hR hτ hσ hworking hcoeff
    hBband hStar horder
  obtain ⟨Sg, hSg, _Cgeom, _hCgeom, κ, hκ, hgeometry⟩ :=
    PhysicalGeometry.exists_geometric_neighborhood G hrGeom hrR hRGeom hBband
      (by omega : 8 ≤ rStar) horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨AF, hAF, hprofileF⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) rGeom)
    (fun _ _ ↦ G.contDiff.contDiffAt) hBband horder
  obtain ⟨Pξ, Pζ, Clead, Ccorr, hPξ, hPζ, hClead, hCcorr, hprofiles⟩ :=
    exists_retainedPrimary_coefficient_profiles_before_geometry
      (N := embeddingDimension n) T a hσ (isCompact_closedBall _ _)
      (closedBall_subset_ball hrR) hball I (by norm_num : (0 : ℝ) < 1 / 4)
      hκ AF Ar E Γ hAF hAr hE hΓ
  let Mgeom := AF (20 * (n + 1) + 5) + 1
  have hMgeom : 0 < Mgeom := by
    dsimp only [Mgeom]
    linarith [hAF (20 * (n + 1) + 5)]
  refine ⟨max SΓ Sg, hSΓ.trans (le_max_left _ _), Mgeom, hMgeom, κ, hκ,
    Pξ, Pζ, Clead, Ccorr, hPξ, hPζ, hClead, hCcorr, ?_⟩
  intro R₀ hR₀ stage u ell hu F hF hi hrank hdata Q Φ Y a' I' J O L
    initial hinit h14 hlower rpar Rr hfloor hRF hRr hpr
  have hRg : Sg ≤ R₀ := (le_max_right _ _).trans hR₀
  have hRΓ : SΓ ≤ R₀ := (le_max_left _ _).trans hR₀
  have htwo : 2 ≤ R₀ := hSg.trans hRg
  have hpF := hprofileF R₀ htwo stage u ell hu _ Subset.rfl
  obtain ⟨_hi, _hrank, _hC4, hmetric, hnormal, _hQ, _hframe⟩ :=
    hgeometry R₀ hRg stage u ell hu
  have hmetricK (x) (hx : x ∈ closedBall (0 : Euclidean n) rGeom) (v) :=
    hmetric x (closedBall_subset_ball hrR hx) v
  have hnormalK (x) (hx : x ∈ closedBall (0 : Euclidean n) rGeom) (w)
      (hw : w ∈ normalSpace F x) := hnormal x (closedBall_subset_ball hrR hx) w hw
  have hFM : cNorm (closedBall (0 : Euclidean n) rGeom) (20 * (n + 1) + 5) F ≤ Mgeom := by
    have hb := hpF (20 * (n + 1) + 5)
    have he : 20 * (n + 1) + 5 - rStar = 0 := by omega
    simp only [he, pow_zero, mul_one] at hb
    exact hb.trans (le_add_of_nonneg_right zero_le_one)
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
  have hΩ : IsOpen (C ⁻¹' D) := hD.preimage C.continuous
  have hWΩ : W ⊆ C ⁻¹' D := by
    rintro w ⟨q, hq, rfl⟩
    change C (C.symm q) ∈ D
    rw [C.apply_symm_apply]
    apply hcover
    have hqt : -τ cell / 2 ≤ q.1 ∧ q.1 ≤ τ cell / 2 := hq.1
    change q.1 ∈ Ioo (-(τ cell)) (τ cell) ∧
      q.2 ∈ ball ((0 : Euclidean (n - 1)),
        (cell.1.1, T.reference.spatialPatch cell.1.1)) (R cell / 32)
    exact ⟨⟨by linarith only [hqt.1, hτ], by linarith only [hqt.2, hτ]⟩,
      (closedBall_subset_ball (by linarith only [hR] : R cell / 64 < R cell / 32)) hq.2⟩
  have hballΩ : closedBall a (2 * σ cell) ⊆ C ⁻¹' D := hworking.trans hWΩ
  have hρ2 : ρ cell ≤ 2 * ρ cell := by linarith only [hρ]
  have hlarge : closedBall a (2 * σ cell) ⊆ closedBall a (2 * ρ cell) :=
    hcoeff.trans (closedBall_subset_closedBall hρ2)
  have hphase : closedBall a (2 * σ cell) ⊆ domain T := hlarge.trans hdom
  have hphysical : MapsTo Prod.fst (closedBall a (2 * σ cell)) (closedBall 0 rGeom) :=
    fun w hw ↦ interior_subset (hphysK (hlarge hw)).2.2
  have hspace : closedBall a.1 (2 * σ cell) ⊆ closedBall (0 : Euclidean n) rGeom := by
    intro x hx
    apply hphysical (show (x, a.2) ∈ closedBall a (2 * σ cell) from ?_)
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hx
  obtain ⟨hb₀, _hnull, hleading⟩ := LeadingCell.solution T centers row col ρ R τ Rc τc Mc
    rcomp δcomp σ Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
    initial hinit h14 hlower
  obtain ⟨hb₁, hcorrectBig⟩ := hcorrection R₀ hRΓ stage u ell hu hF hi hrank hdata
    initial hinit h14 hlower
  have hsmall : closedBall a (σ cell) ⊆ closedBall a (2 * σ cell) :=
    closedBall_subset_closedBall (by linarith only [hσ])
  have hcorrect (j : ℕ) : cNorm (closedBall a (σ cell)) j
      (fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial) ≤
      Γ j * (1 + cNorm (closedBall 0 rGeom) (j + 14) F + cNorm I (j + 14) initial) := by
    have hregular : ContDiffOn ℝ ∞
        (fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial) (C ⁻¹' D) := by
      simpa only [F, Q, Φ, Y, C, D] using hb₁
    have hmono : cNorm (closedBall a (σ cell)) j
        (fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial) ≤
        cNorm (closedBall a (2 * σ cell)) j
          (fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial) :=
      cNorm_mono_set_of_contDiffAt (r := j)
        (f := fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial)
        hsmall (isCompact_closedBall _ _)
        (fun w hw ↦ (hregular.contDiffAt (hΩ.mem_nhds (hballΩ hw))).of_le (by simp))
    apply hmono.trans
    simpa only [F, Q, Φ, Y, a, I] using hcorrectBig j
  refine ⟨hFM, hmetricK, hnormalK, fun w hw ↦ hphase (ball_subset_closedBall hw), ?_⟩
  have hL : 1 ≤ L := one_le_currentCoefficientScale (by linarith only [htwo]) stage
  run_tac Lean.Elab.Tactic.withMainContext do
    let get (name : Lean.Name) : Lean.MetaM Lean.Expr := do
      let some d := (← Lean.getLCtx).findFromUserName? name
        | throwError "retained profile application: missing local {name}"
      pure (Lean.mkFVar d.fvarId)
    let mut args : Array Lean.Expr := #[]
    for name in #[`F, `hF, `hi, `hrank, `hspace, `hphase, `hmetricK, `hnormalK] do
      args := args.push (← get name)
    let qproperty ← Lean.Meta.mkAppM ``Subtype.property #[← get `Q]
    args := args.push (← Lean.Meta.mkAppM ``And.right #[qproperty])
    args := args.push (Lean.mkApp (← get `row) (← get `cell))
    args := args.push (Lean.mkApp (← get `col) (← get `cell))
    for name in #[`Φ, `Y, `initial] do
      args := args.push (← get name)
    args := args.push (← Lean.Meta.inferType (← get `hΩ)).appArg!
    for name in #[`hΩ, `hballΩ, `hb₀, `hb₁, `hleading, `hcorrect,
        `rStar, `Rr, `rpar, `L, `hL, `hRF, `hRr, `hpF, `hpr] do
      args := args.push (← get name)
    unless args.size == 30 do
      throwError "retained profile application: expected thirty checked arguments"
    let proof := Lean.mkAppN (← get `hprofiles) args
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end JanetCartan.PhysicalNormalInverse
