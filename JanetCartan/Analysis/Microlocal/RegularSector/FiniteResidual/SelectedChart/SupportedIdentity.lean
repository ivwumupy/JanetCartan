module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Collars
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Assembly
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Supported
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Identification

/-!
# The complete residual on the retained supported chart

Apply the complete-residual identity to the SAME smooth supported phase and
collared amplitudes from `SelectedChartEvolutionAt`. Construct all retarded
and PDO regularizations; localize coefficients only inside the proof. The
four symbol budgets are the precise outputs of `FiniteAlgebraic.Construction`,
`FinitePdo.Source` and the selected-family endpoint producer.

Consumer: the common-mask local solver equation before finite summation.
Source: `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`;
`paper.tex`, `app:ch_regular_base:prop:complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.AmplitudeBounds Characteristic.ConicPhase
open Characteristic.ConicAmplitude Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FourierIntegral.LowBounds FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution
open FiniteEvolution.PhysicalCutoff
open JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral.LowBounds.FrequencyCutoff
open Characteristic.PdoRealization Characteristic.RootFamily
open Pseudodifferential FourierIntegral.FullLowBounds
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- The four precise PDO budgets and retained primitive chart outputs imply
`PS = Op(α) + R` on the original common physical ball, for all L² inputs.
Every graph regularization and strong limit is constructed in the proof.
The full `B` term, all three residual terms, and `Op(α)-I` are retained.
The cancellation, endpoint and phase premises below are exactly the outputs
of `SelectedChartEvolutionAt`; the smooth algebraic symbol and complement
identity are outputs of `exists_finite_physical_algebraic_pdos`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem completeResidual_of_selected_supported_chart
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (L : ℝ) (hL : 1 ≤ L) (hLf : f.radialThreshold ≤ L) (angular : Euclidean d → ℝ)
    (hang : ContDiff ℝ ∞ angular)
    (hangpos : ∀ η ∈ tsupport angular, 0 < (f.chart p).radialSection η)
    (hangular : ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L)
      (physicalCoordinates (f.chart p).index ξ) : ℂ)),
      conicMask angular =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ)) :
    let c := f.chart p
    let z : Z := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat)
      (_hQ : ContDiffOn ℝ ∞ Q Ω) (_hB : ContDiffOn ℝ ∞ B Ω),
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
    closedBall (z.1, z) c.targetRadius ⊆ C.target →
    ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
    (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
    (∀ v ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1/2) →
    (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase C) ≤
      c.phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
    (∀ v ∈ C.target, (C.symm v).2.1 = v.2.1) →
    ∀ Fs : Fin 3 → T → CMat,
    (∀ j, ContDiff ℝ ∞ (Fs j)) →
    let W := fun j : Fin 3 ↦ collared c.radialSection (if j = 0 then 0 else 1) angular (Fs j)
    (∀ j, ContDiff ℝ ∞ (W j)) →
    (∀ j, tsupport (W j) ⊆ ConicPhase.domain c.radialSection
      (C.target ∩ C.symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
        (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2))))) →
    (∀ v : T, c.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
      (fun k ↦ W 2 v k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit c.index) v.2.1 v.2.2.2 y) k j)
          ((coordinateSplit c.index).symm (v.1, v.2.2.1))) →
    ∀ G : T → ℝ,
    (∀ v ∈ tsupport (W 0) ∪ tsupport (W 1), G =ᶠ[𝓝 v] ConicPhase.phase c.radialSection C) →
    (∀ v : T, c.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → W 2 v ≠ 0 →
      G =ᶠ[𝓝 v] ConicPhase.phase c.radialSection C) →
    ContDiff ℝ ∞ G →
    (∀ t y η, G (t, (t, (y, η))) = inner ℝ y η) →
    let A : E → Fin (d+1) → CMat := fun y i ↦ (coefficient c.index Q y i).map Complex.ofReal
    let Bc : E → CMat := fun y ↦ (zeroth c.index B y).map Complex.ofReal
    let W₀ : TwoTimeAmplitude d (d+1) := curryCharacteristicMatrix (W 0)
    let W₁ : TwoTimeAmplitude d (d+1) := curryCharacteristicMatrix (W 1)
    let Ψ : TwoTimePhase d := fun t s y η ↦ G (t, (s, (y, η)))
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L)
      (physicalCoordinates c.index ξ) : ℂ)
    let bm : E → E → CMat := conicBminus c.radialSection c.index Q h c.row c.col
    let σ : E → Euclidean d → ℂ := conicSourceSymbol c.radialSection (conicMask angular) c.sourceMask
    let σf : E → Euclidean d → ℂ := conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask
    (∀ y : E, c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
      WKB.firstOrderApply (fun y i ↦ (A y i).mulVecLin) (fun y ↦ (Bc y).mulVecLin)
        (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
          (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) y =
      Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply A Bc W₁ (y 0) s (spatialPart y) η i j)) →
    (∀ y : E, c.timeMask (y 0) = 1 → ∀ η,
      A y 0 * W₀ (y 0) (y 0) (spatialPart y) η =
        σ y η • projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η)) →
    ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bm σf β)) →
    (∀ ξ ∈ tsupport β, ∀ y ∈ physicalCoordinates c.index ⁻¹' Ω,
      (∑ a, (ξ a : ℂ) • A y a) * bm y ξ =
        1 - projector c.index Q h c.row c.col y
          ((c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ)) →
    ∀ (Rbox Mbound : Fin 4 → ℝ),
    (∀ k, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (directPDOSymbols A Bc W₁ bm σf β k)) (Rbox k) (Mbound k)) →
    let U : Set E := physicalCoordinates c.index ⁻¹' ball x f.physicalRadius
    let P : Fin 4 → H →L[ℂ] H := fun k ↦ maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (directPDOSymbols A Bc W₁ bm σf β k)
    let b : Bool → TwoTimeAmplitude d (d+1) := directRetardedAmplitudes A Bc W₀ W₁
    ∃ Op : Bool → H →L[ℂ] H,
      (∀ k u, Op k u = elapsedGraphIntegral (3*c.maskRadius/4) Ψ (b k)
        (chartOutputMask f p) (chartInputMask f p) β u) ∧
      (∀ k u, (Op k).adjoint u = ∫ r in Icc 0 (3*c.maskRadius/4),
        (elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r).adjoint u) ∧
      (∀ k (u : graphTestSpace (d+1) (d+1)), Op k (graphTestToLp u) =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ (b k) (chartOutputMask f p)
          (chartInputMask f p) β (chartPhysicalMasks_properties f p).2.1
          (z.1-c.maskRadius/2) u y)) ∧
      let S := Op false + (1 / Complex.I) • P 0
      let R := P 2 + Op true + (1 / Complex.I) • P 3
      (∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
        physicalTestAction (coefficient c.index Q) (zeroth c.index B)
          (fun y ↦ (S u y).ofLp) φ j = ∫ y, φ y • ((P 1 + R) u) y j) ∧
      (∀ V : Set E, IsOpen V → V ⊆ U → ∀ u du,
        Mollification.HasWeakFDerivOn volume (fun y ↦ (S u y).ofLp) du V →
        physicalWeakApply (coefficient c.index Q) (zeroth c.index B)
          (fun y ↦ (S u y).ofLp) du =ᵐ[volume.restrict V]
            fun y ↦ (((P 1 + R) u) y).ofLp) ∧
      P 1 + R = ContinuousLinearMap.id ℂ H + ((P 1 - ContinuousLinearMap.id ℂ H) + R) := by
  classical
  have hm := @chartPhysicalMasks_properties d Ω x RQ M A₀ K f p
  have ho := hm.1
  have hs := hm.2.1
  have hoc := hm.2.2.1
  have hsc := hm.2.2.2.1
  have hcarrier := hm.2.2.2.2
  have hgeom := @selected_output_retained_geometry d Ω x RQ M A₀ K f p hρb hsrcρ
  have hslab := hgeom.2.1
  have htime := hgeom.2.2
  intro c z Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs hFs W hWs
    hsupport hphysical G hG hGres hGs hGdiag A Bc W₀ W₁ Ψ β bm σ σf hcancel hlead
    hc hcomp Rbox Mbound hbudget U P b
  have hχΩ : ∀ y ∈ tsupport (chartOutputMask f p), physicalCoordinates c.index y ∈ Ω := by
    intro y hy
    apply hKΩ
    have hy' := hcarrier hy
    change dist y ((physicalCoordinates c.index).symm x) ≤ RQ at hy'
    change dist (physicalCoordinates c.index y) x ≤ RQ
    conv_lhs => arg 2; rw [← (physicalCoordinates c.index).apply_symm_apply x]
    rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, ← dist_eq_norm]
    exact hy'
  have hExt := @exists_smooth_coordinate_coefficients d c.index Ω hΩ Q B hQ hB
    (tsupport (chartOutputMask f p)) (isClosed_tsupport (chartOutputMask f p)) hχΩ
  let Ae : E → Fin (d+1) → Mat := hExt.choose
  let Be : E → Mat := hExt.choose_spec.choose
  have hAe : ContDiff ℝ ∞ Ae := hExt.choose_spec.choose_spec.1
  have hBe : ContDiff ℝ ∞ Be := hExt.choose_spec.choose_spec.2.1
  have he : ∀ y ∈ tsupport (chartOutputMask f p),
      Ae =ᶠ[𝓝 y] coefficient c.index Q ∧ Be =ᶠ[𝓝 y] zeroth c.index B :=
    hExt.choose_spec.choose_spec.2.2
  let Ac := fun y i ↦ (Ae y i).map Complex.ofReal
  let Bext := fun y ↦ (Be y).map Complex.ofReal
  have hAeq (y) (hy : y ∈ tsupport (chartOutputMask f p)) : Ac y = A y := by
    change (fun i ↦ (Ae y i).map Complex.ofReal) = (fun i ↦ (coefficient c.index Q y i).map Complex.ofReal)
    exact congrArg (fun X : Fin (d+1) → Mat ↦ fun i ↦ (X i).map Complex.ofReal) (he y hy).1.eq_of_nhds
  have hBeq (y) (hy : y ∈ tsupport (chartOutputMask f p)) : Bext y = Bc y := by
    exact congrArg (fun X : Mat ↦ X.map Complex.ofReal) (he y hy).2.eq_of_nhds
  have hAe' (a i j) : ContDiff ℝ ∞ (fun y ↦ Ae y a i j) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp ((contDiff_pi.mp hAe) a)
  have hBe' (i j) : ContDiff ℝ ∞ (fun y ↦ Be y i j) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp hBe
  have hU : IsOpen U := isOpen_ball.preimage (physicalCoordinates c.index).continuous
  have hplateau (y) (hy : y ∈ U) : chartOutputMask f p =ᶠ[𝓝 y] fun _ ↦ (1 : ℂ) := by
    have hp := f.outputMask_plateau (ball_subset_closedBall hy)
    have hf : f.outputMask =ᶠ[𝓝 (physicalCoordinates c.index y)] fun _ ↦ (1 : ℝ) := by
      filter_upwards [isOpen_interior.mem_nhds hp] with v hv
      exact interior_subset (s := {y | f.outputMask y = 1}) hv
    filter_upwards [hf.comp_tendsto (physicalCoordinates c.index).continuous.continuousAt] with v hv
    change (f.outputMask (physicalCoordinates c.index v) : ℂ) = 1
    change f.outputMask (physicalCoordinates c.index v) = 1 at hv
    rw [hv, Complex.ofReal_one]
  have hUχ (y) (hy : y ∈ U) : y ∈ tsupport (chartOutputMask f p) :=
    subset_tsupport _ (by
      change chartOutputMask f p y ≠ 0
      rw [(hplateau y hy).eq_of_nhds]
      exact one_ne_zero)
  have hβ : ContDiff ℝ ∞ β := Complex.ofRealCLM.contDiff.comp
    ((contDiff_dilatedConicMask (f.angularMask_smooth p) (2*L)).comp
      (physicalCoordinates c.index).contDiff)
  have hcollar := selected_directPDOSymbols_collar f p (show 2*f.radialThreshold ≤ 2*L by linarith)
    angular hangular A Bc W₁ bm
  have hc' : ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bm σ β)) := by
    have heq := congrFun hcollar 0
    change directAlgebraicSymbol bm σ β = directAlgebraicSymbol bm σf β at heq
    rw [heq]
    exact hc
  have hρ : tsupport (conicMask angular) ⊆ {η | 0 < c.radialSection η} :=
    conicMask_tsupport_subset_cone angular hangpos (fun η hη t ht ↦ by
      change 0 < c.radialSection (t • η)
      simpa only [map_smul, smul_eq_mul] using mul_pos ht hη)
  have hσ : ContDiff ℝ ∞ (Function.uncurry σ) :=
    contDiff_conicSourceSymbol c.radialSection (conicMask angular) (contDiff_conicMask hang)
      hρ c.sourceMask c.sourceMask_smooth
  have hregs :=
    @exists_selected_supported_graph_regularizations d Ω x RQ M A₀ K f p hρb hsrcρ L hL angular hang
      hangular
      Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs hFs hWs hsupport hphysical G hG hGres
  have hzero := hregs.1
  let D : Bool → ℝ := hregs.2.choose
  let Treg : Bool → ℕ → ℝ → H →L[ℂ] H := hregs.2.choose_spec.choose
  have hr := hregs.2.choose_spec.choose_spec
  have htbound := hr.2.1
  have ht := hr.2.2.1
  have htAdj := hr.2.2.2.1
  have htlim := hr.2.2.2.2.1
  have htlimAdj := hr.2.2.2.2.2.1
  let Op : Bool → H →L[ℂ] H := hr.2.2.2.2.2.2.choose
  have hOpdata := hr.2.2.2.2.2.2.choose_spec
  have hOpint := hOpdata.2.1
  have hOpadj := hOpdata.2.2.1
  have hOptest := hOpdata.2.2.2.1
  have hregroup : ContDiff ℝ ∞ (fun v : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      (v.1.1, (v.1.2, (v.2.1, v.2.2)))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd))
  have hΔ : 0 ≤ 3*c.maskRadius/4 := by
    have := c.maskRadius_pos
    positivity
  have hbmask (k : Bool) (r : ℝ) := elapsedDirectAmplitude_eq_of_coefficients Ac A Bext Bc
    W₀ W₁ (chartOutputMask f p) (chartInputMask f p) β hAeq hBeq k r
  have hgraph (k : Bool) (r : ℝ) :
      elapsedGraph Ψ (directRetardedAmplitudes Ac Bext W₀ W₁ k)
        (chartOutputMask f p) (chartInputMask f p) β r =
      elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r := by
    unfold elapsedGraph
    rw [hbmask]
  have hpmask (k : Fin 4) :
      (fun y v ξ ↦ (chartOutputMask f p y * chartInputMask f p v) •
        directPDOSymbols Ac Bext W₁ bm σ β k y ξ) =
      fun y v ξ ↦ (chartOutputMask f p y * chartInputMask f p v) •
        directPDOSymbols A Bc W₁ bm σf β k y ξ := by
    rw [maskedDirectPDOAmplitude_eq_of_coefficients Ac A Bext Bc W₁ bm σ
      (chartOutputMask f p) (chartInputMask f p) β hAeq hBeq k]
    rw [hcollar]
  have hpdo (k : Fin 4) : maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (directPDOSymbols Ac Bext W₁ bm σ β k) = P k := by
    unfold maskedPhysicalPDO
    rw [hpmask]
    rfl
  let Preg : Fin 4 → ℕ → H →L[ℂ] H := fun k j ↦
    fullGraphOperator (fun y ξ ↦ inner ℝ y ξ) (frequencyCutFullAmplitude (complexPhysicalCutoff j)
      (fun y v ξ ↦ (chartOutputMask f p y * chartInputMask f p v) •
        directPDOSymbols A Bc W₁ bm σf β k y ξ))
  have hp (k : Fin 4) (j : ℕ) (u : graphTestSpace (d+1) (d+1)) :=
    canonicalGraph_frequencyCut_realizes (Nat.succ_pos d) _ (hbudget k)
      (complexPhysicalCutoff j) (complexPhysicalCutoff_contDiff j) zero_le_one
      (complexPhysicalCutoff_norm_le j) u
  have hplim (k : Fin 4) (u : H) := tendsto_canonicalGraph_frequencyCut (Nat.succ_pos d)
    _ (hbudget k) complexPhysicalCutoff complexPhysicalCutoff_contDiff le_rfl
    complexPhysicalCutoff_norm_le complexPhysicalCutoff_tendsto u
  have hleadExt (y : E) (hy : y ∈ U) (η : Euclidean d) :
      Ac y 0 * W₀ (y 0) (y 0) (spatialPart y) η =
        σ y η • projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η) := by
    rw [hAeq y (hUχ y hy)]
    exact hlead y (htime y (hUχ y hy)).eq_of_nhds η
  have hcompExt (y : E) (hy : y ∈ U) (ξ : E) (hξ : β ξ ≠ 0) :
      (∑ a, (ξ a : ℂ) • Ac y a) * bm y ξ =
        1 - projector c.index Q h c.row c.col y
          ((c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ) := by
    rw [hAeq y (hUχ y hy)]
    exact hcomp ξ (subset_tsupport β hξ) y (hχΩ y (hUχ y hy))
  have hcancelExt (y : E) (hy : y ∈ U) (s : ℝ) (η : Euclidean d) (j : Fin (d+1)) :
      WKB.firstOrderApply (fun y i ↦ (Ac y i).mulVecLin) (fun y ↦ (Bext y).mulVecLin)
        (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
          (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) y =
      Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply Ac Bext W₁ (y 0) s (spatialPart y) η i j) := by
    rw [firstOrderApply_eq_of_coefficients Ac A Bext Bc _ (hAeq y (hUχ y hy)) (hBeq y (hUχ y hy)),
      twoTimePhysicalApply_eq_of_coefficients Ac A Bext Bc W₁ (hAeq y (hUχ y hy)) (hBeq y (hUχ y hy))]
    exact hcancel y (htime y (hUχ y hy)) s η j
  dsimp only [Ac, Bext] at hbmask hgraph hpmask hpdo
  have hres0 := completeResidual_operators_of_graph_regularizations (d := d) (q := d+1) Ae Be hAe' hBe'
    Ψ W₀ W₁ bm σ (fun y η ↦ projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η))
    β (chartOutputMask f p) complexPhysicalCutoff (z.1-c.maskRadius/2) (3*c.maskRadius/4) hΔ
  have hres1 := hres0 (U := U)
    (hGs.comp hregroup) ((hWs 0).comp hregroup) ((hWs 1).comp hregroup) hc' hβ ho
    complexPhysicalCutoff_contDiff complexPhysicalCutoff_hasCompactSupport
  have hres2a := hres1 hU
  have hσcont (y : E) : Continuous (σ y) := by
    exact Continuous.uncurry_left y hσ.continuous
  have hres2 := hres2a (fun y _ ↦ hσcont y)
  have hres3 := hres2 hplateau hGdiag
  have hres4 := hres3 hleadExt
  have hres5 := hres4 hcompExt
  have hres6 := hres5 hcancelExt
  have hres7 := hres6 (chartInputMask f p) hs hoc hsc
  have hres8 := hres7 (fun y hy ↦ hslab y (subset_tsupport _ hy))
  have hzero₀ : ∀ t s y η, s ≤ z.1-c.maskRadius/2 → W₀ t s y η = 0 := hzero 0
  have hzero₁ : ∀ t s y η, s ≤ z.1-c.maskRadius/2 → W₁ t s y η = 0 := hzero 1
  have hres := hres8 hzero₀ hzero₁
  have hresult := hres Treg D
    (by
      intro k j r hr u
      rw [hbmask]
      exact ht k j r hr u)
    (by
      intro k j r hr u
      simp only [hbmask]
      exact htAdj k j r hr u)
    htbound
    (by
      intro k r hr u
      rw [hgraph]
      exact htlim k r hr u)
    (by
      intro k r hr u
      rw [hgraph]
      exact htlimAdj k r hr u)
    Preg
    (by
      intro k j u
      refine (hp k j u).trans ?_
      exact Filter.Eventually.of_forall fun y ↦ congrArg
        (fun amp : E → E → E → CMat ↦ graphTestOutput (fun y ξ ↦ inner ℝ y ξ)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j) amp) u y) (hpmask k).symm)
    (by
      intro k u
      exact (congrArg (fun op : H →L[ℂ] H ↦
        Tendsto (fun j ↦ Preg k j u) atTop (𝓝 (op u))) (hpdo k)).mpr (hplim k u))
  have hresdata := hresult.choose_spec
  have hOp'int := hresdata.2.1
  have hOp'eq : hresult.choose = Op := by
    funext k
    apply ContinuousLinearMap.ext
    intro u
    refine (hOp'int k u).trans (Eq.trans ?_ (hOpint k u).symm)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r ↦ congrArg (fun op : H →L[ℂ] H ↦ op u) (hgraph k r)
  have htest : ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction Ae Be (fun y ↦ ((Op false + (1 / Complex.I) • P 0) u y).ofLp) φ j =
        ∫ y, φ y • ((P 1 + (P 2 + Op true + (1 / Complex.I) • P 3)) u) y j := by
    intro u φ hφ hcφ hφU j
    have hh := hresdata.2.2.2.2.1 u φ hφ hcφ hφU j
    simpa only [hOp'eq, hpdo] using hh
  refine ⟨Op, hOpint, hOpadj, hOptest, ?_, ?_, ?_⟩
  · intro u φ hφ hcφ hφU j
    exact (physicalTestAction_eq_of_coefficients_on_support Ae (coefficient c.index Q)
      Be (zeroth c.index B) _ φ
      (fun y hy ↦ (he y (hUχ y (hφU hy))).1.eq_of_nhds)
      (fun y hy ↦ (he y (hUχ y (hφU hy))).2.eq_of_nhds) j).symm.trans
        (htest u φ hφ hcφ hφU j)
  · intro V hV hVU u du hdu
    let J : EuclideanSpace ℂ (Fin (d+1)) →L[ℝ] (Fin (d+1) → ℂ) :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (d+1) ↦ ℂ)).toContinuousLinearMap.restrictScalars ℝ
    have hg : MemLp (fun y ↦ (((P 1 + (P 2 + Op true + (1 / Complex.I) • P 3)) u) y).ofLp)
        2 volume := J.comp_memLp' (Lp.memLp _)
    have hv := physicalWeakApply_ae_eq_of_test Ae Be hAe' hBe' hV hdu
      ((hg.locallyIntegrable (by norm_num)).locallyIntegrableOn V)
      (fun φ hφ hcφ hφV j ↦ htest u φ hφ hcφ (hφV.trans hVU) j)
    filter_upwards [hv, ae_restrict_mem hV.measurableSet] with y hy hyV
    have ha := (he y (hUχ y (hVU hyV))).1.eq_of_nhds
    have hb := (he y (hUχ y (hVU hyV))).2.eq_of_nhds
    funext j
    simpa only [physicalWeakApply, ha, hb] using congrFun hy j
  · abel

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
