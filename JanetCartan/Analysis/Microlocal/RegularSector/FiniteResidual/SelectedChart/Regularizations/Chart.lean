module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Collared
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Supported
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Identification

/-!
# The actual selected-chart graph regularizations

The original finite-family chart masks are used, with the same root, chart,
supported phase and buffered amplitudes retained by `SelectedChartEvolutionAt`.
Every primitive geometric and symbol input is discharged. The third collared
matrix is identified with the full physical `PW₁` on the actual output plateau.
Consumer: `completeResidual_operators_of_graph_regularizations`, for
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
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
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- Construct both graph regularizations for the SAME retained supported
phase, literal `W₀+W₁` and full `PW₁`, with uniform bounds and both strong
limits, and construct their canonical retarded operators. Their common-mask
localizations are the SAME retained `Solver` and `Residual`. The lower source-time buffer is proved from the retained support and
inverse-time identity. All hypotheses after the fixed family data are exact
same-witness outputs of `SelectedChartEvolutionAt`; no graph bound, limit,
uncut equation, or blanket elapsed-chart containment is assumed.
Source: `retarded-kernel`, `energy-complete-residual`. -/
theorem exists_selected_supported_graph_regularizations
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (L : ℝ) (hL : 1 ≤ L) (angular : Euclidean d → ℝ)
    (hang : ContDiff ℝ ∞ angular)
    (hplateau : ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L)
      (physicalCoordinates (f.chart p).index ξ) : ℂ)),
      conicMask angular =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ)) :
    let c := f.chart p
    let z : Z := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat)
      (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
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
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L) (physicalCoordinates c.index ξ) : ℂ)
    let Ψ := fun t s y η ↦ G (t, (s, (y, η)))
    let b := directRetardedAmplitudes (fun y i ↦ (coefficient c.index Q y i).map Complex.ofReal)
      (fun y ↦ (zeroth c.index B y).map Complex.ofReal)
      (curryCharacteristicMatrix (W 0)) (curryCharacteristicMatrix (W 1))
    (∀ j : Fin 2, ∀ t s y η, s ≤ z.1-c.maskRadius/2 →
      W (Fin.castLE (by decide) j) (t, (s, (y, η))) = 0) ∧
    ∃ D : Bool → ℝ, ∃ Treg : Bool → ℕ → ℝ → H →L[ℂ] H,
      (∀ k r, r ∈ Icc 0 (3*c.maskRadius/4) →
        ‖elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r‖ ≤ D k) ∧
      (∀ k j r, r ∈ Icc 0 (3*c.maskRadius/4) → ‖Treg k j r‖ ≤ D k) ∧
      (∀ k j r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u : graphTestSpace (d+1) (d+1),
        Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j)
            (elapsedAmplitude (b k) (chartOutputMask f p) (chartInputMask f p) β r)) u) ∧
      (∀ k j r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u : graphTestSpace (d+1) (d+1),
        (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (reverseGraphOperator (elapsedPhase Ψ r)
            (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
              (fun x y ξ ↦ (elapsedAmplitude (b k) (chartOutputMask f p) (chartInputMask f p) β r x y ξ).conjTranspose))
            (fun x ↦ (u.val x).ofLp) y)) ∧
      (∀ k r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u, Tendsto (fun j ↦ Treg k j r u) atTop
        (𝓝 (elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r u))) ∧
      (∀ k r, r ∈ Icc 0 (3*c.maskRadius/4) → ∀ u, Tendsto (fun j ↦ (Treg k j r).adjoint u) atTop
        (𝓝 ((elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r).adjoint u))) ∧
      ∃ Op : Bool → H →L[ℂ] H,
        (∀ k, ‖Op k‖ ≤ (3*c.maskRadius/4) * D k) ∧
        (∀ k u, Op k u = elapsedGraphIntegral (3*c.maskRadius/4) Ψ (b k)
          (chartOutputMask f p) (chartInputMask f p) β u) ∧
        (∀ k u, (Op k).adjoint u = ∫ r in Icc 0 (3*c.maskRadius/4),
          (elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r).adjoint u) ∧
        (∀ k (u : graphTestSpace (d+1) (d+1)), Op k (graphTestToLp u) =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ (b k) (chartOutputMask f p)
            (chartInputMask f p) β (chartPhysicalMasks_properties f p).2.1
            (z.1-c.maskRadius/2) u y)) ∧
        ∀ (k : Bool) (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
          (o : ℕ) (A : ℝ) (As : ℕ → ℝ) (retained : H →L[ℂ] H),
          RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4)
            (z.1-c.maskRadius/2) Ψ (b k) χout χsource β hs o A As retained →
        ∀ (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1),
          tsupport output ⊆ ball x f.physicalRadius →
          (∀ y, (output y : ℂ) * χout ((physicalCoordinates c.index).symm y) = (output y : ℂ)) →
          (∀ y, χsource ((physicalCoordinates c.index).symm y) *
            (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) →
          let e := physicalCoordinates c.index
          let Mo := sourceCutMultiplier (r := d+1) (fun y ↦ output (e y))
            (ho.comp e.continuous) (fun y ↦ hob (e y))
          let Mi := sourceCutMultiplier (r := d+1) (fun y ↦ f.inputMask (e y))
            (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ by
              simpa only [Real.norm_eq_abs, abs_of_nonneg (f.inputMask_range (e y)).1]
                using (f.inputMask_range (e y)).2)
          Mo.comp (Op k) = Mo.comp (retained.comp Mi) := by
  classical
  intro c z Q B h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs hFs W hWs hsupport
    hphysical G hG hGres β Ψ b
  obtain ⟨ho, hs, hoc, hsc, _⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hout, hslab, htime⟩ := selected_output_retained_geometry f p hρb hsrcρ
  have hout' : ∀ y, chartOutputMask f p y ≠ 0 → c.timeMask =ᶠ[𝓝 (y 0)] fun _ ↦ (1 : ℝ) :=
    fun y hy ↦ htime y (subset_tsupport _ hy)
  obtain ⟨aperture, hAp, hcar⟩ := exists_chart_temporal_aperture c hρb hsrcρ
    (f.angularMask p) (f.angularMask_support p)
  have hβsub : tsupport β ⊆ retainedFrequencyDomain c.radialSection z
      (retainedRadius c.targetRadius c.bufferRadius) aperture (1/2) := by
    intro ξ hξ
    have hcan := tsupport_complex_physical_dilatedConicMask_subset (f.angularMask p) c.index
      (zero_lt_one.trans_le hL) hξ
    have hr : ξ ∈ tsupport (dilatedConicMask (f.angularMask p ∘ physicalCoordinates c.index) L) :=
      tsupport_comp_subset Complex.ofReal_zero _ hcan
    refine ⟨dilatedConicMask_tsupport_subset_fullAngularCone c.radialSection z _ _ _ hcar
      (zero_lt_one.trans_le hL) hr, ?_⟩
    have he := (hplateau ξ hξ).eq_of_nhds
    have hn : conicMask angular (spatialPart ξ) ≠ 0 := by rw [he]; norm_num
    have hn' := (conicMask_tsupport_subset angular (subset_tsupport _ hn)).1
    change (1/2 : ℝ) < ‖spatialPart ξ‖
    linarith
  obtain ⟨Rs, hRs⟩ := hsc.exists_bound_of_continuousOn (f := fun y : E ↦ y) continuous_id.continuousOn
  let R := 1 + |z.1| + ‖z.2.1‖ + retainedRadius c.targetRadius c.bufferRadius + |Rs|
  have hε := (retainedRadius_bounds c.targetRadius_pos c.bufferRadius_pos).1
  have hR : 0 < R := by dsimp [R]; positivity
  have hX : ∀ y ∈ elapsedPhysicalBox z (retainedRadius c.targetRadius c.bufferRadius/2), ‖y‖ ≤ R := by
    intro y hy
    have hn := norm_le_on_elapsedPhysicalBox hy
    dsimp [R]
    linarith [abs_nonneg Rs]
  have hY : ∀ y ∈ tsupport (chartInputMask f p), ∀ i : Fin (d+1), |y i| ≤ R := by
    intro y hy i
    have hn := (PiLp.norm_apply_le y i).trans (hRs y hy)
    rw [Real.norm_eq_abs] at hn
    dsimp [R]
    linarith [le_abs_self Rs, abs_nonneg z.1, norm_nonneg z.2.1]
  obtain ⟨D, Treg, hlow, hbound, hreal, hrealAdj, hlim, hlimAdj, Op, hOp, hOpint, hOpadj, hOptest⟩ :=
    exists_retained_collared_graph_regularizations c.radialSection z c.targetRadius_pos
      c.bufferRadius_pos c.maskRadius_pos hρb hsrcρ hAp
      (chartOutputMask f p) (chartInputMask f p) ho hs hoc hsc hout (fun y hy ↦ hslab y (subset_tsupport _ hy)) R hR hX hY
      c.index (f.angularMask p) (f.angularMask_smooth p) hcar L hL hβsub
      (closedBall x RQ) Q c.phaseCost h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime angular hang Fs hFs hWs hsupport
  let V : Bool → TwoTimeAmplitude d (d+1) := fun k ↦ if k then curryCharacteristicMatrix (W 2)
    else curryCharacteristicMatrix (W 0) + curryCharacteristicMatrix (W 1)
  have hpw := retained_residual_eq_twoTimePhysicalApply c.index Q B (W 1) (W 2)
    c.timeMask (hWs 1) hphysical
  have hgraph (k : Bool) (r : ℝ) :
      elapsedGraph Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β r =
        elapsedGraph (curriedPhase c.radialSection C) (V k) (chartOutputMask f p) (chartInputMask f p) β r := by
    cases k
    · exact solver_elapsedGraph_eq_supported c.radialSection C (W 0) (W 1) G hG _ _ _ r
    · calc
        _ = elapsedGraph Ψ (curryCharacteristicMatrix (W 2))
            (chartOutputMask f p) (chartInputMask f p) β r :=
          (retained_elapsedGraph_amplitude_congr Ψ _ _ _ _ _
            (fun y hy s η ↦ hpw y (hout' y hy) s η) r).symm
        _ = _ := residual_elapsedGraph_eq_supported c.radialSection C (W 2) G c.timeMask hGres
          _ _ _ hout' r
  have hkernel (k : Bool) (j : ℕ) (r : ℝ) :
      graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j)
            (elapsedAmplitude (b k) (chartOutputMask f p) (chartInputMask f p) β r)) =
        graphTestOutput (elapsedPhase (curriedPhase c.radialSection C) r)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j)
            (elapsedAmplitude (V k) (chartOutputMask f p) (chartInputMask f p) β r)) ∧
      ∀ u : E → Fin (d+1) → ℂ, reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x y ξ ↦ (elapsedAmplitude (b k) (chartOutputMask f p) (chartInputMask f p) β r x y ξ).conjTranspose)) u =
        reverseGraphOperator (elapsedPhase (curriedPhase c.radialSection C) r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x y ξ ↦ (elapsedAmplitude (V k) (chartOutputMask f p) (chartInputMask f p) β r x y ξ).conjTranspose)) u := by
    cases k
    · exact solver_cut_elapsed_kernels_supported c.radialSection C (W 0) (W 1) G hG _ _ _ _ r
    · exact residual_cut_elapsed_kernels_supported c.radialSection C (W 2) _ G c.timeMask hGres
        _ _ _ _ hout' hpw r
  have htest (k : Bool) (u : graphTestSpace (d+1) (d+1)) (y : E) :
      retardedPhysicalIntegral Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β hs
          (z.1-c.maskRadius/2) u y =
        retardedPhysicalIntegral (curriedPhase c.radialSection C) (V k)
          (chartOutputMask f p) (chartInputMask f p) β hs (z.1-c.maskRadius/2) u y := by
    cases k
    · exact solver_retardedPhysicalIntegral_eq_supported c.radialSection C (W 0) (W 1) G hG
        _ _ _ hs _ u y
    · calc
        _ = retardedPhysicalIntegral Ψ (curryCharacteristicMatrix (W 2))
            (chartOutputMask f p) (chartInputMask f p) β hs (z.1-c.maskRadius/2) u y :=
          (retained_retardedPhysicalIntegral_amplitude_congr Ψ _ _ _ _ _
            (fun x hx s η ↦ hpw x (hout' x hx) s η) hs _ u y).symm
        _ = _ := residual_retardedPhysicalIntegral_eq_supported c.radialSection C (W 2) G
          c.timeMask hGres _ _ _ hout' hs _ u y
  have hcanonical (k : Bool) (u : graphTestSpace (d+1) (d+1)) :
      Op k (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (retardedPhysicalIntegral Ψ (b k) (chartOutputMask f p) (chartInputMask f p) β
          (chartPhysicalMasks_properties f p).2.1 (z.1-c.maskRadius/2) u y) := by
    simp only [htest]
    simpa [V, W, β] using hOptest k u
  refine ⟨?_, D, Treg, ?_, hbound, ?_, ?_, ?_, ?_, Op, hOp, ?_, ?_, hcanonical, ?_⟩
  · intro j t s y η hs'
    exact retained_amplitude_zero_before_source_half c.radialSection z c.maskRadius C
      hsourceTime _ (hsupport _) hs'
  · intro k r hr
    rw [hgraph]
    exact hlow k r hr
  · intro k j r hr u
    rw [(hkernel k j r).1]
    exact hreal k j r hr u
  · intro k j r hr u
    simp only [(hkernel k j r).2]
    exact hrealAdj k j r hr u
  · intro k r hr u
    rw [hgraph]
    exact hlim k r hr u
  · intro k r hr u
    rw [hgraph]
    exact hlimAdj k r hr u
  · intro k u
    simp only [elapsedGraphIntegral, hgraph]
    simpa [elapsedGraphIntegral, V, W, β] using hOpint k u
  · intro k u
    simp only [hgraph]
    simpa [V, W, β] using hOpadj k u
  · intro k χout χsource hs' o A As retained hret output ho' hob hout' hlocalout hlocalin
    exact retained_common_localization_eq_canonical f p Q B _ _ Ψ (b k) β (Op k)
      (hcanonical k) χout χsource hs' o A As retained hret output ho' hob hout' hlocalout hlocalin

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
