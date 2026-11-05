module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.PhysicalOperators

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction.PhysicalOperators

/-!
# Retained protection certificates for the finite direct construction

The same local root, masks and evolution are retained through this deduction.
Consumer: `exists_finite_direct_operator_bounds_with_protection_certificates`,
then `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo.RetainedConstruction
open ActualCarriers Characteristic Characteristic.ResidualCoordinates
open Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.ConicAmplitude
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open Characteristic.AmplitudeBounds Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral.SymbolBudgets FourierIntegral LocalSobolev
open Characteristic.RetardedLocalization JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Construct one common radial threshold and physical output plateau, and
instantiate the physical retarded theorem on every SAME selected chart.
Every analytic input comes from the original coefficient producer. The
result retains all local identities and all signed integer estimates in
`SelectedChartEvolutionAtWithProtection`; no operator estimate is assumed. The source
plateau contains the original common input support. The angular cover is
unchanged. The already selected `f` is an input; no second family is
chosen. For every `L' ≥ L ≥ f.radialThreshold`, normalized frequency coverage
and the literal amplitudes have the SAME existential radial band. Consumer:
the upper-endpoint PDO and signed integer gains for that selected `W₁`.
Source: `thm:sector`, `energy-complete-residual`. -/
theorem exists_finite_physical_evolution_data_with_protection_certificates_on_enlarged_bands
    (hΩ : IsOpen Ω) (f : ActualMaskFamily Ω x RQ A₀ K M)
    {evolutionTime speedGap rootSize : f.centers → ℝ} {rootCost : f.centers → ℕ → ℝ}
    (hprotection : ∀ p, Characteristic.AlgebraicChart.LocalProtectionCertificate (f.chart p)
      (evolutionTime p) (speedGap p) (rootSize p) (rootCost p))
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hM : 0 ≤ M)
    (bandFloor bandCeiling : f.centers → ℝ) (hbandFloor : ∀ p, 0 < bandFloor p) :
    ∃ L : ℝ, 1 ≤ L ∧ f.radialThreshold ≤ L ∧ f.radialThreshold ≤ 2 * L ∧
    ∃ (angular : f.centers → Euclidean d → ℝ)
      (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        (∀ η, angular p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (angular p) ∧
        tsupport (angular p) ⊆ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius / 2) ∧
        (∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)) ∧
      (∀ p, ContDiff ℝ ∞ (χout p) ∧ HasCompactSupport (χout p) ∧
        HasCompactSupport (χsource p) ∧
        tsupport (χsource p) ⊆ (physicalCoordinates (f.chart p).index) ⁻¹' Ω ∧
        (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
          interior {y | χsource p y = 1} ∧
        (∀ y ∈ tsupport (χout p), (f.chart p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1))) ∧
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p, tsupport output ⊆ (physicalCoordinates (f.chart p).index).symm ⁻¹'
        interior {y | χout p y = 1}) ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) *
        χout p ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ)) ∧
      (∀ ζ : E, (∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ζ +
        FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1) ∧
      ∀ p : f.centers,
        let Aref := A₀
        let lc := f.chart p
        let ξ := p.val.val
        let evolutionTime := evolutionTime p
        let speedGap := speedGap p
        let rootSize := rootSize p
        let rootCost := rootCost p
        let β : ℝ → E → ℂ := fun L' ζ ↦
          (dilatedConicMask (f.angularMask p) (2*L')
            (physicalCoordinates (f.chart p).index ζ) : ℂ)
        let angular := angular p
        let χout := χout p
        let χsource := χsource p
        let hs := hs p

    let e := coordinateSplit lc.index
    let z : Z := ((e x).1, ((e x).2, (e ξ).2))
    let ℓ := lc.radialSection
    ∀ L' ≥ L,
      (∀ ζ ∈ tsupport (β L'),
        conicMask angular =ᶠ[𝓝 (spatialPart ζ)] (fun _ ↦ 1)) ∧
    ∃ ra > (0 : ℝ), ∃ rb > ra,
      ra ≤ bandFloor p ∧ bandCeiling p ≤ rb ∧
      DiagonalFrequencyCoverage ℓ z.2.2 (lc.bufferRadius/2) ra rb (β L') ∧
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
    ∃ A₀ > (0 : ℝ), ∃ A₁ > (0 : ℝ), ∃ A Bnd : ℕ → ℝ,
      (∀ s, 0 < A s) ∧ (∀ s, 0 < Bnd s) ∧
    ∃ H1 > (0 : ℝ),
    ∀ Q : E → Fin (d+1) → Mat, ContDiffOn ℝ ∞ Q Ω →
      MapsTo Q Ω (closedBall Aref lc.coefficientRadius) →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
      let h := fieldRoot e Q lc.root
      let U := fieldDomain e Ω ℓ z.2.2 lc.coefficientRadius
      ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
        SelectedProtectionData lc evolutionTime speedGap rootSize rootCost Q Φ C ∧
        ContDiffOn ℝ ∞ h U ∧
        (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
        closedBall z lc.rootRadius ⊆ U ∧
        (∀ w ∈ closedBall z lc.rootRadius, (rootPencil e Q h w).det = 0 ∧
          lc.minorGap ≤ |(rootPencil e Q h w).adjugate lc.row lc.col| ∧
          lc.transportGap ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) lc.row lc.col|) ∧
        (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) lc.sourceRadius ∧
        ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) lc.targetRadius ⊆ C.target ∧
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
        (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
        (∀ q ∈ C.target,
          (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
          (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
        (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
          (twoTimeState Φ (C.symm q)).1 = q.1) ∧
        (∀ w ∈ ball z lc.sourceRadius, (w.1, w) ∈ C.target ∧
          C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
        (∀ q ∈ closedBall (z.1, z) lc.targetRadius, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
        (∀ m, cNorm (closedBall (z.1, z) lc.targetRadius) m (twoTimePhase C) ≤
          lc.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
        ball (z.1, z) lc.outerRadius ⊆ C.target ∧
        MapsTo C (closedBall (z.1, z) lc.maskRadius) (closedBall (z.1, z) (lc.bufferRadius / 2)) ∧
        ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
          let V := C.target ∩ C.symm ⁻¹' (ball z.1 (lc.maskRadius / 2) ×ˢ
            (ball z.1 (lc.maskRadius / 2) ×ˢ ball z.2 (lc.maskRadius / 2)))
          let Fs := fun j ↦ bufferedMatrix V lc.timeMask (pencilAmplitudeFamily lc.index Q B h Φ C lc.row lc.col lc.sourceMask j)
          let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
          let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
          ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
            (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
            (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
              tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
            (∀ p : T, lc.timeMask =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
              collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
            (∀ y : E, lc.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
              WKB.firstOrderApply
                (fun x idx ↦ ((coefficient lc.index Q x idx).map Complex.ofReal).mulVecLin)
                (fun x ↦ ((zeroth lc.index B x).map Complex.ofReal).mulVecLin)
                (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                  (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                  (fun k ↦ twoTimePhysicalApply (fun x idx ↦ (coefficient lc.index Q x idx).map Complex.ofReal)
                    (fun x ↦ (zeroth lc.index B x).map Complex.ofReal) W₁
                      (y 0) s (spatialPart y) η k j)) ∧
            (∀ y : E, lc.timeMask (y 0) = 1 → ∀ η,
              (coefficient lc.index Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                conicSourceSymbol ℓ (FiniteMasks.conicMask angular) lc.sourceMask y η •
                  projector lc.index Q h lc.row lc.col y ((ℓ η)⁻¹ • η)) ∧
          (∃ Solver Residual : SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
            RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*lc.maskRadius/4)
              (z.1-lc.maskRadius/2) (fun t s y η ↦ G (t, (s, (y, η))))
              (W₀ + W₁) χout χsource
              (β L')
              hs 0 A₀ A Solver ∧
            RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*lc.maskRadius/4)
              (z.1-lc.maskRadius/2) (fun t s y η ↦ G (t, (s, (y, η))))
              (curryCharacteristicMatrix (collared ℓ 1 angular (Fs 2))) χout χsource
              (β L')
              hs 1 A₁ Bnd Residual ∧
            RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*lc.maskRadius/4)
              (z.1-lc.maskRadius/2) (fun t s y η ↦ G (t, (s, (y, η))))
              (twoTimePhysicalApply (fun y idx ↦ (coefficient lc.index Q y idx).map Complex.ofReal)
                (fun y ↦ (zeroth lc.index B y).map Complex.ofReal) W₁)
              χout χsource
              (β L')
              hs 1 A₁ Bnd Residual ∧
            ∀ (U Vout : Set E) (hU : MeasurableSet U), MeasurableSet Vout →
              (∀ f : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
                MemRestrictionSobolev Vout 1 (localRetardedOperator hU Vout Residual f) ∧
                restrictionSobolevNorm Vout 1 (localRetardedOperator hU Vout Residual f) ≤
                  (H1 * Bnd 1 * (2 + 2 * M)) * ‖f‖) ∧
              (∀ g : LocalL2 Vout (EuclideanSpace ℂ (Fin (d+1))),
                MemRestrictionSobolev U 1 ((localRetardedOperator hU Vout Residual).adjoint g) ∧
                restrictionSobolevNorm U 1 ((localRetardedOperator hU Vout Residual).adjoint g) ≤
                  (H1 * Bnd 1 * (2 + 2 * M)) * ‖g‖)) ∧
          (∀ q : T, lc.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
            (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
              WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                (fun y k ↦ collared ℓ 1 angular (Fs 1)
                  (physicalSlice e q.2.1 q.2.2.2 y) k j)
                (e.symm (q.1, q.2.2.1))) ∧
          ∀ j : Fin 3,
            let f := pencilAmplitudeFamily lc.index Q B h Φ C lc.row lc.col lc.sourceMask j
            let F := bufferedMatrix V lc.timeMask f
            let o := if j = 0 then 0 else 1
            let W := collared ℓ o angular F
            ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
            tsupport F ⊆ closedBall (z.1, z) (lc.bufferRadius / 2) ∧ ContDiff ℝ ∞ W ∧
            tsupport W ⊆ ConicPhase.domain ℓ V ∧
            (∀ q : T, q.2.1 ≤ z.1 - lc.maskRadius → W q = 0) ∧
            (∀ q ∈ V, lc.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
            ∀ m,
              BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (lc.bufferRadius / 2) ra rb) m
                (curryCharacteristicMatrix W) ∧
              twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (lc.bufferRadius / 2) ra rb) m
                (curryCharacteristicMatrix W) ≤
                D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                  cNorm (closedBall x RQ) (m + 9) B) := by
  classical
  have hinput : x ∈ tsupport f.inputMask := by
    apply subset_tsupport f.inputMask
    have he := interior_subset
      (f.inputMask_plateau (mem_closedBall_self
        (mul_nonneg (by norm_num) f.physicalRadius_pos.le)))
    change f.inputMask x = 1 at he
    change f.inputMask x ≠ 0
    rw [he]
    exact one_ne_zero
  have hp (p : f.centers) :=
    exists_selected_chart_physical_operators_with_protection_certificates_on_enlarged_band
      (f.chart p) (hprotection p) (hradii p).1 (hradii p).2 hM
      (f.angularMask p) (f.angularMask_smooth p) (f.angularMask_support p)
      (f.inputMask_compact.image (physicalCoordinates (f.chart p).index).symm.continuous)
      ⟨(physicalCoordinates (f.chart p).index).symm x, x, hinput, rfl⟩
      (hΩ.preimage (physicalCoordinates (f.chart p).index).continuous)
      (selected_input_carrier_subset_domain f p)
      (bandFloor p) (bandCeiling p) (hbandFloor p)
  dsimp only at hp
  choose angular localL hL ha har hac has hap χout χsource ho hs hoc hsc hop hsp
    hos hss hκ hconstruct using hp
  let L := f.radialThreshold + ∑ p, localL p
  have hsum : 0 ≤ ∑ p, localL p := Finset.sum_nonneg fun p _ ↦ (zero_le_one.trans (hL p))
  have hLf : f.radialThreshold ≤ L := le_add_of_nonneg_right hsum
  have hLone : 1 ≤ L := f.radialThreshold_ge_one.trans hLf
  have hlocal (p : f.centers) : localL p ≤ L := by
    exact (Finset.single_le_sum (fun q _ ↦ zero_le_one.trans (hL q))
      (Finset.mem_univ p)).trans (le_add_of_nonneg_left
        (zero_le_one.trans f.radialThreshold_ge_one))
  let V : Set E := ball x f.physicalRadius ∩ ⋂ p : f.centers,
    (physicalCoordinates (f.chart p).index).symm ⁻¹' interior {y | χout p y = 1}
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_iInter_of_finite fun p ↦ isOpen_interior.preimage
      (physicalCoordinates (f.chart p).index).symm.continuous)
  have hx : x ∈ V := ⟨mem_ball_self f.physicalRadius_pos, mem_iInter.mpr fun p ↦ by
    simpa only [mem_preimage, physicalCoordinates_symm_center] using hop p⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨output, hout, hrange, hcompact, hsupport, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff (isCompact_closedBall x (r/2))
      isOpen_ball (closedBall_subset_ball (by linarith : r/2 < r))
  have hsupportV : tsupport output ⊆ V := hsupport.trans hrV
  refine ⟨L, hLone, hLf, by linarith, angular, χout, χsource, hs,
    fun p ↦ ⟨ha p, har p, hac p, has p, hap p⟩,
    fun p ↦ ⟨ho p, hoc p, hsc p, hss p, hsp p, hκ p⟩,
    output, r/2, by positivity, hout, hrange, hcompact,
    fun y hy ↦ (hsupportV hy).1, hplateau,
    fun p y hy ↦ mem_iInter.mp (hsupportV hy).2 p, ?_, ?_, ?_, ?_⟩
  · intro p y
    by_cases hy : f.inputMask y = 0
    · simp only [hy, Complex.ofReal_zero, mul_zero]
    · have he := interior_subset (hsp p ⟨y, subset_tsupport f.inputMask hy, rfl⟩)
      change χsource p ((physicalCoordinates (f.chart p).index).symm y) = 1 at he
      rw [he, one_mul]
  · intro p y
    by_cases hy : output y = 0
    · simp only [hy, Complex.ofReal_zero, zero_mul]
    · have he := interior_subset (mem_iInter.mp (hsupportV (subset_tsupport output hy)).2 p)
      change χout p ((physicalCoordinates (f.chart p).index).symm y) = 1 at he
      rw [he, mul_one]
  · exact dilatedConicMask_complete_partition f.angularMask (2*L)
  · intro p
    dsimp only
    intro L' hLL
    exact hconstruct p L' ((hlocal p).trans hLL)

/-- Project the original finite-family conclusion from the enlarged-band
construction on the same witnesses (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_finite_physical_evolution_data_with_protection_certificates
    (hΩ : IsOpen Ω) (f : ActualMaskFamily Ω x RQ A₀ K M)
    {evolutionTime speedGap rootSize : f.centers → ℝ} {rootCost : f.centers → ℕ → ℝ}
    (hprotection : ∀ p, Characteristic.AlgebraicChart.LocalProtectionCertificate (f.chart p)
      (evolutionTime p) (speedGap p) (rootSize p) (rootCost p))
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hM : 0 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ f.radialThreshold ≤ L ∧ f.radialThreshold ≤ 2 * L ∧
    ∃ (angular : f.centers → Euclidean d → ℝ)
      (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        (∀ η, angular p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (angular p) ∧
        tsupport (angular p) ⊆ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius / 2) ∧
        (∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)) ∧
      (∀ p, ContDiff ℝ ∞ (χout p) ∧ HasCompactSupport (χout p) ∧
        HasCompactSupport (χsource p) ∧
        tsupport (χsource p) ⊆ (physicalCoordinates (f.chart p).index) ⁻¹' Ω ∧
        (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
          interior {y | χsource p y = 1} ∧
        (∀ y ∈ tsupport (χout p), (f.chart p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1))) ∧
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p, tsupport output ⊆ (physicalCoordinates (f.chart p).index).symm ⁻¹'
        interior {y | χout p y = 1}) ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) *
        χout p ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ)) ∧
      (∀ ζ : E, (∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ζ +
        FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1) ∧
      ∀ p : f.centers, SelectedChartEvolutionAtWithProtection (f.chart p)
        (evolutionTime p) (speedGap p) (rootSize p) (rootCost p)
        (fun L' ζ ↦ (dilatedConicMask (f.angularMask p) (2*L')
          (physicalCoordinates (f.chart p).index ζ) : ℂ))
        L (angular p) (χout p) (χsource p) (hs p) := by
  obtain ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, hevolution⟩ :=
    exists_finite_physical_evolution_data_with_protection_certificates_on_enlarged_bands
      hΩ f hprotection hradii hM (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
  refine ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, ?_⟩
  intro p L' hLL
  obtain ⟨hp, ra, hra, rb, hrab, _, _, hcoverage, hremaining⟩ := hevolution p L' hLL
  exact ⟨hp, ra, hra, rb, hrab, hcoverage, hremaining⟩

end JanetCartan.RegularSector.FinitePdo.RetainedConstruction
