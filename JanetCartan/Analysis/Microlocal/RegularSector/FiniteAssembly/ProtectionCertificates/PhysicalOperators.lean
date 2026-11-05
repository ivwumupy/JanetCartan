module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectionCertificates.EvolutionInterface

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction.LocalSolver
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction.SelectedChart

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
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.AmplitudeBounds
open Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LocalSobolev
open Characteristic.RetardedLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
open FiniteEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
variable {Ω : Set (Euclidean (d+1))} {x ξ : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)}

/-- Construct the actual solver evolution and the literal `PW₁` evolution
with the exact physical right multiplier from one selected chart. Only original coefficient smoothness, value range
and one fixed finite coefficient norm remain as varying inputs. In particular
no root, flow, amplitude, phase or operator bound is assumed. The full `B`
term, same supported phase, signed estimates and reversed adjoint triangles
are retained (`retarded-kernel`, `energy-complete-residual`). The additional
endpoint coverage uses the exact radial band of these same constructed
amplitudes. Consumer: `exists_finite_physical_evolution_data_with_diagonal`. -/
theorem exists_selected_chart_physical_operators_with_protection_certificates_on_enlarged_band
    (lc : LocalChart Ω x RQ Aref ξ M)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotection : Characteristic.AlgebraicChart.LocalProtectionCertificate lc
      evolutionTime speedGap rootSize rootCost)
    (hρb : lc.bufferRadius ≤ lc.targetRadius)
    (hsrcρ : lc.maskRadius ≤ lc.bufferRadius/4) (hM : 0 ≤ M)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : tsupport mask ⊆ lc.angularNeighborhood)
    {Ksource Usource : Set E} (hKs : IsCompact Ksource) (hKsne : Ksource.Nonempty)
    (hUs : IsOpen Usource) (hKUs : Ksource ⊆ Usource)
    (bandFloor bandCeiling : ℝ) (hbandFloor : 0 < bandFloor) :
    let β : ℝ → E → ℂ := fun L ζ ↦
      (dilatedConicMask mask (2*L) (physicalCoordinates lc.index ζ) : ℂ)
    let e := coordinateSplit lc.index
        let z : Z := ((e x).1, ((e x).2, (e ξ).2))
        let ℓ := lc.radialSection
        ∃ (angular : Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
          ContDiff ℝ ∞ angular ∧ (∀ η, angular η ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport angular ∧
          tsupport angular ⊆ angularCone ℓ z.2.2
            (retainedRadius lc.targetRadius lc.bufferRadius / 2) ∧
          (∀ η ∈ tsupport angular, 0 < ℓ η) ∧
        ∃ χout χsource : E → ℂ, ∃ _ho : ContDiff ℝ ∞ χout, ∃ hs : ContDiff ℝ ∞ χsource,
          HasCompactSupport χout ∧ HasCompactSupport χsource ∧
          KernelIdentification.timeSpacePoint z.1 z.2.1 ∈ interior {y | χout y = 1} ∧
          Ksource ⊆ interior {y | χsource y = 1} ∧
          tsupport χout ⊆ elapsedPhysicalBox z (retainedRadius lc.targetRadius lc.bufferRadius / 2) ∧
          tsupport χsource ⊆ Usource ∧
          (∀ y ∈ tsupport χout, lc.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1)) ∧

    let e := coordinateSplit lc.index
        let z : Z := ((e x).1, ((e x).2, (e ξ).2))
        let ℓ := lc.radialSection
        ∀ L' ≥ L,
          (∀ ζ ∈ tsupport (β L'),
            conicMask angular =ᶠ[𝓝 (spatialPart ζ)] (fun _ ↦ 1)) ∧
        ∃ ra > (0 : ℝ), ∃ rb > ra,
        ra ≤ bandFloor ∧ bandCeiling ≤ rb ∧
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
  dsimp only
  let e := coordinateSplit lc.index
  let z : Z := ((e x).1, ((e x).2, (e ξ).2))
  obtain ⟨aperture, hAp, hcar⟩ :=
    exists_chart_temporal_aperture lc hρb hsrcρ mask hcarrier
  obtain ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho, hs, hoc, hsc, hop, hsp, hos, hss, hκout, hconstruct⟩ :=
    exists_physical_local_solver_and_residual_with_diagonal_on_enlarged_band lc.radialSection z lc.targetRadius_pos
      lc.bufferRadius_pos lc.maskRadius_pos hρb hsrcρ hAp lc.timeMask lc.timeMask_plateau
      hKs hKsne hUs hKUs lc.index mask hm hcar lc.phaseCost lc.phaseCost_pos M hM bandFloor bandCeiling hbandFloor
  refine ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho, hs, hoc, hsc, hop, hsp, hos, hss, hκout, ?_⟩
  intro L' hLL
  obtain ⟨hplateau, ra, hra, rb, hrab, hfloor, hceiling, hcoverage, hoperators⟩ := hconstruct L' hLL
  obtain ⟨D, hD, hevolution⟩ := (hprotection.2.2.2.2.2.2.2.2.2) angular hang hangpos ra hra rb
  obtain ⟨A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, hop⟩ := hoperators D hD
  obtain ⟨H1, hH1, hlocal⟩ := exists_retained_local_residual_H1_constant d (d+1)
  refine ⟨hplateau, ra, hra, rb, hrab, hfloor, hceiling, hcoverage, D, hD, A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd,
    H1, hH1, ?_⟩
  intro Q hQ hQrange hQlow
  have hQret : cNorm (closedBall x RQ) (retardedCoefficientOrder d) Q ≤ M :=
    (cNorm_mono_order (sectorLowOrder_bounds d).1).trans hQlow
  have hQ10 : cNorm (closedBall x RQ) 10 Q ≤ M :=
    (cNorm_mono_order (retardedCoefficientOrder_bounds (d := d) (Or.inl rfl)).1).trans hQret
  obtain ⟨Φ, C, hrootProtection, hsmoothFlow, hflowSource, hstateSmooth, hprojectionSmooth, hchartSmooth, hflowDeriv, hwholeFlow, hwholeInverse, hrootNorm, hrootLow, hrootProfile, hjoint, hzero, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, hevoB⟩ :=
    hevolution Q hQ hQrange hQ10
  refine ⟨Φ, C, ⟨hrootProtection, hsmoothFlow, hflowSource, hstateSmooth, hprojectionSmooth, hchartSmooth, hflowDeriv, hwholeFlow, hwholeInverse, hrootNorm, hrootLow, hrootProfile, hjoint, hzero⟩, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, ?_⟩
  intro B hB hBlow
  have hBret : cNorm (closedBall x RQ) (retardedCoefficientOrder d) B ≤ M :=
    (cNorm_mono_order (sectorLowOrder_bounds d).1).trans hBlow
  have hB9 : cNorm (closedBall x RQ) 9 B ≤ M :=
    (cNorm_mono_order (retardedCoefficientOrder_bounds (d := d) (Or.inl rfl)).2.1).trans hBret
  obtain ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead, hphysical, hW⟩ := hevoB B hB hB9
  have hoperators := hop lc.row lc.col lc.sourceMask (closedBall x RQ) Q B hQret hBret
    _ Φ C hbuffer hphase hdiff hnear hphaseBudget (fun p hp ↦ (hinv p hp).2.1)
    (fun j ↦ ⟨(hW j).2.2.2.2.1, (hW j).2.2.2.2.2.1, (hW j).2.2.2.2.2.2.2.2⟩)
    hphysical G hG hGres
  obtain ⟨Solver, Residual, hSolver, hResidual, hPW⟩ := hoperators
  refine ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead,
    ⟨Solver, Residual, hSolver, hResidual, hPW, ?_⟩, hphysical, hW⟩
  intro U Vout hU hVout
  obtain ⟨hf, hg⟩ := hlocal (closedBall x RQ) Q B _ _ _ _ _ _ _ hs _ _ Residual
    hResidual U Vout hU hVout
  have hprofile := retarded_gain_one_profile_le (closedBall x RQ) Q B hQlow hBlow
  have hconstant := mul_le_mul_of_nonneg_left hprofile
    (mul_pos hH1 (hBnd 1)).le
  exact ⟨fun f ↦ ⟨(hf f).1, (hf f).2.trans
    (mul_le_mul_of_nonneg_right hconstant (norm_nonneg f))⟩,
    fun g ↦ ⟨(hg g).1, (hg g).2.trans
    (mul_le_mul_of_nonneg_right hconstant (norm_nonneg g))⟩⟩

/-- Forget only the prescribed band comparisons from the actual enlarged
construction, retaining the same protection, amplitudes and physical operators
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_chart_physical_operators_with_protection_certificates
    (lc : LocalChart Ω x RQ Aref ξ M)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotection : Characteristic.AlgebraicChart.LocalProtectionCertificate lc
      evolutionTime speedGap rootSize rootCost)
    (hρb : lc.bufferRadius ≤ lc.targetRadius)
    (hsrcρ : lc.maskRadius ≤ lc.bufferRadius/4) (hM : 0 ≤ M)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : tsupport mask ⊆ lc.angularNeighborhood)
    {Ksource Usource : Set E} (hKs : IsCompact Ksource) (hKsne : Ksource.Nonempty)
    (hUs : IsOpen Usource) (hKUs : Ksource ⊆ Usource) :
    SelectedChartPhysicalEvolutionWithProtection lc evolutionTime speedGap rootSize rootCost mask Ksource Usource := by
  unfold SelectedChartPhysicalEvolutionWithProtection SelectedChartEvolutionForWithProtection
    SelectedChartEvolutionAtWithProtection
  dsimp only
  obtain ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho, hs, hoc, hsc, hop, hsp, hos, hss, hκout, hconstruct⟩ :=
    exists_selected_chart_physical_operators_with_protection_certificates_on_enlarged_band
      lc hprotection hρb hsrcρ hM mask hm hcarrier hKs hKsne hUs hKUs 1 1 zero_lt_one
  refine ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho, hs, hoc, hsc, hop, hsp, hos, hss, hκout, ?_⟩
  intro L' hLL
  obtain ⟨hp, ra, hra, rb, hrab, _, _, hcoverage, hremaining⟩ := hconstruct L' hLL
  exact ⟨hp, ra, hra, rb, hrab, hcoverage, hremaining⟩

end JanetCartan.RegularSector.FinitePdo.RetainedConstruction
