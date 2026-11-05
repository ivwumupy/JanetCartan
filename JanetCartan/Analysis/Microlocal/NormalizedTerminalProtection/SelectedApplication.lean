module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.CommonMask
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.SelectedApplication

/-!
# Terminal protection on the original selected radial family

Apply the original selected root/flow certificates and finite radial chart
producer to the terminal carrier and prescribed-mask constructions. The same
witnesses carry the original canonical and conic interior/boundary phase gaps.
The final normalized-source mask is chosen before the phase band, radial proof
refinement and current coefficient field; no solver or finite family is reselected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius NNReal ENNReal

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open SelectedSectorProtection SelectedEvenProofMasks
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.UniformAmplitudes
open RegularSector.FiniteAssembly RegularSector.FiniteEvolution RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.EvolutionIntegral RegularSector.NormalizedSolver
open ProtectedMasks ProtectedMasks.ConicInterior ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
open RegularSector.Characteristic.RetardedLocalization LocalSobolev FourierIntegral LowBounds

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "L2C" => Lp CV 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The retained selected family supplies its literal radial roots, flows,
source/endpoint masks and complete elapsed interval to the reflected terminal
construction. One carrier contains every finite word depth, including the source
and elliptic diagonals. One final mask has the normalized-source estimates and
contains the closed shoulders of these same even proof masks. All original
canonical and conic phase gaps are proved on those witnesses; the physical
annulus precedes the phase band and radial refinement. Producers are
`selected_root_mask_primitives`, `exists_finite_radial_chart_buffers`, and the
retained comparison outputs of initialized signed no-return
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_selected_terminal_even_proof_masks_of_coefficient_bound
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hΩ : IsOpen Ω)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ωsource : Set E} (hKcone : IsCompact K) (hKsym : ∀ ξ ∈ K, -ξ ∈ K)
    {r Mglobal c C Lx ε : ℝ}
    (hr : 0 < r) (hMglobal : 0 ≤ Mglobal) (hcgraph : 0 < c) (hCgraph : 0 < C)
    (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hphysical : closedBall x RQ ⊆ ball 0 (2*r))
    (hΩΓ : Ωsource ⊆ interior K)
    (hΩsym : ∀ ξ ∈ Ωsource, -ξ ∈ Ωsource)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball x f.physicalRadius)
    (hχ₂source : tsupport χ₂ ⊆ ball 0 r)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ interior Ωsource)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (hreflectV : physicalCovectorReflection '' (tsupport χ₂ ×ˢ Ksource) ⊆ V)
    (output : E → ℝ) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let γ := fun p : J ↦ (f.chart p).maskRadius
    EqOn f.inputMask 1 (tsupport χ₂) ∧
    ∃ aCarrier > (0 : ℝ), ∃ bCarrier > aCarrier, ∃ εterminal > (0 : ℝ),
    ∃ (mi : LocalizerSymbol (d+1)) (δfinal a b Rbase : ℝ) (Djet : ℕ → ℝ)
      (Mterminal : {ρ : ℝ // 1 ≤ ρ} → L2C →L[ℂ] L2C),
      IsBufferedLocalizer mi
        (protectedAnnularCarrier (cthickening 1 (closedBall x RQ))
          aCarrier bCarrier εterminal K) (physicalProtectedRegion K) ∧
      0 < δfinal ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧
      tsupport mi ⊆ closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b ∧
      (∀ k, 0 ≤ Djet k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Djet k) ∧
      (∀ ρ u, Mterminal ρ u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ.1 mi (fun z ↦ (u z).ofLp) y)) ∧
      (∀ (L₀ : ℝ), f.radialThreshold ≤ L₀ →
      ∀ (ho : ContDiff ℝ ∞ output) (_hoc : HasCompactSupport output)
        (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
        (χ₃ : ContDiffBump x) (U : Set E), IsOpen U →
        tsupport (χ₃ : E → ℝ) ⊆ U → U ⊆ ball x f.physicalRadius →
        (∀ y ∈ U, output y = 1) →
      ∃ C Cr : ℕ → ℕ → ℝ, (∀ s q, 0 ≤ C s q) ∧ (∀ s q, 0 ≤ Cr s q) ∧
        ∀ (ρ : {ρ : ℝ // 1 ≤ ρ}) (L : ℝ), 1 ≤ L → L ≤ ρ.1 →
        ∀ χ₂ : ContDiffBump x, (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) →
        ∀ (s q : ℕ) (D : Set E) (hD : MeasurableSet D)
          (W : Set E) (hW : MeasurableSet W) (u : LocalL2 D CV) (backward : Bool),
          let w := SmallSupport.zeroExtend hD (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)
          let S := pairedSource f hKcone L₀ output ho.continuous
            (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
          let P := if backward then S.adjoint else S
          let v := restrictL2 W ((P-1) (Mterminal ρ w))
          (v ∈ (restrictionSobolevScale W CV hW).level s ∧
            (restrictionSobolevScale W CV hW).gradeNorm s v ≤
              C s q * ρ.1^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ.1)^q * ‖u‖) ∧
          ∀ c : ℂ, ‖c‖ = 1 →
            let vr := l2RealPart (volume.restrict W) (c • v)
            vr ∈ (restrictionSobolevScale W RV hW).level s ∧
            (restrictionSobolevScale W RV hW).gradeNorm s vr ≤
              Cr s q * ρ.1^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ.1)^q * ‖u‖) ∧
    ∀ (N : ℕ) (aPhase bPhase : J → ℝ), (∀ p, 0 < aPhase p) →
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2*r)) 3 Q ≤ Mglobal →
      let h := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) Ω (ℓ p)
        (z p).2.2 (εroot p)
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP),
        (∀ p, SelectedProtectionData (f.chart p) (T p) (speed p) (G p) (rootCost p)
          Q (Φ p) (Cphase p)) →
        (∀ p, ContDiffOn ℝ ∞ (h p) (D p)) →
        (∀ p w, w ∈ D p → ∀ t : ℝ, 0 < t →
          h p (w.1, (w.2.1, t • w.2.2)) = t * h p w) →
        (∀ p, (Cphase p : TP → TP) = twoTimeProjection (Φ p)) →
        (∀ p, (Cphase p).source = ball ((z p).1, z p) (f.chart p).sourceRadius) →
        (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cphase p).target) →
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cphase p)) (Cphase p).target) →
        (∀ p q, q ∈ (Cphase p).target → HasFDerivAt (twoTimePhase (Cphase p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cphase p) q) q) →
        (∀ p w, w ∈ ball (z p) (f.chart p).sourceRadius →
          twoTimePhase (Cphase p) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ K) →
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z : J → Z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let W := closedBall x RQ
    let S := tsupport χ₂ ×ˢ Ksource
    let Δ := 6 * f.physicalRadius
    let h : J → Z → ℝ := fun p ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
    let irad : ((j : J) × Fin (n j)) → Fin (d+1) := fun k ↦ i k.1
    let hrad : ((j : J) × Fin (n j)) → Z → ℝ := fun k ↦ h k.1
    let Φrad : ((j : J) × Fin (n j)) → Z × ℝ → Z := fun k ↦
      radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
    let Ur : ((j : J) × Fin (n j)) → Set Z := fun k ↦ Urad k.1 k.2
    let Kr : ((j : J) × Fin (n j)) → Set Z := fun k ↦
      rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' ''
        closedBall (z k.1) (f.chart k.1).rootRadius
    let Ractual : (E × E) → (E × E) → Prop := physicalDirectRelation irad hrad Φrad Ur Kr W
      (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output) Δ
    let Runit : (E × E) → (E × E) → Prop := physicalDirectRelation irad hrad Φrad Ur Kr W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
    (∀ depth, reachableAt (reflectedProofRelation Ractual)
      (physicalSymmetricHull S) depth ⊆
        protectedAnnularCarrier (cthickening 1 W) aCarrier bCarrier εterminal K) ∧
    ∃ (Gext : J → TwoTimePoint (Euclidean d) → ℝ)
      (m : Fin (N + 1) → LocalizerSymbol (d + 1)),
      (∀ k y ξ, m k (y, -ξ) = m k (y, ξ)) ∧
      (∀ j, Continuous (Gext j) ∧ ContDiffOn ℝ ∞ (Gext j) {q | q.2.2.2 ≠ 0} ∧
        (∀ (q : TwoTimePoint (Euclidean d)) (s : ℝ), 0 < s →
          Gext j (q.1, (q.2.1, (q.2.2.1, s • q.2.2.2))) = s * Gext j q) ∧
        ∀ q ∈ ConicPhase.domain (ℓ j) (closedBall ((z j).1, z j) (2 * (f.chart j).maskRadius)),
          Gext j =ᶠ[𝓝 q] ConicPhase.phase (ℓ j) (Cphase j)) ∧
      (∀ k, IsBufferedLocalizer (m k)
        (reachableAt Ractual S k.val)
        (physicalProtectedRegion K)) ∧
      IsBufferedLocalizer (m 0) S V ∧
      cthickening θ (tsupport (m 0)) ⊆ V ∧
      (∀ k, cthickening θ (reachableAt
        Ractual S k.val) ⊆
          interior {p | m k p = 1}) ∧
      (∀ k, cthickening θ (tsupport (m k)) ⊆
        (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
          physicalProtectedRegion K) ∧
      (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
      (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
        p = q ∨ Ractual p q →
          closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
      (∀ k j, IsBufferedLocalizer
        (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
        (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
          Ractual S k.val)
        (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion K)) ∧
      (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
        closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
      (∀ k j l p, ‖iteratedFDeriv ℝ l
        (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
      (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
        p = q ∨ Runit p q →
            closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
      (∀ (k : Fin N) (χ₂ χ₃ : Euclidean (d + 1) → ℝ),
        EqOn χ₃ 1 (tsupport χ₂) →
        ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
          sourceRecutRelation χ₂ Ractual p q →
            χ₃ p.1 = 1 ∧ closedBall q θ ⊆ interior {q | m k.succ q = 1}) ∧
      (∀ k, cthickening θ (tsupport (m k)) ⊆ interior {p | mi p = 1}) ∧
      (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
        p = q ∨ reflectedProofRelation Runit p q →
          closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
      ∀ (k : Fin N) (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
      ∀ (x y : Euclidean (d + 1)) (r' : ℝ) (p : JointVariables (Euclidean (d + 1))),
        r' ∈ Icc 0 Δ → r' ≤ (f.chart j).maskRadius →
        p.1.1 0 ∈ closedBall (z j).1 ((f.chart j).maskRadius / 2) →
        spatialPart p.1.1 ∈ closedBall (z j).2.1 ((f.chart j).maskRadius / 2) →
        spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2
          ((f.chart j).maskRadius / 2) (aPhase j) (bPhase j) →
        (y, p.2.2.1) ∈ cthickening (θ / 2)
          (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc))) →
        (x, p.2.2.2) ∈ tsupport
          (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q) →
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
            (SymbolBudgets.normalizedTwoTimePhase Rf
              (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y (r', w)) p)) ∧
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
            (SymbolBudgets.normalizedTwoTimePhase Rf
              (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y) (r', p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
            (SymbolBudgets.normalizedTwoTimePhase Rf
              (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (r', w)) p) ∧
        fderiv ℝ (jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ≠ 0 ∧
        fderiv ℝ (fun w ↦ jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y (0, w)) p ≠ 0 ∧
        fderiv ℝ (jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y) (r', p) ≠ 0 ∧
        fderiv ℝ (fun w ↦ jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (0, w)) p ≠ 0 := by
  classical
  intro J i ℓ z εroot γ
  let ρ := fun p : J ↦ (f.chart p).rootRadius / 3
  let W := closedBall x RQ
  let S := tsupport χ₂ ×ˢ Ksource
  let Δ := 6 * f.physicalRadius
  refine ⟨selected_source_recut_plateau f χ₂ hχ₂support, ?_⟩
  have hσr (j : J) : (f.chart j).sourceRadius < (f.chart j).rootRadius / 2 := by
    have hsmall := (hc j).2.2.2.2.1
    have hpos := (f.chart j).rootRadius_pos
    linarith
  have hσR (j : J) : (f.chart j).sourceRadius ≤ (f.chart j).rootRadius :=
    (hσr j).le.trans (by linarith [(f.chart j).rootRadius_pos])
  let Splus := physicalSymmetricHull S
  have hS : IsCompact S := hχ₂.isCompact.prod hKsource
  have hSplus : IsCompact Splus := isCompact_physicalSymmetricHull hS
  have hSVplus : Splus ⊆ V := union_subset hSV hreflectV
  have hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ωsource :=
    fun p hp ↦ ⟨hχ₂source hp.1, hsourceFrequency p.2 hp.2⟩
  have hSB : ∀ p ∈ S, p.1 ∈ W := by
    intro p hp
    apply f.physicalBall_coefficientDomain
    exact ball_subset_closedBall ((ball_subset_ball (by linarith [f.physicalRadius_pos]))
      (hχ₂support hp.1))
  have hSBplus : ∀ p ∈ Splus, p.1 ∈ W := by
    rintro p (hp | ⟨q, hq, rfl⟩)
    · exact hSB p hp
    · exact hSB q hq
  obtain ⟨κ, hκ, hκspeed⟩ := exists_selected_common_root_speed f T speed G rootCost hc
  have hΔ : 0 ≤ Δ := mul_nonneg (by norm_num) f.physicalRadius_pos.le
  obtain ⟨a₁, ha₁, b₁, hab₁, ε₁, hε₁, hcarrier⟩ :=
    exists_uniform_reflected_terminal_carrier hSplus hr hcgraph hCgraph hε hSBplus hphysical
      (fun p hp ↦ let hs := physicalSymmetricHull_source_geometry hΩsym hsource p hp
        ⟨hs.1, hs.2.1, interior_subset hs.2.2⟩) hΩΓ
  obtain ⟨a₂, ha₂, b₂, hab₂, ε₂, hε₂, hselect⟩ :=
    exists_uniform_reflected_prescribed_terminal_shoulders hSplus (isCompact_closedBall x RQ)
      hr hcgraph hCgraph hε hSBplus hphysical
      (physicalSymmetricHull_source_geometry hΩsym hsource) hΩΓ hV hSVplus
  let aCarrier := min a₁ a₂
  let bCarrier := max b₁ b₂
  let εterminal := min ε₁ ε₂
  have haCarrier : 0 < aCarrier := lt_min ha₁ ha₂
  have habCarrier : aCarrier < bCarrier :=
    (min_le_left _ _).trans_lt (hab₁.trans_le (le_max_left _ _))
  have hεterminal : 0 < εterminal := lt_min hε₁ hε₂
  have hE₁ : protectedAnnularCarrier W a₁ b₁ ε₁ K ⊆
      protectedAnnularCarrier (cthickening 1 W) aCarrier bCarrier εterminal K := by
    intro p hp
    exact ⟨⟨self_subset_cthickening _ hp.1.1, (min_le_left _ _).trans hp.1.2.1,
      hp.1.2.2.trans (le_max_left _ _)⟩,
      (closedBall_subset_closedBall (min_le_left _ _)).trans hp.2⟩
  have hE₂ : protectedAnnularCarrier (cthickening 1 W) a₂ b₂ ε₂ K ⊆
      protectedAnnularCarrier (cthickening 1 W) aCarrier bCarrier εterminal K := by
    intro p hp
    exact ⟨⟨hp.1.1, (min_le_right _ _).trans hp.1.2.1,
      hp.1.2.2.trans (le_max_right _ _)⟩,
      (closedBall_subset_closedBall (min_le_right _ _)).trans hp.2⟩
  obtain ⟨mi, δfinal, a, b, Rbase, Djet, Mterminal, hmterminal, hδfinal,
    ha, hab, hRbase, hmisupp, hDjet, hmijet, hmiplateau, hright, hsourceBound⟩ :=
    SignedProductEstimates.exists_common_normalizedSource_terminal_localizer
      (b := bCarrier) (isCompact_closedBall x RQ).cthickening hKcone hKsym haCarrier hεterminal
  refine ⟨aCarrier, haCarrier, bCarrier, habCarrier, εterminal, hεterminal,
    mi, δfinal, a, b, Rbase, Djet, Mterminal, hmterminal, hδfinal, ha, hab, hRbase,
    hmisupp, hDjet, hmijet, hright, ?_, ?_⟩
  · intro L₀ hL₀ ho hoc hor χ₃ U hU hχ₃ hcore houtput
    exact hsourceBound f L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput
  intro N aPhase bPhase haPhase
  choose n cRad hcRad zj rj Rj Urad hgeom hradcover using fun j : J ↦
    exists_finite_radial_chart_buffers (ℓ j) (z j) (f.chart j).maskRadius_pos
      (haPhase j) (b := bPhase j) (f.chart j).sourceRadius_pos.le (hσr j) (hσR j)
  let Jrad := (j : J) × Fin (n j)
  obtain ⟨δproof, hδproof, hconstruct⟩ := hselect mi δfinal hδfinal
      ((cthickening_subset_of_subset _ hE₂).trans (hmiplateau _ Subset.rfl)) N
      (fun k : Jrad ↦ (cRad k.1 k.2)⁻¹ • ℓ k.1)
      (fun k : Jrad ↦ cRad k.1 k.2 • (z k.1).2.2)
      (fun k : Jrad ↦ cRad k.1 k.2 * εroot k.1)
      (fun k : Jrad ↦ cRad k.1 k.2 * G k.1)
      (fun k ↦ mul_nonneg (hcRad k.1 k.2).le (hc k.1).2.2.1.le)
      hMglobal hLx hκ hΔ
  obtain ⟨H, hH, hcut⟩ :=
    exists_uniform_even_masks_inside_prescribed_terminal mi hmterminal.compactSupport hδproof N
  let θ := δproof / 8
  have hθ : 0 < θ := by positivity
  obtain ⟨δI, hδI, hgapI⟩ := exists_uniform_conic_interior_phaseGradientSquare_gap hθ eI
    n ℓ z γ (fun j ↦ (f.chart j).sourceRadius) (fun j ↦ (f.chart j).rootRadius)
    aPhase bPhase cRad hcRad Urad (fun j ↦ (f.chart j).maskRadius_pos) haPhase hσR hradcover
  obtain ⟨εcollar, δT, χ, Hcollar, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hgapT⟩ := exists_uniform_finiteFamily_rootFlow_collar_of_diagonal
      eT ℓ z (fun _ ↦ x) (fun _ ↦ RQ) ρ T (fun j ↦ (f.chart j).sourceRadius)
      (fun j ↦ (f.chart j).targetRadius / 2) γ (fun j ↦ (f.chart j).phaseCost 2)
      aPhase bPhase hθ hMglobal (fun j ↦ (f.chart j).maskRadius_pos)
      (fun j ↦ (selected_mask_radius_protection_bounds f hradii j).2.1)
      (fun j ↦ (f.chart j).maskRadius_lt_sourceRadius.le)
      (fun j ↦ (f.chart j).phaseCost_pos 2 |>.le) haPhase (Δ := Δ)
  refine ⟨n, cRad, hcRad, Urad, θ, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, ?_⟩
  intro Q hQ hQM h D Φ Cphase hd hh hhom hCphase hCsource htarget hsmooth hdiff hdiag
    I g charts hgr hderiv hnorm hcover hbuffer
  have hroot j := selected_root_mask_primitives f j (hc j) Q (Φ j) (Cphase j) (hd j)
  have hD j : IsOpen (D j) := isOpen_fieldDomain _ hΩ _ _ _
  have hradial j := fieldRoot_maskAssembly_radial_invariance _ _ _ _ _ Q _ (hhom j)
  let irad : Jrad → Fin (d+1) := fun k ↦ i k.1
  let hrad : Jrad → Z → ℝ := fun k ↦ h k.1
  let Φrad : Jrad → Z × ℝ → Z :=
    fun k ↦ radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
  let Ur : Jrad → Set Z := fun k ↦ Urad k.1 k.2
  let Kr : Jrad → Set Z := fun k ↦ rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' ''
    closedBall (z k.1) (f.chart k.1).rootRadius
  have hUK (k : Jrad) : Ur k ⊆ Kr k := (hgeom k.1 k.2).2.2.2.2.2.2.1
  have hKrD (k : Jrad) : Kr k ⊆ D k.1 :=
    radial_image_subset_fieldDomain _ (hcRad k.1 k.2) (hroot k.1).1
  have hprad (k : Jrad) : ∀ v ∈ Ur k ∪ Kr k,
      v.2.2 ∈ closedBall (cRad k.1 k.2 • (z k.1).2.2) (cRad k.1 k.2 * εroot k.1) ∧
      (1 / 2 : ℝ) ≤ ((cRad k.1 k.2)⁻¹ • ℓ k.1) v.2.2 ∧
      |hrad k v| ≤ ((cRad k.1 k.2)⁻¹ • ℓ k.1) v.2.2 * (cRad k.1 k.2 * G k.1) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (union_subset (hUK k) Subset.rfl) hv
    obtain ⟨hfreq, hsection, hvalue⟩ := (hroot k.1).2.2.1 w hw
    refine ⟨radial_frequency_mem_closedBall (hcRad k.1 k.2) hfreq, ?_, ?_⟩
    · simpa only [radial_section_apply] using hsection
    · rw [radial_section_apply]
      change |h k.1 (rootRadialEquiv _ _ w)| ≤ _
      rw [rootRadialEquiv_apply, hhom k.1 w ((hroot k.1).1 hw) _ (hcRad k.1 k.2),
        abs_mul, abs_of_pos (hcRad k.1 k.2)]
      exact (mul_le_mul_of_nonneg_left hvalue (hcRad k.1 k.2).le).trans_eq (by ring)
  have hbrad (k : Jrad) : ∀ v ∈ Ur k ∪ Kr k,
      (coordinateSplit (irad k)).symm (v.1, v.2.1) ∈ W := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (union_subset (hUK k) Subset.rfl) hv
    exact (hroot k.1).2.2.2.1 w hw
  have hfrad (k : Jrad) : ODE.IsSmoothFlowOn (rootHamiltonField (hrad k))
      (zj k.1 k.2) (Rj k.1 k.2) (rj k.1 k.2) (T k.1) (Φrad k) := by
    obtain ⟨_, _, _, _, _, _, _, hclosed, hopen, hrange⟩ := hgeom k.1 k.2
    exact isSmoothFlowOn_radialFlow (hD k.1) (hh k.1) (hradial k.1) (hcRad k.1 k.2)
      (hd k.1).2.1 (hroot k.1).1 hclosed hopen hrange
  let Ractual := physicalDirectRelation irad hrad Φrad Ur Kr W
    (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output) Δ
  let Runit := physicalDirectRelation irad hrad Φrad Ur Kr W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
  have hRunit : IsCompact {pq : (E × E) × (E × E) | Runit pq.1 pq.2} := by
    apply isCompact_physicalDirectRelation irad hrad Φrad Ur Kr (fun k ↦ D k.1) W
      (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
      (fun k ↦ (hgeom k.1 k.2).2.2.2.1)
      (fun _ ↦ (isCompact_closedBall _ _).image (rootRadialEquiv _ _).continuous)
      isClosed_closedBall (fun k ↦ (hUK k).trans (hKrD k)) hKrD
      (fun k ↦ (hh k.1).continuousOn)
    intro k
    apply (hfrad k).continuous.mono
    intro v hv
    refine ⟨(hgeom k.1 k.2).2.2.2.2.1 hv.1, ?_⟩
    have ht := (selected_common_elapsed_lt_evolutionTime f k.1 (hc k.1)).2.2
    exact ⟨by linarith [hv.2.1], hv.2.2.trans ht.le⟩
  have hprop := (hconstruct δproof hδproof.le le_rfl).2 Q hQ hQM
      irad hrad Φrad Ur Kr (fun k ↦ D k.1) W (fun _ _ ↦ 1) (fun _ _ ↦ 1)
      (fun k ↦ (hgeom k.1 k.2).2.2.2.1)
      (fun _ ↦ (isCompact_closedBall _ _).image (rootRadialEquiv _ _).continuous)
      isClosed_closedBall (fun k ↦ (hUK k).trans (hKrD k)) hKrD
      (hphysical.trans ball_subset_closedBall) (fun k ↦ hD k.1) (fun k ↦ hh k.1)
      (fun k ↦ (hroot k.1).2.1) hprad hbrad
      (fun k v hv ↦ (hκspeed k.1).trans ((hroot k.1).2.2.2.2 v (hKrD k hv)))
      (fun k ↦ zj k.1 k.2) (fun k ↦ Rj k.1 k.2) (fun k ↦ rj k.1 k.2)
      (fun k ↦ T k.1) hfrad
      (fun k ↦ (selected_common_elapsed_lt_evolutionTime f k.1 (hc k.1)).2.2)
      (fun k ↦ (hgeom k.1 k.2).2.2.2.2.1) I g charts hgr hderiv hnorm hcover hbuffer
  obtain ⟨m, hmsmooth, hrange, hcompact, heven, hreach, _, hsupport,
    hterminal, hjet, hnest, _⟩ :=
    hcut Runit Splus hRunit hSplus (physicalSymmetricHull_reflection S) hprop
  have hmipoint {p : E × E} (hp : p ∈ interior {p | mi p = 1}) : p ∈ tsupport mi := by
    apply subset_tsupport mi
    have he : mi p = 1 := interior_subset (s := {p | mi p = 1}) hp
    change mi p ≠ 0
    rw [he]
    exact one_ne_zero
  have hshoulder k : cthickening θ (tsupport (m k)) ⊆
      (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩ physicalProtectedRegion K := by
    intro p hp
    have hp' := hmipoint (hterminal k hp)
    exact ⟨hmisupp hp', hmterminal.support_subset hp'⟩
  have hreachSub depth : reachableAt Ractual S depth ⊆
      reachableAt (reflectedProofRelation Runit) Splus depth := by
    rintro q ⟨p, hp, hchain⟩
    refine ⟨p, Or.inl hp, ?_⟩
    clear hp
    induction hchain with
    | refl p => exact .refl p
    | tail hs _ ih =>
      exact .tail (hs.imp_right (fun h ↦ Or.inl (physicalDirectRelation_subset_unit_masks h))) ih
  have hreachable k : cthickening θ (reachableAt Ractual S k.val) ⊆
      interior {p | m k p = 1} :=
    (cthickening_subset_of_subset _ ((hreachSub k.val).trans
      (reachableAt_subset_bufferedReachableAt (reflectedProofRelation Runit) Splus δproof k.val))).trans
      (hreach k)
  have hm k : IsBufferedLocalizer (m k) (reachableAt Ractual S k.val)
      (physicalProtectedRegion K) := ⟨hmsmooth k, hrange k, hcompact k,
    fun p hp ↦ (hshoulder k (self_subset_cthickening _ hp)).2,
    fun p hp ↦ hreachable k (self_subset_cthickening _ hp)⟩
  have hsourceShoulder : cthickening θ (tsupport (m 0)) ⊆ V :=
    (hsupport 0).trans (hconstruct δproof hδproof.le le_rfl).1
  have hfirst : IsBufferedLocalizer (m 0) S V := ⟨hmsmooth 0, hrange 0, hcompact 0,
    fun p hp ↦ hsourceShoulder (self_subset_cthickening _ hp),
    fun p hp ↦ hreach 0 (self_subset_cthickening _ (Or.inl hp))⟩
  have hunit (k : Fin N) : ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
      p = q ∨ Runit p q → closedBall q θ ⊆ interior {p | m k.succ p = 1} :=
    fun p hp q hpq ↦ hnest k p hp q (hpq.imp_right Or.inl)
  have hactual (k : Fin N) : ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
      p = q ∨ Ractual p q → closedBall q θ ⊆ interior {p | m k.succ p = 1} :=
    fun p hp q hpq ↦ hunit k p hp q (hpq.imp_right physicalDirectRelation_subset_unit_masks)
  have hcarrierActual := hcarrier
      (fun k : Jrad ↦ (cRad k.1 k.2)⁻¹ • ℓ k.1)
      (fun k : Jrad ↦ cRad k.1 k.2 • (z k.1).2.2)
      (fun k : Jrad ↦ cRad k.1 k.2 * εroot k.1)
      (fun k : Jrad ↦ cRad k.1 k.2 * G k.1)
      (fun k ↦ mul_nonneg (hcRad k.1 k.2).le (hc k.1).2.2.1.le)
      hMglobal hLx hκ hΔ Q hQ hQM irad hrad Φrad Ur Kr (fun k ↦ D k.1) W
      (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output)
      (fun k ↦ hD k.1) (fun k ↦ hh k.1) (fun k ↦ (hroot k.1).2.1) hKrD
      (hphysical.trans ball_subset_closedBall) (fun k v hv ↦ hprad k v (Or.inr hv)) hbrad
      (fun k v hv ↦ (hκspeed k.1).trans ((hroot k.1).2.2.2.2 v (hKrD k hv)))
      (fun k ↦ zj k.1 k.2) (fun k ↦ Rj k.1 k.2) (fun k ↦ rj k.1 k.2)
      (fun k ↦ T k.1) hfrad
      (fun k ↦ (selected_common_elapsed_lt_evolutionTime f k.1 (hc k.1)).2.2)
      (fun k ↦ (hgeom k.1 k.2).2.2.2.2.1) I g charts hgr hderiv hnorm hcover hbuffer
  have hcarrierAll depth : reachableAt (reflectedProofRelation Ractual) Splus depth ⊆
      protectedAnnularCarrier (cthickening 1 W) aCarrier bCarrier εterminal K :=
    (hcarrierActual depth).trans hE₁
  have htargetγ j : closedBall ((z j).1, z j) (2 * γ j) ⊆ (Cphase j).target := by
    apply (closedBall_subset_closedBall ?_).trans (htarget j)
    have hbound := (selected_mask_radius_protection_bounds f hradii j).2.1
    dsimp [γ] at *
    linarith
  choose Gext hGcont hGsmooth hGhom hGerm using fun j ↦
    ConicPhase.exists_continuous_conicPhase_extension (ℓ j) (Cphase j)
      (isCompact_closedBall _ _) (htargetγ j) (hsmooth j)
  dsimp only
  refine ⟨hcarrierAll, Gext, m, heven,
    fun j ↦ ⟨hGcont j, hGsmooth j, hGhom j, hGerm j⟩,
    hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet, hactual,
    ?_, ?_, ?_, hunit, ?_, hterminal, hnest, ?_⟩
  · exact fun k j ↦ IsBufferedLocalizer.canonicalProofLocalizer (coordinateSplit (i j)) (hm k)
  · intro k j
    exact canonicalProofLocalizer_support_bounds (i j)
      (fun p hp ↦ (hshoulder k (self_subset_cthickening _ hp)).1)
  · intro k j l p
    rw [norm_iteratedFDeriv_canonicalProofLocalizer]
    exact hjet k l _
  · intro k χ₂ χ₃ hcut p hp q hpq
    exact sourceRecutRelation_mem_closed_shoulder_plateau (hactual k) hcut hp hpq
  · intro k j backward Rf hRf x' y' r' p hr' hrγ ht hy hη hin hout
    have hI := hgapI i h Φ Cphase D W Δ hCphase hCsource htargetγ
      (fun j ↦ (hroot j).1) (fun j w hw ↦ (hroot j).2.2.2.1 w hw) hhom hdiff
      (fun j ↦ selected_inverse_complete_segments f j Q (Φ j) (Cphase j) (hd j))
      (m k.castSucc) (m k.succ) (hunit k) j backward Rf hRf x' y' r' p
      hr' hrγ ht hy hη hin hout
    have hQMlocal : cNorm (closedBall x RQ) 3 Q ≤ Mglobal :=
      (cNorm_mono_set_of_contDiffAt (hphysical.trans ball_subset_closedBall)
        (isCompact_closedBall _ _) (fun _ _ ↦ hQ.contDiffAt.of_le (by simp))).trans hQM
    have hthird (r : ℝ) : 3 * (r / 3) = r := by ring
    have hdouble (r : ℝ) : 2 * (r / 2) = r := by ring
    have hT r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrε : r₁ ≤ εcollar) :=
      hgapT Q i Φ Cphase (fun _ ↦ hQMlocal)
        (fun j ↦ by simpa only [hdouble] using htarget j) hsmooth
        (fun j ↦ by
          simpa only [ρ, hthird, hdouble] using (hd j).2.2.2.2.2.2.2.2.2.2.2.2.1 2)
        hdiag (m k.castSucc) (m k.succ)
        (fun q hq ↦ hunit k q hq q (Or.inl rfl)) j backward Rf hRf x' y' r₁ p
        hr₁ hrε ht hy hη hin hout
    have hext r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrγ₁ : r₁ ≤ γ j) :=
      phaseGradientSquare_normalized_extension_eq eT eI (ℓ j) (Cphase j) (hGerm j)
        hRf backward x' y' (r₁, p)
        (elapsedChartPoint_mem_conic_boundary_buffer (ℓ j) (z j) (f.chart j).maskRadius_pos
          (haPhase j) p ⟨hr₁.1, hrγ₁⟩ ht hy hη)
    have hIext := (hext r' hr' hrγ).1 ▸ hI
    have hText r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrε : r₁ ≤ εcollar) :=
      (hext r₁ hr₁ (hrε.trans (hεγ j))).2 ▸ hT r₁ hr₁ hrε
    refine ⟨⟨hI, hT r' hr'⟩, hIext, hText r' hr', ?_, ?_, ?_, ?_⟩
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp (hδI.trans_le hI)
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδT.trans_le (hT 0 ⟨le_rfl, hΔ⟩ hεcollar.le))
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp (hδI.trans_le hIext)
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδT.trans_le (hText 0 ⟨le_rfl, hΔ⟩ hεcollar.le))

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
