module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.SelectedApplication
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedNestedLocalizers

/-!
# Analytic realization of the actual protected terminal mask family

Apply the bounded-localizer, cross-quantization and terminal-right estimates to
one geometric construction. The phase witnesses are supplied by the retained
solver, and no independent mask choice is substituted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius NNReal ENNReal

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open SelectedSectorProtection SelectedEvenProofMasks NormalizedTerminalProtection
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

/-- Realize the SAME terminal-protected even masks and apply the localizer
estimates needed by the complete alternating residual chain. The original
selected phase, reflection, source plateau and supported gradient gaps are
retained. Low, cross-quantization and terminal-defect constants precede the
current coefficients, history and source accuracy. The supplied phases can be
those of `exists_finite_selected_direct_construction_with_prescribed_alternating_leakage`;
there is no new phase or solver selection. Consumers:
`normalizedSource_alternatingChain_observation_rapidDecayAt.hcross` and `.htleak`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_terminal_even_masks_with_localizer_estimates
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
      ∃ lowCost : ℝ, 0 ≤ lowCost ∧
      ∃ crossCost terminalCost : ℕ → ℕ → ℝ,
        (∀ s q, 0 ≤ crossCost s q) ∧ (∀ s q, 0 ≤ terminalCost s q) ∧
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
      (∀ (ρ : ℝ) (hρ : 1 ≤ ρ),
        ∃ right left : Fin (N+1) → L2C →L[ℂ] L2C,
          (∀ k, right k = (left k).adjoint ∧
            (∀ u, right k u =ᵐ[volume] fun y ↦ WithLp.toLp 2
              (rightLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
            (∀ u, (∀ l, Integrable (fun y ↦ u y l)) → left k u =ᵐ[volume]
              fun y ↦ WithLp.toLp 2 (leftLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
            ‖right k‖ ≤ lowCost ∧ ‖left k‖ ≤ lowCost) ∧
          ∀ L : ℝ, 1 ≤ L → L ≤ ρ →
          ∀ (k : Fin N) (s q : ℕ) (backward : Bool)
            (u : LocalL2 (univ : Set E) CV),
          let scale := restrictionSobolevScale univ CV MeasurableSet.univ
          let cross := (1-localRetardedOperator MeasurableSet.univ univ (right k.succ)).comp
            (localRetardedOperator MeasurableSet.univ univ (left k.castSucc))
          let v := (if backward then cross.adjoint else cross) u
          let w := (1-localRetardedOperator MeasurableSet.univ univ (Mterminal ⟨ρ, hρ⟩))
            (localRetardedOperator MeasurableSet.univ univ (right k.castSucc) u)
          (v ∈ scale.level s ∧ scale.gradeNorm s v ≤
            crossCost s q*ρ^s*L^(s+(d+1+1))*(L/ρ)^q*‖u‖) ∧
          (w ∈ scale.level s ∧ scale.gradeNorm s w ≤
            terminalCost s q*ρ^(2*(d+1)+s)*L^(s+(d+1+1))*(L/ρ)^q*‖u‖)) ∧
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
  have hselected := exists_selected_terminal_even_proof_masks_of_coefficient_bound
    f hΩ T speed G rootCost hc hradii eT eI hKcone hKsym hr hMglobal hcgraph hCgraph
    hLx hε hphysical hΩΓ hΩsym χ₂ hχ₂ hχ₂support hχ₂source hKsource hsourceFrequency
    hV hSV hreflectV output
  dsimp only at hselected ⊢
  obtain ⟨hinput, aCarrier, haCarrier, bCarrier, habCarrier, εterminal, hεterminal,
    mi, δfinal, a, b, Rbase, Djet, Mterminal, hmi, hδfinal, ha, hab, hRbase,
    hmisupport, hDjet, hmijet, hMterminal, hsource, hselect⟩ := hselected
  refine ⟨hinput, aCarrier, haCarrier, bCarrier, habCarrier, εterminal, hεterminal,
    mi, δfinal, a, b, Rbase, Djet, Mterminal, hmi, hδfinal, ha, hab, hRbase,
    hmisupport, hDjet, hmijet, hMterminal, hsource, ?_⟩
  intro N aPhase bPhase haPhase
  obtain ⟨n, cRad, hcRad, Urad, θ, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hδI, hH, hεcollar, hδT, hεsmall, hχ, hχone, hχsupport, hχaway,
    hHcollar, hχjet, hselect⟩ := hselect N aPhase bPhase haPhase
  obtain ⟨lowCost, hlowCost, crossCost, terminalCost, hcrossCost, hterminalCost, hlocalizers⟩ :=
    exists_prescribed_buffered_chain_localizers a b Rbase H hH mi hmi.smooth
      hmi.compactSupport hθ
  refine ⟨n, cRad, hcRad, Urad, θ, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hδI, hH, hεcollar, hδT, hεsmall, hχ, hχone, hχsupport, hχaway,
    hHcollar, hχjet, lowCost, hlowCost, crossCost, terminalCost, hcrossCost, hterminalCost, ?_⟩
  intro Q hQ hQnorm Φ Cphase hprotection hsmooth hhom hproj hsrc htgt hphase hphaseDer hdiag
    I geometry charts hradius hLipschitz hgradient hcover hprotected
  obtain ⟨hreachable, Gext, m, heven, hGext, hm, hfirst, hfirstV, hplateau,
    hcarrier, hjets, hlink, hcanonical, hcanonicalSupport, hcanonicalJets,
    hunitLink, hrecut, hterminal, hreflected, hgap⟩ :=
    hselect Q hQ hQnorm Φ Cphase hprotection hsmooth hhom hproj hsrc htgt hphase
      hphaseDer hdiag I geometry charts hradius hLipschitz hgradient hcover hprotected
  refine ⟨hreachable, Gext, m, heven, hGext, hm, hfirst, hfirstV, hplateau,
    hcarrier, hjets, hlink, hcanonical, hcanonicalSupport, hcanonicalJets,
    hunitLink, hrecut, hterminal, hreflected, ?_, hgap⟩
  intro ρ hρ
  obtain ⟨right, left, hrealize, hestimates⟩ := hlocalizers N m _ _ _ hm hcarrier
    hjets hlink hterminal ρ hρ
  refine ⟨right, left, hrealize, ?_⟩
  intro L hL hLρ k s q backward u
  exact hestimates L hL hLρ (Mterminal ⟨ρ,hρ⟩) (hMterminal ⟨ρ,hρ⟩) k s q backward u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
