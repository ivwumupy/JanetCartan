module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.Triangular

/-!
# Original phase fields used in the elapsed chart estimates

These are the original two-time phase derivatives restricted to `s = t-r`.
For the actual phase, `hasFDerivAt_twoTimePhase` identifies them
with the same inverse projection and root flow. Low derivative budgets on
these fields are the original joint phase grades of
`app:ch_regular:eq:high-phase`, not elapsed inverse or frequency estimates.
-/

@[expose] public noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d : ℕ}

/-- Original spatial covector derivative on the elapsed slice. Consumer:
the forward chart control (`app:ch_regular:eq:joint-stationary`). -/
def phaseFootpoint (Ψ : TwoTimePhase d) (r : ℝ)
    (p : (ℝ × Euclidean d) × Euclidean d) : Euclidean d :=
  gradient (Ψ p.1.1 (p.1.1-r) p.1.2) p.2

/-- Original spatial position derivative on the elapsed slice. Consumer:
the reverse chart control (`app:ch_regular:eq:joint-stationary`). -/
def phaseMomentum (Ψ : TwoTimePhase d) (r : ℝ)
    (p : (ℝ × Euclidean d) × Euclidean d) : Euclidean d :=
  gradient (fun y => Ψ p.1.1 (p.1.1-r) y p.2) p.1.2

/-- Original simultaneous-time derivative on the elapsed slice. This is
the temporal shear; its low budget is required even when the spatial mixed
block is close to the identity (`app:ch_regular:eq:high-phase`). -/
def phaseShear (Ψ : TwoTimePhase d) (r : ℝ)
    (p : (ℝ × Euclidean d) × Euclidean d) : ℝ :=
  elapsedTimeDerivative Ψ r p.1 p.2

/-- Coordinate projection for the original phase fields. Consumer:
`app:ch_regular_base:eq:fixed-time-representation`. -/
def phaseFieldPoint (x ξ : Euclidean (d+1)) :
    (ℝ × Euclidean d) × Euclidean d := ((x 0, spatialPart x), spatialPart ξ)

/-- Full input base from original phase derivatives, including `t-r`.
Consumer: the forward inverse bound (`app:ch_regular:eq:joint-stationary`). -/
def phaseBaseMap (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : Euclidean (d+1)) :
    Euclidean (d+1) :=
  timeSpacePoint (x 0-r) (phaseFootpoint Ψ r (phaseFieldPoint x ξ))

/-- Full output covector, for every temporal covector. Consumer: the reverse
inverse bound and full frequency comparison (`app:ch_regular:lem:finite-chain`). -/
def phaseCovectorMap (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : Euclidean (d+1)) :
    Euclidean (d+1) :=
  timeSpacePoint (ξ 0+phaseShear Ψ r (phaseFieldPoint x ξ))
    (phaseMomentum Ψ r (phaseFieldPoint x ξ))

/-- The footpoint derivative is the actual inverse chart, by the proved
original differential (`app:ch_regular:eq:joint-stationary`). -/
theorem phaseFootpoint_chartPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d+1)}
    (hp : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    phaseFootpoint (chartPhase C) r (phaseFieldPoint x ξ) =
      (C.symm (elapsedChartPoint r x ξ)).2.2.1 :=
  (show HasGradientAt _ _ _ from hasFDerivAt_twoTimePhase_covector hp).gradient

/-- The momentum derivative is transported by the same original root flow
(`app:ch_regular:eq:joint-stationary`). -/
theorem phaseMomentum_chartPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d+1)}
    (hp : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    phaseMomentum (chartPhase C) r (phaseFieldPoint x ξ) =
      (twoTimeState Φ (C.symm (elapsedChartPoint r x ξ))).2.2 :=
  (show HasGradientAt _ _ _ from hasFDerivAt_twoTimePhase_position hp).gradient

/-- Both Hamilton--Jacobi time terms survive in the temporal shear.
This is derived from the original differential, without an energy-zero
restriction (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem phaseShear_chartPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d+1)}
    (hp : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    phaseShear (chartPhase C) r (phaseFieldPoint x ξ) =
      h (x 0, (spatialPart x, (twoTimeState Φ (C.symm (elapsedChartPoint r x ξ))).2.2)) -
      h (x 0-r, ((C.symm (elapsedChartPoint r x ξ)).2.2.1, spatialPart ξ)) := by
  have hc : HasFDerivAt (fun p : ℝ × Euclidean d =>
      (p.1, (p.1-r, (p.2, spatialPart ξ)))) _ (x 0, spatialPart x) :=
    (ContinuousLinearMap.fst ℝ ℝ (Euclidean d)).hasFDerivAt.prodMk
      (((ContinuousLinearMap.fst ℝ ℝ (Euclidean d)).hasFDerivAt.sub_const r).prodMk
        ((ContinuousLinearMap.snd ℝ ℝ (Euclidean d)).hasFDerivAt.prodMk
          (hasFDerivAt_const _ _)))
  have hd := hp.comp (x 0, spatialPart x) hc
  change fderiv ℝ (fun p : ℝ × Euclidean d =>
    twoTimePhase C (p.1, (p.1-r, (p.2, spatialPart ξ)))) _ (1,0) = _
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (fun p : ℝ × Euclidean d =>
    twoTimePhase C (p.1, (p.1-r, (p.2, spatialPart ξ)))) (x 0, spatialPart x) (1,0) = _
  rw [hd.fderiv]
  simp [twoTimePhaseDifferential, elapsedChartPoint]

/-- The full input-base field is identified with the actual phase derivative.
Its producer is `hasFDerivAt_twoTimePhase` (`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_elapsedPhase_covector_eq_phaseBaseMap
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d+1)}
    (hp : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    fderiv ℝ (elapsedPhase (chartPhase C) r x) ξ =
      innerSL ℝ (phaseBaseMap (chartPhase C) r x ξ) := by
  rw [(hasFDerivAt_elapsedChartPhase_covector hp).fderiv]
  simp only [phaseBaseMap, phaseFootpoint_chartPhase hp, elapsedInputBase]

/-- The full output-covector field is identified with the actual phase
derivative, including the temporal shear (`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_elapsedPhase_output_eq_phaseCovectorMap
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d+1)}
    (hp : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    fderiv ℝ (fun u => elapsedPhase (chartPhase C) r u ξ) x =
      innerSL ℝ (phaseCovectorMap (chartPhase C) r x ξ) := by
  rw [(hasFDerivAt_elapsedChartPhase_output hp).fderiv]
  simp only [phaseCovectorMap, phaseMomentum_chartPhase hp, phaseShear_chartPhase hp,
    elapsedOutputCovector, elapsedChartPoint]
  congr 2
  ring

/-- Joint differentiability of the literal elapsed phase follows from the
original differential, with both original times retained. Consumer: both
chart controls (`app:ch_regular:eq:joint-stationary`). -/
theorem differentiableAt_elapsedChartPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {x ξ : Euclidean (d+1)}
    (hp : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ)) :
    DifferentiableAt ℝ (Function.uncurry (elapsedPhase (chartPhase C) r)) (x,ξ) := by
  let t₁ : (Euclidean (d+1) × Euclidean (d+1)) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).comp
      (ContinuousLinearMap.fst ℝ _ _)
  let t₂ : (Euclidean (d+1) × Euclidean (d+1)) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).comp
      (ContinuousLinearMap.snd ℝ _ _)
  let x₁ : (Euclidean (d+1) × Euclidean (d+1)) →L[ℝ] Euclidean d :=
    spatialPartCLM.comp (ContinuousLinearMap.fst ℝ _ _)
  let ξ₂ : (Euclidean (d+1) × Euclidean (d+1)) →L[ℝ] Euclidean d :=
    spatialPartCLM.comp (ContinuousLinearMap.snd ℝ _ _)
  have hc := t₁.hasFDerivAt.prodMk ((t₁.hasFDerivAt.sub_const r).prodMk
    (x₁.hasFDerivAt.prodMk ξ₂.hasFDerivAt)) (x := (x,ξ))
  have hd := ((t₁.hasFDerivAt.sub_const r).mul t₂.hasFDerivAt).add
    (hp.comp (x,ξ) hc)
  exact hd.differentiableAt

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
