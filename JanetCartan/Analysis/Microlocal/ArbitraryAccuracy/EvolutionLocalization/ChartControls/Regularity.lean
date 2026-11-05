module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.PhaseFields

/-!
# Regularity of the original phase fields

All differentiability premises used in the chart estimates follow from joint
smoothness of the original two-time phase. For the constructed chart this is
`contDiffOn_twoTimePhase`, an output of `exists_localTwoTimeHamiltonPhase`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}

/-- Original joint smoothness gives smoothness of all three first-derivative
fields on the elapsed slice. Consumer: the low geometry of both chart
orientations (`app:ch_regular:eq:high-phase`). -/
theorem contDiffAt_phaseFields (Ψ : TwoTimePhase d) (r : ℝ)
    {p : (ℝ × Euclidean d) × Euclidean d}
    (hs : ContDiffAt ℝ ∞ (Function.uncurry (elapsedSpatialPhase Ψ r)) p) :
    ContDiffAt ℝ ∞ (phaseFootpoint Ψ r) p ∧
      ContDiffAt ℝ ∞ (phaseMomentum Ψ r) p ∧
      ContDiffAt ℝ ∞ (phaseShear Ψ r) p := by
  constructor
  · have hh : ContDiffAt ℝ ∞
        (Function.uncurry (fun q : (ℝ × Euclidean d) × Euclidean d => fun η =>
          elapsedSpatialPhase Ψ r q.1 η)) (p,p.2) :=
      hs.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact (InnerProductSpace.toDual ℝ (Euclidean d)).symm.contDiff.contDiffAt.comp p
      (hh.fderiv (m := ∞) contDiffAt_snd (by simp))
  constructor
  · have hh : ContDiffAt ℝ ∞
        (Function.uncurry (fun q : (ℝ × Euclidean d) × Euclidean d => fun y =>
          elapsedSpatialPhase Ψ r (q.1.1,y) q.2)) (p,p.1.2) :=
      hs.comp (p,p.1.2) ((contDiffAt_fst.fst.fst.prodMk contDiffAt_snd).prodMk
        contDiffAt_fst.snd)
    exact (InnerProductSpace.toDual ℝ (Euclidean d)).symm.contDiff.contDiffAt.comp p
      (hh.fderiv (m := ∞) contDiffAt_fst.snd (by simp))
  · have hh : ContDiffAt ℝ ∞
        (Function.uncurry (fun q : (ℝ × Euclidean d) × Euclidean d => fun z =>
          elapsedSpatialPhase Ψ r z q.2)) (p,p.1) :=
      hs.comp (p,p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    exact (hh.fderiv (m := ∞) contDiffAt_fst (by simp)).clm_apply contDiffAt_const

/-- The actual chart constructor supplies the original joint regularity
needed by all phase-field estimates. There is no regularity claim at a point
outside the chart target, in particular at excluded spatial frequency zero
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem contDiffAt_chartPhaseFields
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (r : ℝ) {p : (ℝ × Euclidean d) × Euclidean d}
    (hp : (p.1.1, (p.1.1-r, (p.1.2,p.2))) ∈ C.target) :
    ContDiffAt ℝ ∞ (phaseFootpoint (chartPhase C) r) p ∧
      ContDiffAt ℝ ∞ (phaseMomentum (chartPhase C) r) p ∧
      ContDiffAt ℝ ∞ (phaseShear (chartPhase C) r) p := by
  apply contDiffAt_phaseFields
  exact (hs.contDiffAt (C.open_target.mem_nhds hp)).comp p
    (contDiffAt_fst.fst.prodMk ((contDiffAt_fst.fst.sub contDiffAt_const).prodMk
      (contDiffAt_fst.snd.prodMk contDiffAt_snd)))

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
