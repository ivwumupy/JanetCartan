module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCutoffChoices

/-!
# The actual pre-source all-cells sampling cap

One positive callback controls the literal original spatial radius and original
angular width. It retains the scalar, joint-cutoff, sharp-label and both normal
geometry caps on the SAME named witnesses. Irrelevant parent slots get one;
the actual selected parent is in the good branch by `SelectedBoundary.fact1.2`.

The accompanying tolerance and rate are chosen before source σ and all current
histories. They are additional source-scale/large-frequency obligations, not
assumed bounds (`new:sec:order-of-choices`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Metric
namespace JanetCartan.PhysicalSampling
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open FullPhaseCharts.ActualComparison Sampling Sampling.MeasuredAmplitude OriginalChoices

variable {m : ℕ} (hn : 5 ≤ m + 1) (p : ℕ)
  (q : IncidenceCenter (OriginalBoundary.D hn))
  (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
  (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)

/-- The positive minimum on an admitted original parent. No current field,
reference, source scale or later derivative budget is an input. -/
def candidateSamplingCap
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    {a : ℝ // 0 < a} := by
  let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint ((1 / 4 : ℝ) • q.1.2)
  have hηb : ηb ≠ 0 := (PhysicalNormalInverse.OriginalTransport.quarter_incidence_facts hn q l).2.2.2
  exact ⟨min (Scalar.cap (p := p) hn q l j hroot / 4)
      (min (Cutoff.cap (p := p) hn q l j hroot)
        (min (Label.cap (p := p) hn q l j hroot)
          (min (angularWidth ηb (Mean.radius (p := p) hn q l j hroot))
            (angularWidth ηb (Comparison.radius (p := p) hn q l j hroot))))),
    lt_min (div_pos (Scalar.hcap (p := p) hn q l j hroot) (by norm_num))
      (lt_min (Cutoff.hcap (p := p) hn q l j hroot)
        (lt_min (Label.hcap (p := p) hn q l j hroot)
          (lt_min (angularWidth_spec hηb (Mean.hradius (p := p) hn q l j hroot)).1
            (angularWidth_spec hηb (Comparison.hradius (p := p) hn q l j hroot)).1)))⟩

/-- The actual all-cells `aExtra` supplied before original conic selection.
A later strong cap may shrink it; no selected parent is identified with a
parent selected using a different callback. -/
def originalSamplingExtraCap : {a : ℝ // 0 < a} := by
  classical
  exact if hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
      spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
    ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j) then
    candidateSamplingCap hn p q l j hroot
  else ⟨1, zero_lt_one⟩

/-- All five literal cap admissions on the actual admitted parent. These
bounds apply to BOTH selected spatial radius and selected angular width. -/
theorem originalSamplingExtraCap_spec
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    let cap : ℝ := originalSamplingExtraCap hn p q l j
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint ((1 / 4 : ℝ) • q.1.2)
    cap ≤ Scalar.cap (p := p) hn q l j hroot ∧
      cap ≤ Cutoff.cap (p := p) hn q l j hroot ∧
      cap ≤ Label.cap (p := p) hn q l j hroot ∧
      cap ≤ angularWidth ηb (Mean.radius (p := p) hn q l j hroot) ∧
      cap ≤ angularWidth ηb (Comparison.radius (p := p) hn q l j hroot) := by
  simp only [originalSamplingExtraCap, dite_eq_left hroot]
  dsimp only [candidateSamplingCap]
  have hquarter : Scalar.cap (p := p) hn q l j hroot / 4 ≤
      Scalar.cap (p := p) hn q l j hroot := by
    have := Scalar.hcap (p := p) hn q l j hroot
    linarith
  exact ⟨(min_le_left _ _).trans hquarter,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- The factor four is essential: the original physical cutoffs extend to
`4 * a`, not merely to the selected radius `a`. -/
theorem originalSamplingExtraCap_four_le_scalar_inner
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    4 * (originalSamplingExtraCap hn p q l j).1 ≤
      (Scalar.χstar (p := p) hn q l j hroot).rIn := by
  have hquarter : (originalSamplingExtraCap hn p q l j).1 ≤
      Scalar.cap (p := p) hn q l j hroot / 4 := by
    simp only [originalSamplingExtraCap, dite_eq_left hroot]
    dsimp only [candidateSamplingCap]
    exact min_le_left _ _
  have hinner := Scalar.hcap_χstar (p := p) hn q l j hroot
  linarith

/-- The SAME scalar output cutoff equals one on all three original physical
cutoff supports, including their full outer collar. -/
theorem originalSamplingExtraCap_scalar_cutoffs
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j))
    {a : ℝ} (ha : 0 < a) (hcap : a ≤ (originalSamplingExtraCap hn p q l j).1) :
    ∀ i : Fin 3, ∀ x ∈ tsupport (FixedCutoffs.physical (n := m + 1) ha i),
      Scalar.χstar (p := p) hn q l j hroot x = 1 := by
  intro i x hx
  apply (Scalar.χstar (p := p) hn q l j hroot).one_of_mem_closedBall
  exact closedBall_subset_closedBall
    ((mul_le_mul_of_nonneg_left hcap (by norm_num)).trans
      (originalSamplingExtraCap_four_le_scalar_inner hn p q l j hroot))
    (FixedCutoffs.physical_tsupport_four ha i hx)

/-- The actual common low-six stress tolerance; a source interval must be
chosen small enough for this NEW value as well as the old selected tolerance. -/
def candidateSamplingTolerance
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    {δ : ℝ // 0 < δ} :=
  ⟨min (Scalar.δ (p := p) hn q l j hroot)
    (min (Mean.δ (p := p) hn q l j hroot)
      (min (Band.δ (p := p) hn q l j hroot) (Comparison.δ (p := p) hn q l j hroot))),
    lt_min (Scalar.hδ (p := p) hn q l j hroot)
      (lt_min (Mean.hδ (p := p) hn q l j hroot)
        (lt_min (Band.hδ (p := p) hn q l j hroot) (Comparison.hδ (p := p) hn q l j hroot)))⟩

/-- The same positive low-six tolerance lies below all four factory tolerances. -/
theorem candidateSamplingTolerance_spec
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    let δ : ℝ := candidateSamplingTolerance hn p q l j hroot
    δ ≤ Scalar.δ (p := p) hn q l j hroot ∧
      δ ≤ Mean.δ (p := p) hn q l j hroot ∧
      δ ≤ Band.δ (p := p) hn q l j hroot ∧
      δ ≤ Comparison.δ (p := p) hn q l j hroot := by
  dsimp only [candidateSamplingTolerance]
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The single small rate window, also enforcing the exact finite-phase shift
needed for the same joint cutoff's plateau. -/
def candidateSamplingRate
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    {e : ℝ // 0 < e} := by
  let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
  let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
  let ρ := originalSamplingRadius hn q l j
  exact ⟨min (Scalar.ε (p := p) hn q l j hroot)
    (min (Mean.e (p := p) hn q l j hroot)
      (min (Comparison.e (p := p) hn q l j hroot)
        (min (Band.e (p := p) hn q l j hroot / 2)
          (measuredPhaseRadius T hP (ρ := (ρ : ℝ)))))),
    lt_min (Scalar.hε (p := p) hn q l j hroot)
      (lt_min (Mean.he (p := p) hn q l j hroot)
        (lt_min (Comparison.he (p := p) hn q l j hroot)
          (lt_min (half_pos (Band.he (p := p) hn q l j hroot))
            (measuredPhaseRadius_pos T ρ.2 hP))))⟩

/-- All small-rate admissions retain the same original phase radius. -/
theorem candidateSamplingRate_spec
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    let e : ℝ := candidateSamplingRate hn p q l j hroot
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
    let ρ : ℝ := originalSamplingRadius hn q l j
    e ≤ Scalar.ε (p := p) hn q l j hroot ∧
      e ≤ Mean.e (p := p) hn q l j hroot ∧
      e ≤ Comparison.e (p := p) hn q l j hroot ∧
      e ≤ Band.e (p := p) hn q l j hroot / 2 ∧
      e ≤ measuredPhaseRadius T hP (ρ := ρ) := by
  dsimp only [candidateSamplingRate]
  exact ⟨min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- Preserve every earlier user cap in the ONE callback passed to the strong
source and current construction. Its subsequent raw cap is still applied only
once by `strongCappedExtra`. -/
def samplingCappedExtra (userExtra : PhysicalNormalInverse.StrongExtraCaps hn) :
    PhysicalNormalInverse.StrongExtraCaps hn := fun q l j ↦
  ⟨min (userExtra q l j).1 (originalSamplingExtraCap hn p q l j).1,
    lt_min (userExtra q l j).2 (originalSamplingExtraCap hn p q l j).2⟩

/-- Existing preselection buffers survive the sampling minimum. -/
theorem samplingCappedExtra_le_user (userExtra : PhysicalNormalInverse.StrongExtraCaps hn) :
    (samplingCappedExtra hn p userExtra q l j).1 ≤ (userExtra q l j).1 :=
  min_le_left _ _

/-- The same single callback retains every original sampling buffer. -/
theorem samplingCappedExtra_le_sampling (userExtra : PhysicalNormalInverse.StrongExtraCaps hn) :
    (samplingCappedExtra hn p userExtra q l j).1 ≤ (originalSamplingExtraCap hn p q l j).1 :=
  min_le_right _ _

end JanetCartan.PhysicalSampling
