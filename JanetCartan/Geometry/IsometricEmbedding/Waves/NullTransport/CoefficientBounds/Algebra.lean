module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# Fixed formulas for the actual principal transport coefficients

The input is the frame and the identical carrier gradient, with the original
Euclidean/Frobenius norms. These formulas supply the principal part of
`app:ch_waves:eq:joint-tame`; the adapted denominator uses the actual section
normal. Its positive gap will be instantiated by `exists_actual_nullvectors`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.CoefficientBounds

variable {n : ℕ}

/-- Value inputs to the finite-jet formulas in `app:ch_waves:thm:leading`. -/
abbrev Input (n : ℕ) := (Fin n → MetricTensor n) × Euclidean n

/-- The Euclidean right cofactor column (`app:ch_waves:thm:leading`). -/
def right (c : Fin n) (p : Input n) : Euclidean n :=
  WithLp.toLp 2 (rightNullvector (reducedSymbol p.1 p.2) c)

/-- The left cofactor row (`app:ch_waves:thm:leading`). -/
def left (r : Fin n) (p : Input n) : Fin n → ℝ :=
  leftNullvector (reducedSymbol p.1 p.2) r

/-- The original adapted denominator (`app:ch_waves:thm:leading`). -/
def denominator (ν : Euclidean n) (r c : Fin n) (p : Input n) : ℝ :=
  adaptedTimeCoefficient p.1 p.2 r c ν

/-- The normalized principal vector (`app:ch_waves:thm:leading`). -/
def direction (ν : Euclidean n) (r c : Fin n) (p : Input n) : Euclidean n :=
  WithLp.toLp 2 (fun a ↦
    transportField p.1 (left r p) (fun j ↦ right c p j) a / denominator ν r c p)

private theorem smooth_frame_entry (i j a : Fin n) :
    ContDiff ℝ ∞ (fun p : Input n ↦ p.1 i j a) :=
  (Matrix.entryLinearMap ℝ ℝ j a).toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mp (contDiff_fst :
      ContDiff ℝ ∞ (Prod.fst : Input n → Fin n → MetricTensor n)) i)

/-- Smoothness is polynomial and does not require a minor gap
(`app:ch_waves:thm:leading`). -/
theorem smooth_right (c : Fin n) : ContDiff ℝ ∞ (right c) := by
  rw [← contDiffOn_univ]
  exact (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp
    (contDiffOn_rightNullvector_reducedSymbol
      (fun i j a ↦ (smooth_frame_entry i j a).contDiffOn) contDiffOn_snd c))

/-- Smoothness of the same left cofactor row (`app:ch_waves:thm:leading`). -/
theorem smooth_left (r : Fin n) : ContDiff ℝ ∞ (left r) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_leftNullvector_reducedSymbol
    (fun i j a ↦ (smooth_frame_entry i j a).contDiffOn) contDiffOn_snd r

private theorem smooth_transport (r c a : Fin n) :
    ContDiff ℝ ∞ (fun p : Input n ↦
      transportField p.1 (left r p) (fun j ↦ right c p j) a) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_transportField (fun i j a ↦ (smooth_frame_entry i j a).contDiffOn)
    (smooth_left r).contDiffOn
    (contDiffOn_rightNullvector_reducedSymbol
      (fun i j a ↦ (smooth_frame_entry i j a).contDiffOn) contDiffOn_snd c) a

/-- Polynomial smoothness of the adapted denominator
(`app:ch_waves:thm:leading`). -/
theorem smooth_denominator (ν : Euclidean n) (r c : Fin n) :
    ContDiff ℝ ∞ (denominator ν r c) := by
  unfold denominator adaptedTimeCoefficient
  exact ContDiff.sum fun a _ ↦ contDiff_const.mul (smooth_transport r c a)

/-- The fixed compact value range retains the actual adapted gap. It is
chosen from low budgets, before the current immersion (`app:ch_waves:eq:joint-tame`). -/
def admissibleInputs (ν : Euclidean n) (r c : Fin n) (L ε : ℝ) : Set (Input n) :=
  closedBall 0 L ∩ {p | ε ≤ |denominator ν r c p|}

/-- Compactness of the fixed range in the Frobenius and Euclidean norms
(`app:ch_waves:eq:joint-tame`). -/
theorem compact_admissibleInputs (ν : Euclidean n) (r c : Fin n) (L ε : ℝ) :
    IsCompact (admissibleInputs ν r c L ε) :=
  (isCompact_closedBall 0 L).inter_right
    (isClosed_le continuous_const (smooth_denominator ν r c).continuous.abs)

/-- The gap makes the reciprocal smooth on the entire fixed range
(`app:ch_waves:eq:joint-tame`). -/
theorem smoothAt_inverse {ν : Euclidean n} {r c : Fin n} {L ε : ℝ}
    (hε : 0 < ε) {p : Input n} (hp : p ∈ admissibleInputs ν r c L ε) :
    ContDiffAt ℝ ∞ (fun q ↦ (denominator ν r c q)⁻¹) p :=
  (smooth_denominator ν r c).contDiffAt.inv (abs_pos.mp (hε.trans_le hp.2))

/-- Smoothness of the literal normalized direction on the fixed gap range
(`app:ch_waves:eq:joint-tame`). -/
theorem smoothAt_direction {ν : Euclidean n} {r c : Fin n} {L ε : ℝ}
    (hε : 0 < ε) {p : Input n} (hp : p ∈ admissibleInputs ν r c L ε) :
    ContDiffAt ℝ ∞ (direction ν r c) p := by
  apply (contDiffAt_piLp 2).mpr
  intro a
  exact (smooth_transport r c a).contDiffAt.div (smooth_denominator ν r c).contDiffAt
    (abs_pos.mp (hε.trans_le hp.2))

end JanetCartan.NullTransport.CoefficientBounds
