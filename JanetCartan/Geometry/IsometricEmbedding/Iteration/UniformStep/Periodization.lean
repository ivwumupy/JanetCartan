module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.StageConstants

/-!
# Physical corrections as actual smooth periodic stage fields

The adapter used by `jc-uniform-history-step` for `main:thm:step` and
`main:eq:metric-ledger`. A fixed physical cutoff equals one on an open
neighborhood of the closed core and has support strictly inside the unit cell.
The construction proves smooth periodicity, equality of all core jets, exact
L² transfer, and integer Sobolev transfer for the same cut fields.

`fields` sets the stage's `V` and `S` to the periodic lifts. Thus the secondary
identity is global, while agreement with the original physical fields is local.
The physical fields, their physical profiles, and their physical mean/pair
identities still come from their respective producers. No construction of those
inputs or unconditional one-step existence is asserted here.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep.Periodization

variable {n N : ℕ}

/-- The literal secondary torus field `W₂ = b² V + S` in `main:thm:step`. -/
def secondaryTorus (χ : Euclidean n → ℝ) (b : ℝ) (V S : Euclidean n → Euclidean N) :
    Torus n → Euclidean N := b ^ 2 • cutToTorus χ V + cutToTorus χ S

/-- The secondary torus field is the periodization of the same combined cut
physical field whose profiles occur in `main:eq:joint-physical-profile`. -/
theorem secondaryTorus_eq_cutToTorus (χ : Euclidean n → ℝ) (b : ℝ)
    (V S : Euclidean n → Euclidean N) :
    secondaryTorus χ b V S = cutToTorus χ (b ^ 2 • V + S) := by
  rw [cutToTorus_add, cutToTorus_smul]
  rfl

/-- Global secondary identity for `StageConstants.Identities.secondary`
(`main:eq:metric-ledger`). The right hand side uses the periodic lifts. -/
theorem periodicLift_secondaryTorus (χ : Euclidean n → ℝ) (b : ℝ)
    (V S : Euclidean n → Euclidean N) :
    periodicLift (secondaryTorus χ b V S) =
      b ^ 2 • periodicLift (cutToTorus χ V) + periodicLift (cutToTorus χ S) := rfl

/-- The secondary construction is smooth on the torus (`main:thm:step`). -/
theorem isSmoothPeriodic_secondaryTorus {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (hχ : ContDiff ℝ ∞ χ) (b : ℝ) {V S : Euclidean n → Euclidean N}
    (hV : ContDiff ℝ ∞ V) (hS : ContDiff ℝ ∞ S) :
    IsSmoothPeriodic (secondaryTorus χ b V S) := by
  rw [secondaryTorus_eq_cutToTorus]
  exact isSmoothPeriodic_cutToTorus hr hs hχ ((contDiff_const.smul hV).add hS)

/-- Exact L² transfer for the same secondary field (`main:eq:step-L2`). -/
theorem periodicL2Norm_secondaryTorus {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (b : ℝ) (V S : Euclidean n → Euclidean N) :
    periodicL2Norm (secondaryTorus χ b V S) =
      Real.sqrt (∫ x, ‖cutField χ (b ^ 2 • V + S) x‖ ^ 2) := by
  rw [secondaryTorus_eq_cutToTorus]
  exact periodicL2Norm_cutToTorus hr hs _

/-- All integer profiles of the same secondary field transfer to the Fourier
Sobolev norm consumed by `StageConstants` (`main:eq:joint-physical-profile`). -/
theorem periodicSobolevNorm_secondaryTorus_le {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (hχ : ContDiff ℝ ∞ χ) (b : ℝ) {V S : Euclidean n → Euclidean N}
    (hV : ContDiff ℝ ∞ V) (hS : ContDiff ℝ ∞ S) (m : ℕ) :
    periodicSobolevNorm m (secondaryTorus χ b V S) ≤ Real.sqrt (m.factorial : ℝ) *
      LocalSobolev.cartesianJetNorm univ m
        (fun j ↦ iteratedFDeriv ℝ j (cutField χ (b ^ 2 • V + S))) := by
  rw [secondaryTorus_eq_cutToTorus]
  exact periodicSobolevNorm_cutToTorus_le hr hs hχ ((contDiff_const.smul hV).add hS) m

/-- Every core jet of `W₂` is the jet of the combined physical correction
(`main:eq:metric-ledger`). -/
theorem iteratedFDeriv_secondaryTorus_eqOn (D : LocalDomain)
    {χ : Euclidean n → ℝ} {r : ℝ} (hr : r < 1 / 2)
    (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (b : ℝ) (V S : Euclidean n → Euclidean N) (j : ℕ) :
    EqOn (iteratedFDeriv ℝ j (periodicLift (secondaryTorus χ b V S)))
      (iteratedFDeriv ℝ j (b ^ 2 • V + S)) (D.core n) := by
  rw [secondaryTorus_eq_cutToTorus]
  exact iteratedFDeriv_cutToTorus_eqOn D hr hs hU hcore hone _ j

/-- Pair strain transfer, with the physical error tensor unchanged on the core
(`main:eq:metric-ledger`). In particular any pointwise bound for the right hand
side transfers with the identical constant. -/
theorem pairStrain_cutToTorus_eqOn (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (F S : Euclidean n → Euclidean N) (Qoff : MetricField n) :
    EqOn (linearizedMetric F (periodicLift (cutToTorus χ S)) + Qoff)
      (linearizedMetric F S + Qoff) (D.core n) := by
  intro x hx
  exact congrArg (fun v ↦ v + Qoff x)
    (linearizedMetric_cutToTorus_eqOn D hr hs hU hcore hone F S hx)

/-- Actual stage fields supplied to `StageConstants.exists_uniform_correction`
by `jc-uniform-history-step` (`main:thm:step`). Physical inputs are cut and
periodized; the stage's physical-domain `V,S` are their global periodic lifts. -/
def fields (D : LocalDomain) (χ : Euclidean n → ℝ) (R δ b : ℝ)
    (F P V S : Euclidean n → Euclidean N)
    (g e eR H Hself Qoff Emean : MetricField n) : StageConstants.Fields n N where
  R := R
  δ := δ
  b := b
  D := D.core n
  F := F
  P := cutToTorus χ P
  V := periodicLift (cutToTorus χ V)
  S := periodicLift (cutToTorus χ S)
  W := secondaryTorus χ b V S
  g := g
  e := e
  eR := eR
  H := H
  Hself := Hself
  Qoff := Qoff
  Emean := Emean

/-- The periodization obligation in `main:thm:step` is discharged for the concrete
stage fields. The premises are the original physical identities and smoothness;
jet agreement, periodic smoothness, and the global secondary identity are proved.
Actual physical mean/pair constructions remain with their respective producers. -/
theorem identities_fields (D : LocalDomain) {χ : Euclidean n → ℝ} {r : ℝ}
    (hr : r < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ r})
    (hχ : ContDiff ℝ ∞ χ)
    {U : Set (Euclidean n)} (hU : IsOpen U) (hcore : D.core n ⊆ U)
    (hone : EqOn χ (fun _ ↦ 1) U) (R δ b : ℝ)
    (F P V S : Euclidean n → Euclidean N)
    (g e eR H Hself Qoff Emean : MetricField n)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : b ≠ 0)
    (hF : ∀ x ∈ D.core n, DifferentiableAt ℝ F x)
    (hP : ContDiff ℝ ∞ P) (hV : ContDiff ℝ ∞ V) (hS : ContDiff ℝ ∞ S)
    (hdefect : EqOn e (g - inducedMetric F) (D.core n))
    (hself : EqOn Hself (b ^ 2 • H) (D.core n))
    (hoff : EqOn Qoff (inducedMetric P - Hself) (D.core n))
    (hmean : EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) (D.core n)) :
    StageConstants.Identities (fields D χ R δ b F P V S g e eR H Hself Qoff Emean) := by
  refine {
    amplitude_pos := hδ
    amplitude_le_one := hδone
    b_ne_zero := hb
    differentiable_F := hF
    smooth_P := isSmoothPeriodic_cutToTorus hr hs hχ hP
    smooth_W := isSmoothPeriodic_secondaryTorus hr hs hχ b hV hS
    differentiable_V := fun x _ ↦
      (isSmoothPeriodic_cutToTorus hr hs hχ hV).2.differentiable (by simp) x
    differentiable_S := fun x _ ↦
      (isSmoothPeriodic_cutToTorus hr hs hχ hS).2.differentiable (by simp) x
    defect := hdefect
    secondary := periodicLift_secondaryTorus χ b V S
    self := hself
    off := ?_
    mean := ?_ }
  · intro x hx
    change Qoff x = inducedMetric (periodicLift (cutToTorus χ P)) x - Hself x
    rw [inducedMetric_cutToTorus_eqOn D hr hs hU hcore hone P hx]
    exact hoff hx
  · intro x hx
    change Emean x = linearizedMetric F (periodicLift (cutToTorus χ V)) x + H x -
      (b ^ 2)⁻¹ • eR x
    rw [linearizedMetric_cutToTorus_eqOn D hr hs hU hcore hone F V hx]
    exact hmean hx

end JanetCartan.UniformStep.Periodization
