module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.Primitives

/-!
# Initial multipliers evaluated at the genuine footpoint

The normal-field input of the shell theorem may contain a positive initial
multiplier r(z,Y(x,z)). This module proves its primitive composition and product
estimate with the same H, so the high norm of r is counted once alongside the
high geometric norm. Source: `app:ch_background:eq:bg-mixed-input`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
open FourierIntegral.NormalOneHigh
variable {n N : ℕ}

/-- Multiplying the primitive normal by its initial value at the genuine
footpoint, as in `app:ch_background:eq:bg-mixed-input`. -/
def initialWeightedNormal
    (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (ν : Euclidean n × (ℝ × Euclidean 2) → Euclidean N)
    (p : Euclidean n × (ℝ × Euclidean 2)) : Euclidean N := r (p.2, Y p) • ν p

/-- The actual initial multiplier is positive when its primitive initial
scalar is positive. No amplitude positivity is assumed. -/
theorem initialMultiplier_pos
    (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (hr : ∀ z y, 0 < r (z, y)) (p : Euclidean n × (ℝ × Euclidean 2)) :
    0 < r (p.2, Y p) := hr _ _

/-- The evaluated initial scalar and base normal together obey a one-high
primitive profile. Buffered interpolation of r, Y and ν supplies the three
inputs, using H = 1 + the geometric high norm + the initial-data high norm.
The derivative order s and its fixed producer shift do not increase.
Source: `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_initialWeightedNormal_profile
    (s : ℕ) (hs : 2 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    {P : Set (Euclidean n × (ℝ × Euclidean 2))} (hP : IsCompact P) :
    ∃ C > 0,
      ∀ (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
        (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
        (ν : Euclidean n × (ℝ × Euclidean 2) → Euclidean N) (H : ℝ),
        1 ≤ H → ∀ p ∈ P,
        ShellJetProfile s H M r (p.2, Y p) →
        ShellJetProfile s H M Y p → ShellJetProfile s H M ν p →
        ShellJetProfile s H C (initialWeightedNormal r Y ν) p := by
  obtain ⟨R, hR, hid⟩ := exists_fixedShellJetProfile hP
    (f := id) (fun _ _ ↦ contDiffAt_id) s hs
  let B := R + M
  have hB : 0 < B := by dsimp [B]; linarith
  let D := M + ∑ i ∈ Finset.range (s + 1), compositionBudget (fun _ ↦ M) (fun _ ↦ B) i
  have hMD : M ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg
    (fun i _ ↦ compositionBudget_nonneg (fun _ ↦ hM) (fun _ ↦ hB.le) i))
  let T := D + M
  have hT : 0 ≤ T := add_nonneg (hM.trans hMD) hM
  let mulMap := fun q : ℝ × Euclidean N ↦ q.1 • q.2
  have hm : ContDiff ℝ ∞ mulMap := contDiff_fst.smul contDiff_snd
  obtain ⟨A, hA, hop⟩ := exists_fixedShellJetProfile
    (isCompact_closedBall (0 : ℝ × Euclidean N) T)
    (fun _ _ ↦ hm.contDiffAt) s hs
  let C := A + ∑ i ∈ Finset.range (s + 1), compositionBudget (fun _ ↦ A) (fun _ ↦ T) i
  have hC : 0 < C := hA.trans_le (le_add_of_nonneg_right (Finset.sum_nonneg
    (fun i _ ↦ compositionBudget_nonneg (fun _ ↦ hA.le) (fun _ ↦ hT) i)))
  refine ⟨C, hC, ?_⟩
  intro r Y ν H hH p hp hr hY hν
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hc := (hid H hH p hp).snd.prod hY hR.le hM hHpos.le
  have hrY := hr.comp (f := fun p ↦ (p.2, Y p)) (x := p) hc hM hB.le hHpos
  have hpair := hrY.prod hν (hM.trans hMD) hM hHpos.le
  have hmem : (r (p.2, Y p), ν p) ∈ Metric.closedBall (0 : ℝ × Euclidean N) T := by
    simpa only [Metric.mem_closedBall, dist_zero_right, T, D, B, Function.comp_apply] using hpair.value
  exact (hop H hH _ hmem).comp (f := fun p ↦ (r (p.2, Y p), ν p)) (x := p)
    hpair hA.le hT hHpos

/-- Insert the initial scalar into the original normal field, leaving the
literal density definitions applicable without alteration. Source:
`app:ch_background:eq:bg-mixed-input`. -/
def withInitialMultiplier (a : Coefficients n N)
    (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)) : Coefficients n N :=
  { a with normal := initialWeightedNormal r Y a.normal }

/-- Assembly of the evaluated initial multiplier into the exact primitive
interface consumed by `exists_amplitude_shell_bound_of_primitives`. Each
primitive, including r and Y, uses the same H. Consequently inserting positive
initial data contributes one high norm, with no further derivative shift.
Source: `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_initialMultiplier_primitiveShellProfiles
    (s : ℕ) (hs : 2 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    {P : Set (Euclidean n × (ℝ × Euclidean 2))} (hP : IsCompact P) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)) (H : ℝ),
      1 ≤ H → ∀ p : InputVariables n,
      (p.1.1, p.2.1) ∈ P → (p.1.2, p.2.1) ∈ P →
      PrimitiveShellProfiles s H M a J p →
      ShellJetProfile s H M r (p.2.1, Y (p.1.1, p.2.1)) →
      ShellJetProfile s H M r (p.2.1, Y (p.1.2, p.2.1)) →
      ShellJetProfile s H M Y (p.1.1, p.2.1) →
      ShellJetProfile s H M Y (p.1.2, p.2.1) →
      PrimitiveShellProfiles s H C (withInitialMultiplier a r Y) J p := by
  obtain ⟨R, hR, hb⟩ := exists_initialWeightedNormal_profile (N := N) s hs hM hP
  refine ⟨M + R, by linarith, ?_⟩
  intro a J r Y H hH p hl hr hp hrl hrr hYl hYr
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hMC : M ≤ M + R := le_add_of_nonneg_right hR.le
  have hRC : R ≤ M + R := le_add_of_nonneg_left hM
  exact {
    leftMeasurement := hp.leftMeasurement.mono hMC hH0
    rightMeasurement := hp.rightMeasurement.mono hMC hH0
    angular := hp.angular.mono hMC hH0
    high := hp.high.mono hMC hH0
    jacobian := hp.jacobian.mono hMC hH0
    leftNormal := (hb r Y a.normal H hH _ hl hrl hYl hp.leftNormal).mono hRC hH0
    rightNormal := (hb r Y a.normal H hH _ hr hrr hYr hp.rightNormal).mono hRC hH0
    leftReduced := hp.leftReduced.mono hMC hH0
    rightReduced := hp.rightReduced.mono hMC hH0 }

end JanetCartan.ContinuumNormalReduction.TransportSymbol
