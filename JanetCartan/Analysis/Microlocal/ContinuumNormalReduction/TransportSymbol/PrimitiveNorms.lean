module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Assembly

/-!
# Primitive finite norms for the continuum spectator amplitude

The consumer is `exists_transportAmplitude_shell_bound`: its coefficient
profiles are derived here from the original masks and fields, using the
buffered interpolation in `app:ch_regular_base:eq:joint-primitive-product`.
The evaluated initial scalar is also treated before inverse substitution.
Neither an amplitude bound nor a bound on a composed coefficient is an input.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol

/-- A fixed ball with a smoothness buffer for a primitive in
`app:ch_background:eq:bg-mixed-input`. It contains only domain geometry. -/
structure PrimitiveNormChart (E : Type*) [NormedAddCommGroup E] where
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  region : Set E
  isOpen_region : IsOpen region
  ball_subset : closedBall center radius ⊆ region

namespace PrimitiveNormChart
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The compact set on which the primitive finite norms are measured.
Source: `app:ch_background:eq:bg-mixed-input`. -/
def carrier (D : PrimitiveNormChart E) : Set E := closedBall D.center D.radius

/-- Smoothness and the actual low/high norms of a primitive. The low order
is fixed at one and the high order is `s`; no profile or composed-function
estimate is stored. Source: `app:ch_background:eq:bg-mixed-input`. -/
structure Controls (D : PrimitiveNormChart E) (s : ℕ) (M B H : ℝ)
    (f : E → F) : Prop where
  smooth : ContDiffOn ℝ ∞ f D.region
  low : cNorm D.carrier 1 f ≤ M
  high : 1 + cNorm D.carrier s f ≤ B * H

/-- Interpolation of a primitive's actual finite norms, with its constant
chosen before the primitive and the common high norm vary. Consumed by the
coefficient and initial-multiplier assemblies below; source:
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem exists_profiles [FiniteDimensional ℝ E] (D : PrimitiveNormChart E)
    {s : ℕ} (hs : 2 ≤ s) {M B : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ (f : E → F) (H : ℝ), 1 ≤ H → D.Controls s M B H f →
      ∀ p ∈ D.carrier, ShellJetProfile s H C f p := by
  obtain ⟨C, hC, hb⟩ := exists_shellJetProfile_of_cNorm (F := F)
    D.center D.radius_pos D.isOpen_region D.ball_subset hs hM hB
  exact ⟨C, hC, fun f H hH h ↦ hb f H h.smooth hH h.low h.high⟩

end PrimitiveNormChart

variable {n N : ℕ}

/-- Fixed primitive domains for the five coefficient functions in
`app:ch_background:eq:bg-full-complex-amplitude`. The normal and reduced
covector have the same physical/carrier variables. -/
structure CoefficientNormCharts (n : ℕ) where
  measurement : PrimitiveNormChart (Euclidean n)
  angular : PrimitiveNormChart ((ℝ × Euclidean 2) × Euclidean (n - 1))
  high : PrimitiveNormChart ℝ
  field : PrimitiveNormChart (Euclidean n × (ℝ × Euclidean 2))

namespace CoefficientNormCharts

/-- Each original evaluation lies in its fixed primitive norm domain.
This is a chart range condition, independent of coefficient values and jets.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
def Contains (D : CoefficientNormCharts n) (p : InputVariables n) : Prop :=
  p.1.1 ∈ D.measurement.carrier ∧ p.1.2 ∈ D.measurement.carrier ∧
  (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ∈ D.angular.carrier ∧
  ‖p.2.2‖ ∈ D.high.carrier ∧
  (p.1.1, p.2.1) ∈ D.field.carrier ∧ (p.1.2, p.2.1) ∈ D.field.carrier

/-- Primitive finite norms, prior to any substitution. In applications `H`
is `1 + ‖G‖_(C^(s+D)) + ∑ ‖r_a‖_(C^(s+D))`, and `M` is fixed first.
Source: `app:ch_background:eq:bg-mixed-input`. -/
structure Controls (D : CoefficientNormCharts n) (s : ℕ) (M B H : ℝ)
    (a : Coefficients n N) : Prop where
  measurement : D.measurement.Controls s M B H a.measurement
  angular : D.angular.Controls s M B H a.angular
  high : D.high.Controls s M B H a.high
  normal : D.field.Controls s M B H a.normal
  reduced : D.field.Controls s M B H a.reduced

/-- All coefficient profiles required by the actual shell theorem follow
from their finite primitive norms. No high-norm products and no derivative
shift are introduced. Source: `app:ch_regular_base:eq:joint-primitive-product`
and `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_profiles (D : CoefficientNormCharts n)
    {s : ℕ} (hs : 2 ≤ s) {M B : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ (a : Coefficients n N) (H : ℝ), 1 ≤ H → D.Controls s M B H a →
      ∀ p, D.Contains p → CoefficientShellProfiles s H C a p := by
  obtain ⟨C₁, h₁, hb₁⟩ := D.measurement.exists_profiles (F := ℝ) hs hM hB
  obtain ⟨C₂, h₂, hb₂⟩ := D.angular.exists_profiles (F := ℝ) hs hM hB
  obtain ⟨C₃, h₃, hb₃⟩ := D.high.exists_profiles (F := ℝ) hs hM hB
  obtain ⟨C₄, h₄, hb₄⟩ := D.field.exists_profiles (F := Euclidean N) hs hM hB
  obtain ⟨C₅, h₅, hb₅⟩ := D.field.exists_profiles (F := Fin n → ℝ) hs hM hB
  refine ⟨C₁ + C₂ + C₃ + C₄ + C₅, by positivity, ?_⟩
  intro a H hH h p hp
  obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅, hp₆⟩ := hp
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  exact {
    leftMeasurement := (hb₁ a.measurement H hH h.measurement _ hp₁).mono (by linarith) hH0
    rightMeasurement := (hb₁ a.measurement H hH h.measurement _ hp₂).mono (by linarith) hH0
    angular := (hb₂ a.angular H hH h.angular _ hp₃).mono (by linarith) hH0
    high := (hb₃ a.high H hH h.high _ hp₄).mono (by linarith) hH0
    leftNormal := (hb₄ a.normal H hH h.normal _ hp₅).mono (by linarith) hH0
    rightNormal := (hb₄ a.normal H hH h.normal _ hp₆).mono (by linarith) hH0
    leftReduced := (hb₅ a.reduced H hH h.reduced _ hp₅).mono (by linarith) hH0
    rightReduced := (hb₅ a.reduced H hH h.reduced _ hp₆).mono (by linarith) hH0 }

end CoefficientNormCharts

/-- Removing the high-frequency mask costs only the constant profile of one.
This connects the primitive norm assembly to the homogeneous symbol in
`app:ch_background:eq:bg-symbol`. -/
theorem CoefficientShellProfiles.homogeneous
    {s : ℕ} {H M : ℝ} {a : Coefficients n N} {p : InputVariables n}
    (h : CoefficientShellProfiles s H M a p) (hM : 0 ≤ M) (hH : 0 ≤ H) :
    CoefficientShellProfiles s H (M + 1) (homogeneousCoefficients a) p := by
  have hle : M ≤ M + 1 := by linarith
  refine {
    leftMeasurement := h.leftMeasurement.mono hle hH
    rightMeasurement := h.rightMeasurement.mono hle hH
    angular := h.angular.mono hle hH
    high := ?_
    leftNormal := h.leftNormal.mono hle hH
    rightNormal := h.rightNormal.mono hle hH
    leftReduced := h.leftReduced.mono hle hH
    rightReduced := h.rightReduced.mono hle hH }
  refine ⟨contDiffAt_const, ?_, ?_⟩
  · simpa [homogeneousCoefficients] using (show 1 ≤ M + 1 by linarith)
  · intro i hi _
    simp only [homogeneousCoefficients, iteratedFDeriv_const_of_ne (by omega : i ≠ 0),
      Pi.zero_apply, norm_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hH _)

/-- Primitive norms of `r`, `Y`, and `ν` imply profiles of the actual weighted
normal `r(z,Y(x,z)) • ν(x,z)`. The constants precede all three fields, and the
common high norm occurs once. The footpoint range is a geometric assumption,
not a bound on the composed scalar. Source: `app:ch_background:eq:bg-mixed-input`.
Consumed by the coefficient assembly with initial multipliers. -/
theorem exists_initialWeightedNormal_profile_of_norms
    (D : PrimitiveNormChart (Euclidean n × (ℝ × Euclidean 2)))
    (Dr : PrimitiveNormChart ((ℝ × Euclidean 2) × Euclidean (n - 1)))
    {s : ℕ} (hs : 2 ≤ s) {M B : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) :
    ∃ C > 0,
      ∀ (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
        (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
        (ν : Euclidean n × (ℝ × Euclidean 2) → Euclidean N) (H : ℝ),
        1 ≤ H → Dr.Controls s M B H r → D.Controls s M B H Y →
        D.Controls s M B H ν →
        (∀ p ∈ D.carrier, (p.2, Y p) ∈ Dr.carrier) →
        ∀ p ∈ D.carrier, ShellJetProfile s H C (initialWeightedNormal r Y ν) p := by
  obtain ⟨C₁, h₁, hb₁⟩ := Dr.exists_profiles (F := ℝ) hs hM hB
  obtain ⟨C₂, h₂, hb₂⟩ := D.exists_profiles (F := Euclidean (n - 1)) hs hM hB
  obtain ⟨C₃, h₃, hb₃⟩ := D.exists_profiles (F := Euclidean N) hs hM hB
  obtain ⟨C, hC, hb⟩ := exists_initialWeightedNormal_profile (N := N) s hs
    (show 0 ≤ C₁ + C₂ + C₃ by positivity) (isCompact_closedBall D.center D.radius)
  refine ⟨C, hC, ?_⟩
  intro r Y ν H hH hr hY hν hmap p hp
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  exact hb r Y ν H hH p hp
    ((hb₁ r H hH hr _ (hmap p hp)).mono (by linarith) hH0)
    ((hb₂ Y H hH hY p hp).mono (by linarith) hH0)
    ((hb₃ ν H hH hν p hp).mono (by linarith) hH0)

/-- Inserting the actual evaluated initial multiplier into the coefficient
profiles requires only primitive finite norms. No norm of the weighted normal
is assumed. Positivity can be supplied independently via `initialMultiplier_pos`;
the jet estimate itself holds for every real scalar. Source:
`app:ch_background:eq:bg-mixed-input`. -/
theorem exists_initialMultiplier_coefficientShellProfiles_of_norms
    (D : CoefficientNormCharts n)
    (Dr : PrimitiveNormChart ((ℝ × Euclidean 2) × Euclidean (n - 1)))
    {s : ℕ} (hs : 2 ≤ s) {M B : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ (a : Coefficients n N)
      (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)) (H : ℝ),
      1 ≤ H → D.Controls s M B H a → Dr.Controls s M B H r →
      D.field.Controls s M B H Y →
      (∀ p ∈ D.field.carrier, (p.2, Y p) ∈ Dr.carrier) →
      ∀ p, D.Contains p → CoefficientShellProfiles s H C (withInitialMultiplier a r Y) p := by
  obtain ⟨C₁, h₁, hb₁⟩ := D.exists_profiles (N := N) hs hM hB
  obtain ⟨C₂, h₂, hb₂⟩ := exists_initialWeightedNormal_profile_of_norms
    (N := N) D.field Dr hs hM hB
  refine ⟨C₁ + C₂, add_pos h₁ h₂, ?_⟩
  intro a r Y H hH ha hr hY hmap p hp
  have h := hb₁ a H hH ha p hp
  have hn := hb₂ r Y a.normal H hH hr hY ha.normal hmap
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have h₁₂ : C₁ ≤ C₁ + C₂ := le_add_of_nonneg_right h₂.le
  have h₂₁ : C₂ ≤ C₁ + C₂ := le_add_of_nonneg_left h₁.le
  exact {
    leftMeasurement := h.leftMeasurement.mono h₁₂ hH0
    rightMeasurement := h.rightMeasurement.mono h₁₂ hH0
    angular := h.angular.mono h₁₂ hH0
    high := h.high.mono h₁₂ hH0
    leftNormal := (hn _ hp.2.2.2.2.1).mono h₂₁ hH0
    rightNormal := (hn _ hp.2.2.2.2.2).mono h₂₁ hH0
    leftReduced := h.leftReduced.mono h₁₂ hH0
    rightReduced := h.rightReduced.mono h₁₂ hH0 }

/-- Smoothness of an initial multiplier follows from its primitive scalar
and the genuine footpoint. This discharges the regularity input for the
weighted amplitude, independently of all quantitative bounds.
Source: `app:ch_background:eq:bg-mixed-input`. -/
theorem PrimitiveRegularity.withInitialMultiplier
    {a : Coefficients n N} {J : InputVariables n → ℝ} {U : Set (InputVariables n)}
    (h : PrimitiveRegularity a J U)
    {r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ}
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {V : Set (Euclidean n × (ℝ × Euclidean 2))}
    {Vr : Set ((ℝ × Euclidean 2) × Euclidean (n - 1))}
    (hr : ContDiffOn ℝ ∞ r Vr) (hY : ContDiffOn ℝ ∞ Y V)
    (hl : MapsTo (fun p : InputVariables n ↦ (p.1.1, p.2.1)) U V)
    (hrr : MapsTo (fun p : InputVariables n ↦ (p.1.2, p.2.1)) U V)
    (hmap : MapsTo (fun p ↦ (p.2, Y p)) V Vr) :
    PrimitiveRegularity (withInitialMultiplier a r Y) J U := by
  have hscalar : ContDiffOn ℝ ∞ (fun p ↦ r (p.2, Y p)) V :=
    hr.comp (contDiffOn_snd.prodMk hY) hmap
  exact { h with
    leftNormal := (hscalar.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd.fst) hl).smul
      h.leftNormal
    rightNormal := (hscalar.comp (contDiffOn_fst.snd.prodMk contDiffOn_snd.fst) hrr).smul
      h.rightNormal }

end JanetCartan.ContinuumNormalReduction.TransportSymbol
