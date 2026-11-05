module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Collars
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization

/-!
# Localizing the selected-chart equation to the common output

Literal multiplication and local a.e. equality preserve the tested physical
operator on the measurement plateau. The PDO identity is proved from its
actual symbol budget and kernel, including the source mask before Fourier
multiplication. Consumer: `energy-complete-residual` on the common output of
`PhysicalConstruction`, before the finite-sector sum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.PdoRealization Characteristic.EvolutionIntegral
open FourierIntegral FourierIntegral.LowBounds FourierIntegral.FullLowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
open Pseudodifferential
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- A tested physical action depends only on the input's a.e. class near the
closed test support. This includes derivatives of the full test/coefficient
product and the zeroth-order term (`energy-complete-residual`). -/
theorem physicalTestAction_eq_of_ae_on
    (A : E → Fin (d+1) → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    {U : Set E} (hU : MeasurableSet U) (u v : E → Fin q → ℂ)
    (huv : u =ᵐ[volume.restrict U] v) (φ : E → ℝ) (hφ : tsupport φ ⊆ U)
    (i : Fin q) : physicalTestAction A B u φ i = physicalTestAction A B v φ i := by
  have he := (ae_restrict_iff' hU).mp huv
  have hd (a : Fin (d+1)) (j : Fin q) :
      (∫ x, partialDeriv (fun y ↦ φ y * A y a i j) x a • u x j) =
      ∫ x, partialDeriv (fun y ↦ φ y * A y a i j) x a • v x j := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    by_cases hxU : x ∈ U
    · rw [hx hxU]
    · have hn : x ∉ tsupport (fun y ↦ φ y * A y a i j) :=
        fun hm ↦ hxU (hφ (tsupport_mul_subset_left hm))
      simp [partialDeriv, fderiv_of_notMem_tsupport ℝ hn]
  have hb (j : Fin q) : (∫ x, (φ x * B x i j) • u x j) =
      ∫ x, (φ x * B x i j) • v x j := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    by_cases hxU : x ∈ U
    · rw [hx hxU]
    · have hz : φ x = 0 := by
        by_contra hn
        exact hxU (hφ (subset_tsupport φ hn))
      simp [hz]
  simp only [physicalTestAction, hd, hb]

/-- The actual output multiplier is the identity as an L² class on its
measurement plateau (`sector-theorem-identity`). -/
theorem sourceCutMultiplier_ae_on_plateau
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (hp : ∀ x ∈ U, ψ x = 1) (u : H) :
    (fun x ↦ (sourceCutMultiplier ψ hψ hb u x).ofLp) =ᵐ[volume.restrict U]
      fun x ↦ (u x).ofLp := by
  filter_upwards [ae_restrict_of_ae (sourceCutMultiplier_coeFn ψ hψ hb u),
    ae_restrict_mem hU] with x hx hxU
  simp only [hx, hp x hxU, Complex.ofReal_one, one_smul]

/-- Localize the already proved tested equation by the literal common output
multiplier. No derivative or regularity of an arbitrary L² source is needed.
Consumer: the common-output selected solver (`energy-complete-residual`). -/
theorem tested_equation_sourceCutMultiplier
    (A : E → Fin (d+1) → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (S T : H →L[ℂ] H) (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (hp : ∀ x ∈ U, ψ x = 1)
    (ht : ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
      physicalTestAction A B (fun x ↦ (S u x).ofLp) φ i = ∫ x, φ x • T u x i) :
    ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
      physicalTestAction A B
        (fun x ↦ ((sourceCutMultiplier ψ hψ hb).comp S u x).ofLp) φ i =
      ∫ x, φ x • ((sourceCutMultiplier ψ hψ hb).comp T u) x i := by
  intro u φ hφ hcφ hsφ i
  simp only [ContinuousLinearMap.comp_apply]
  rw [physicalTestAction_eq_of_ae_on A B hU _ _
    (sourceCutMultiplier_ae_on_plateau ψ hψ hb hU hp (S u)) φ hsφ i, ht u φ hφ hcφ hsφ i]
  apply integral_congr_ae
  filter_upwards [sourceCutMultiplier_coeFn ψ hψ hb (T u)] with x hx
  by_cases hzero : φ x = 0
  · simp [hzero]
  · have hone := hp x (hsφ (subset_tsupport φ hzero))
    change φ x • T u x i = φ x • sourceCutMultiplier ψ hψ hb (T u) x i
    simp only [hx, hone, Complex.ofReal_one, one_smul]

/-- The canonical PDO with the smaller common output is precisely left
multiplication of the original canonical PDO. The primitive normal-amplitude
budget proves actual realization; density then identifies the two bounded
operators. The source mask retains its original position
(`energy-complete-residual`). -/
theorem sourceCutMultiplier_maskedPhysicalPDO
    (χout χsource : E → ℂ) (c : E → E → Mat) (R M : ℝ)
    (hc : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    (hp : ∀ x, (ψ x : ℂ) * χout x = (ψ x : ℂ)) :
    (sourceCutMultiplier ψ hψ hb).comp (maskedPhysicalPDO χout χsource c) =
      maskedPhysicalPDO (fun x ↦ (ψ x : ℂ)) χsource c := by
  have ht (u : graphTestSpace (d+1) q) :
      maskedPhysicalPDO χout χsource c (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (fun x ξ ↦ inner ℝ x ξ) (fun x z ξ ↦ (χout x * χsource z) • c x ξ) u := by
    have hh := canonicalGraph_frequencyCut_realizes (Nat.succ_pos d) _ hc (fun _ ↦ 1)
      contDiff_const zero_le_one (fun _ ↦ by simp) u
    have he : frequencyCutFullAmplitude (fun _ : E ↦ (1 : ℂ))
        (fun x z ξ ↦ (χout x * χsource z) • c x ξ) =
        (fun x z ξ ↦ (χout x * χsource z) • c x ξ) := by
      funext x z ξ
      exact one_smul ℂ _
    rw [he] at hh
    exact hh
  symm
  apply fullGraphOperator_eq_of_realizes
  intro u
  filter_upwards [sourceCutMultiplier_coeFn ψ hψ hb
    (maskedPhysicalPDO χout χsource c (graphTestToLp u)), ht u] with x hx hu
  change sourceCutMultiplier ψ hψ hb
    (maskedPhysicalPDO χout χsource c (graphTestToLp u)) x = _
  rw [hx, hu]
  simp only [graphTestOutput]
  rw [← WithLp.toLp_smul]
  apply congrArg (WithLp.toLp 2)
  rw [← graphOperator_target_mul (fun x ξ : E ↦ inner ℝ x ξ)
    (fun x z ξ ↦ (χout x * χsource z) • c x ξ) (fun x ↦ (ψ x : ℂ))
    (fun y ↦ (u.val y).ofLp) x]
  have he : (fun x z ξ ↦ (ψ x : ℂ) • ((χout x * χsource z) • c x ξ)) =
      fun x z ξ ↦ ((ψ x : ℂ) * χsource z) • c x ξ := by
    funext x z ξ
    rw [smul_smul, ← mul_assoc, hp]
  rw [he]

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
