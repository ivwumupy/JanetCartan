module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualGeometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.JointGrades
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Nonstationarity beyond the protected elapsed interval

The temporal component of the graph covector occurs only in the linear
clock term of the elapsed phase and in its original Fourier pairing. Thus
the clock mismatch is a directional derivative, with opposite signs for
the forward and literally reversed kernels.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E

/-- The temporal graph frequency gives this lower bound for the tangential joint
gradient without any chart condition on the integrated point. Both signs
come from the literal phases (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem elapsed_clock_defect_le_norm_tangential_fderiv (backward : Bool) (Ψ : TwoTimePhase d)
    (x y : E) (r : ℝ) (p : JointVariables E) (hF : DifferentiableAt ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r,w)) p) :
    |p.1.1 0 - p.1.2 0 - r| ≤ ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r,w)) p‖ := by
  let τ : E := EuclideanSpace.single 0 1
  let w : JointVariables E := (0, (τ, 0))
  let D := p.1.1 0 - p.1.2 0 - r
  have htime : τ 0 = 1 := by simp [τ, EuclideanSpace.single]
  have hsp : spatialPart τ = 0 := spatialPart_single_zero
  have hcoeff : inner ℝ p.1.2 τ = p.1.2 0 := by
    simp [τ, EuclideanSpace.inner_single_right]
  have hspace (t : ℝ) : spatialPart (p.2.1 + t • τ) = spatialPart p.2.1 := by
    change spatialPartCLM _ = _
    rw [map_add, map_smul, spatialPartCLM_apply, spatialPartCLM_apply, hsp, smul_zero, add_zero]
  have hline : (fun t : ℝ ↦ jointElapsedPhase backward Ψ x y (r, p + t • w)) =
      fun t ↦ jointElapsedPhase backward Ψ x y (r, p) + t * (if backward then -D else D) := by
    funext t
    cases backward <;> simp only [jointElapsedPhase, jointPhase, forwardPhase, reversePhase,
      elapsedPhase, Bool.false_eq_true, ↓reduceIte, w, Prod.smul_mk,
      Prod.fst_add, Prod.snd_add, smul_zero, add_zero,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, htime, mul_one, hspace,
      inner_add_right, real_inner_smul_right, hcoeff, D] <;> ring_nf
  have hev : fderiv ℝ (fun v ↦ jointElapsedPhase backward Ψ x y (r,v)) p w = if backward then -D else D := by
    rw [← hF.lineDeriv_eq_fderiv, lineDeriv, hline]
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (if backward then -D else D)).const_add
      (jointElapsedPhase backward Ψ x y (r, p))).deriv
  have hw : ‖w‖ = 1 := by simp [w, τ, Prod.norm_def, EuclideanSpace.single]
  have hb := (fderiv ℝ (fun v ↦ jointElapsedPhase backward Ψ x y (r,v)) p).le_opNorm w
  rw [hw, mul_one, hev] at hb
  cases backward <;> simpa only [Bool.false_eq_true, ↓reduceIte, norm_neg, Real.norm_eq_abs] using hb

/-- The temporal graph frequency gives this lower bound for the full joint
gradient without any chart condition on the integrated point. Both signs
come from the literal phases (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem elapsed_clock_defect_le_norm_fderiv (backward : Bool) (Ψ : TwoTimePhase d)
    (x y : E) (p : V) (hF : DifferentiableAt ℝ (jointElapsedPhase backward Ψ x y) p) :
    |p.2.1.1 0 - p.2.1.2 0 - p.1| ≤ ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) p‖ := by
  let F := jointElapsedPhase backward Ψ x y
  have hs := hF.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  apply (elapsed_clock_defect_le_norm_tangential_fderiv backward Ψ x y p.1 p.2
    hs.differentiableAt).trans
  change ‖fderiv ℝ (F ∘ Prod.mk p.1) p.2‖ ≤ _
  rw [hs.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa using (fderiv ℝ F p).le_opNorm (0, v)

/-- One positive squared-gradient bound for all late times on the literal
selected physical pair support. It is fixed before the coefficient, frequency,
mask order or history, and applies to every smooth supported replacement
of the spatial phase (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_late_elapsed_clock_phase_gap
    {κ : Type*} [Fintype κ] (eI : Module.Basis κ ℝ V) {R : ℝ} (hR : 0 < R) :
    ∃ δ > (0 : ℝ), ∀ (backward : Bool) (Ψ : TwoTimePhase d) (x y : E) (v : V),
      DifferentiableAt ℝ (jointElapsedPhase backward Ψ x y) v →
      |v.2.1.1 0 - v.2.1.2 0| ≤ 4 * R → 6 * R ≤ v.1 →
      δ ≤ phaseGradientSquare eI (jointElapsedPhase backward Ψ x y) v := by
  obtain ⟨B, hB, hbound⟩ := eI.exists_opNorm_le (F := ℝ)
  refine ⟨(R / B)^2, sq_pos_of_pos (div_pos hR hB), ?_⟩
  intro backward Ψ x y v hF htime hlate
  let F := jointElapsedPhase backward Ψ x y
  have hnorm := elapsed_clock_defect_le_norm_fderiv backward Ψ x y v hF
  have hlo : 2 * R ≤ ‖fderiv ℝ F v‖ := by
    linarith [neg_le_abs (v.2.1.1 0 - v.2.1.2 0 - v.1), le_abs_self (v.2.1.1 0 - v.2.1.2 0)]
  by_contra! hsmall
  have hcomponent (k : κ) : ‖fderiv ℝ F v (eI k)‖ ≤ R / B := by
    have hs : (fderiv ℝ F v (eI k))^2 ≤ phaseGradientSquare eI F v :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (fderiv ℝ F v (eI j))) (Finset.mem_univ k)
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (fderiv ℝ F v (eI k)), div_pos hR hB]
  have hu := hbound (div_pos hR hB).le hcomponent
  rw [mul_div_cancel₀ R hB.ne'] at hu
  linarith

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
