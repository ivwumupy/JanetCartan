module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhaseGrades

/-!
# Elapsed variation of the tangential derivative

The only variable phase input is the second derivative of the original joint
two-time phase. The remaining elapsed dependence is the linear covector term
`-r τ`. This supplies the quantitative collar step in
`app:ch_regular:lem:finite-chain`, without compactness of a coefficient class.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph

variable {d : ℕ}

/-- Fixed tangential part of the elapsed coordinate map; consumer: the
boundary collar of `app:ch_regular:eq:chain-tail`. -/
def elapsedTangentialCoordinates : JointVariables (Euclidean (d + 1)) →L[ℝ]
    SymbolBudgets.TwoTimePoint d :=
  elapsedJointCoordinates.comp (ContinuousLinearMap.inr ℝ ℝ _)

/-- The temporal covector in the fixed polynomial part of the elapsed phase
(`app:ch_regular:eq:joint-kernel-phase`). -/
def elapsedTemporalCovector : JointVariables (Euclidean (d + 1)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ p.2.1 0
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem tangential_phase_decomposition
    (backward : Bool) (Ψ : TwoTimePhase d) (x y : Euclidean (d + 1)) (r : ℝ) :
    (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) =
      (if backward then (-1 : ℝ) else 1) •
        (fun w ↦ SymbolBudgets.jointPhase Ψ (elapsedJointCoordinates (r, w)) -
          r * elapsedTemporalCovector w) +
      (fun w ↦ jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y (0, w)) := by
  funext w
  cases backward <;>
    simp [jointElapsedPhase, jointPhase, forwardPhase, reversePhase, elapsedPhase,
      SymbolBudgets.jointPhase, elapsedJointCoordinates, elapsedTemporalCovector] <;> ring

private theorem hasFDerivAt_elapsed_tangential_coordinates (r : ℝ)
    (p : JointVariables (Euclidean (d + 1))) :
    HasFDerivAt (fun w ↦ elapsedJointCoordinates (r, w)) elapsedTangentialCoordinates p :=
  (elapsedJointCoordinates (d := d)).hasFDerivAt.comp p
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) r p)

private theorem fderiv_tangential_phase
    (backward : Bool) (Ψ : TwoTimePhase d) (x y : Euclidean (d + 1))
    (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hΨ : DifferentiableAt ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (r, p))) :
    fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p =
      (if backward then (-1 : ℝ) else 1) •
        ((fderiv ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (r, p))).comp
          elapsedTangentialCoordinates - r • elapsedTemporalCovector) +
      fderiv ℝ (fun w ↦ jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y (0, w)) p := by
  have hQ : Differentiable ℝ
      (fun w ↦ jointElapsedPhase backward (fun _ _ _ _ ↦ 0) x y (0, w)) :=
    ((contDiff_jointElapsedPhase_zero backward x y).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  rw [tangential_phase_decomposition]
  exact ((((hΨ.hasFDerivAt.comp p (hasFDerivAt_elapsed_tangential_coordinates r p)).sub
    ((elapsedTemporalCovector (d := d)).hasFDerivAt.const_mul r)).const_smul
      (if backward then (-1 : ℝ) else 1)).add (hQ p).hasFDerivAt).fderiv

/-- Elapsed variation costs only the variation of the original two-time
derivative and the fixed temporal covector. The estimate is valid for both
orientations and arbitrary external bases (`app:ch_regular:eq:chain-tail`). -/
theorem norm_elapsed_tangential_derivative_sub_le
    (backward : Bool) (Ψ : TwoTimePhase d) (x y : Euclidean (d + 1))
    (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hr : DifferentiableAt ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (r, p)))
    (h0 : DifferentiableAt ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (0, p))) :
    ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p -
      fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (0, w)) p‖ ≤
      ‖fderiv ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (r, p)) -
        fderiv ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (0, p))‖ *
          ‖elapsedTangentialCoordinates (d := d)‖ + |r| * ‖elapsedTemporalCovector (d := d)‖ := by
  have he :
      fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p -
        fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (0, w)) p =
      (if backward then (-1 : ℝ) else 1) •
        ((fderiv ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (r, p)) -
          fderiv ℝ (SymbolBudgets.jointPhase Ψ) (elapsedJointCoordinates (0, p))).comp
            elapsedTangentialCoordinates - r • elapsedTemporalCovector) := by
    rw [fderiv_tangential_phase backward Ψ x y r p hr,
      fderiv_tangential_phase backward Ψ x y 0 p h0]
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    ring
  rw [he]
  have hn : ‖(if backward then (-1 : ℝ) else 1)‖ = 1 := by cases backward <;> norm_num
  rw [norm_smul, hn, one_mul]
  exact (norm_sub_le _ _).trans (add_le_add
    (ContinuousLinearMap.opNorm_comp_le _ _) (by rw [norm_smul, Real.norm_eq_abs]))

/-- A common second-jet bound on a fixed convex domain controls the
tangential elapsed variation. `SecondJets` extracts this input from the
actual coefficient-to-phase constructor at order two; no equicontinuity
or common collar is assumed (`app:ch_regular:lem:finite-chain`). -/
theorem norm_elapsed_tangential_derivative_sub_le_of_secondJet
    (backward : Bool) (Ψ : TwoTimePhase d) (x y : Euclidean (d + 1))
    {J : Set (SymbolBudgets.TwoTimePoint d)} (hJ : Convex ℝ J)
    (hs : ∀ q ∈ J, ContDiffAt ℝ 2 (SymbolBudgets.jointPhase Ψ) q)
    {N : ℝ} (hN : 0 ≤ N)
    (hjet : ∀ q ∈ J, ‖iteratedFDeriv ℝ 2 (SymbolBudgets.jointPhase Ψ) q‖ ≤ N)
    (r : ℝ) (p : JointVariables (Euclidean (d + 1)))
    (hr : elapsedJointCoordinates (r, p) ∈ J) (h0 : elapsedJointCoordinates (0, p) ∈ J) :
    ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p -
      fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (0, w)) p‖ ≤
      (N * ‖elapsedJointCoordinates (d := d)‖ * ‖elapsedTangentialCoordinates (d := d)‖ +
        ‖elapsedTemporalCovector (d := d)‖) * |r| := by
  have hd q hq := ((hs q hq).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hb q (hq : q ∈ J) : ‖fderiv ℝ (fderiv ℝ (SymbolBudgets.jointPhase Ψ)) q‖ ≤ N := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hjet q hq
  have hv := hJ.norm_image_sub_le_of_norm_fderiv_le hd hb h0 hr
  have hcoord : ‖elapsedJointCoordinates (r, p) - elapsedJointCoordinates (0, p)‖ ≤
      ‖elapsedJointCoordinates (d := d)‖ * |r| := by
    have hh := (elapsedJointCoordinates (d := d)).le_opNorm ((r, p) - (0, p))
    rw [map_sub] at hh
    simpa only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_mk,
      norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg r)] using hh
  have hv' := hv.trans (mul_le_mul_of_nonneg_left hcoord hN)
  apply (norm_elapsed_tangential_derivative_sub_le backward Ψ x y r p
    ((hs _ hr).differentiableAt (by norm_num)) ((hs _ h0).differentiableAt (by norm_num))).trans
  exact (add_le_add (mul_le_mul_of_nonneg_right hv' (norm_nonneg _)) le_rfl).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
