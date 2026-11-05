module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.BufferedBounds

/-!
# The actual two-time upper endpoint and its normalized jets

The upper endpoint in `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`, evaluates `W₁(t,s,y,η)`
at `s=t`. Its position derivatives therefore differentiate both times.
The linear pullback below retains those two slots and is a contraction.
The input seminorms are exactly those produced by
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => EvolutionIntegral.SymbolBudgets.TwoTimePoint d

/-- Both time slots of the upper-endpoint pullback in
`app:ch_regular_base:eq:energy-complete-residual` vary with physical time. -/
def diagonalLinear : E →L[ℝ] T :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ ((x 0, x 0, spatialPart x), 0)
      map_add' := by intro x y; ext <;> first | rfl | simp
      map_smul' := by intro a x; ext <;> first | rfl | simp }

/-- The two-time diagonal costs no derivative orders in the endpoint
estimate of `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem norm_diagonalLinear_le : ‖diagonalLinear (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change max (max |x 0| (max |x 0| ‖spatialPart x‖)) ‖(0 : Euclidean d)‖ ≤ 1 * ‖x‖
  rw [norm_zero, one_mul]
  have ht := PiLp.norm_apply_le x 0
  exact max_le (max_le ht (max_le ht (norm_spatialPart_le x))) (norm_nonneg x)

/-- Normalized covector insertion for the upper endpoint. The source and
output times remain equal as functions, not as frozen parameters.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def diagonalPoint (η : Euclidean d) (x : E) : T :=
  diagonalLinear x + ((0, 0, 0), η)

/-- Explicit coordinates of the endpoint pullback (`energy-complete-residual`). -/
@[simp] theorem diagonalPoint_eq (η : Euclidean d) (x : E) :
    diagonalPoint η x = ((x 0, x 0, spatialPart x), η) := by
  simp [diagonalPoint, diagonalLinear]

/-- Exact geometric inclusion to be instantiated by the finite-sector owner.
Both time conditions and the radial section are the SAME buffered jet set
used by the supported amplitude producer (`energy-complete-residual`). -/
theorem diagonalPoint_mem_bufferedJetSet_iff
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    (ε a b : ℝ) (η : Euclidean d) (x : E) :
    diagonalPoint η x ∈ ConicPhase.bufferedJetSet ℓ z ε a b ↔
      x 0 ∈ closedBall z.1 (2 * ε) ∧
      spatialPart x ∈ closedBall z.2.1 (2 * ε) ∧
      η ∈ ConicPhase.radialSectionBand ℓ z.2.2 ε a b := by
  simp only [diagonalPoint_eq, ConicPhase.bufferedJetSet, mem_prod]
  tauto

/-- Every normalized endpoint position jet is bounded by the original JOINT
two-time seminorm, including both time derivatives. This is the primitive
input to the `A_t W₁(t,t) β` PDO in `energy-complete-residual`. -/
theorem cNorm_diagonal_orderField_le
    {J : Set T} (hJ : IsCompact J) {K : Set E}
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (o m : ℕ) (hb : BoundedTwoTimeOrderSeminorm o J m W)
    {R : ℝ} (hR : 1 ≤ R) (η : Euclidean d)
    (hmap : MapsTo (diagonalPoint η) K J) :
    cNorm K m (fun x : E ↦ R ^ o • W (x 0) (x 0) (spatialPart x) (R • η)) ≤
      twoTimeOrderSeminorm o J m W := by
  have hs : ContDiff ℝ ∞ (twoTimeOrderField o R W) := by
    change ContDiff ℝ ∞ (fun p : T ↦ (R ^ o) • jointAmplitude W (p.1, R • p.2))
    exact (hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).const_smul (R ^ o)
  have h := cNorm_preAffine_contraction_le diagonalLinear norm_diagonalLinear_le
    ((0, 0, 0), η) hJ isOpen_univ (subset_univ J) hs.contDiffOn hmap m
  have he : (fun x : E ↦ twoTimeOrderField o R W (diagonalLinear x + ((0, 0, 0), η))) =
      (fun x : E ↦ R ^ o • W (x 0) (x 0) (spatialPart x) (R • η)) := by
    funext x
    change twoTimeOrderField o R W (diagonalPoint η x) = _
    rw [diagonalPoint_eq]
    rfl
  rw [he] at h
  exact h.trans (cNorm_twoTimeOrderField_le hb hR)

/-- The cone converts spatial order minus one into full cycle-frequency order
minus one. The physical covector remains literally `2π ξ`. This controls the
weighted input of `PdoRealization.IntegerBounds`, including its literal
adjoint, for the endpoint in `energy-complete-residual`. -/
theorem cycle_bracket_le_shell_of_cone {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (ξ : E) (hcone : |((2 * Real.pi) • ξ) 0| ≤
      C * ‖spatialPart ((2 * Real.pi) • ξ)‖)
    (hshell : ‖spatialPart ((2 * Real.pi) • ξ)‖ ≤ R) :
    1 + ‖ξ‖ ≤ (2 * (C + 1)) * R := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.one_le_pi_div_two]
  have hnorm : ‖ξ‖ ≤ ‖(2 * Real.pi) • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    nlinarith [norm_nonneg ξ]
  have hc := norm_le_spatial_of_cone hcone
  have hs := mul_le_mul_of_nonneg_left hshell (by linarith : 0 ≤ C + 1)
  nlinarith

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
