module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Expressions

/-!
# Primitive joint fields from the phase and original amplitude

The inputs of the branch symbol budget are discharged here using the actual
coefficient producer. Directions need not be unit vectors: their fixed norms
enter the profile constants, never the coefficient-scale exponent. The
consumer is `hasFullSourceSymbolBound_jointTransferTerm`, for
`app:ch_response:eq:direct-envelope-profile` and `new:eq:carrier-coefficient`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open CompactTransfer

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal transfer coefficient is homogeneous in the external
direction, including at degenerate points of its total definition.
This introduces no frequency factor (`new:eq:carrier-coefficient`). -/
theorem transferCoefficient_smul_direction
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    (a : ℝ) (e q : E) (w : CarrierVariables n) :
    transferCoefficient f w₀ (a • e) q w = a • transferCoefficient f w₀ e q w := by
  have he : externalDerivative f (a • e) = a • externalDerivative f e := by
    funext p z
    simp [externalDerivative]
  have hg (p : E) (z : CarrierVariables n) :
      gradient (externalDerivative f (a • e) p) z =
        a • gradient (externalDerivative f e p) z := by
    rw [he]
    change (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm
      (fderiv ℝ (a • externalDerivative f e p) z) = _
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply, map_smul, gradient]
  simp_rw [transferCoefficient, averagedExternalGradient, hg]
  rw [intervalIntegral.integral_smul, map_smul]

variable {M ι : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]

private theorem norm_jet_amplitudeField_le
    {α : E → CarrierVariables n → M} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    (j : ℕ) {q : E × CarrierVariables n} (hq : q ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ j (jointAmplitudeFields b f w₀ α none) q‖ ≤
      ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ := by
  let T : M →L[ℝ] M × ℝ := (ContinuousLinearMap.id ℝ M).prod 0
  have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (by intro v; simp [T])
  exact (T.norm_iteratedFDeriv_comp_left (hα.contDiffAt ((hU.prod hD).mem_nhds hq))
    (by simp : (j : ℕ∞ω) ≤ ∞)).trans
      ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans_eq (one_mul _))

private theorem norm_jet_coefficientField_le
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    (α : E → CarrierVariables n → M) {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (e : E) (i : ι)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (j : ℕ) {q : E × CarrierVariables n} (hq : q ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ j (jointAmplitudeFields b f w₀ α (some (e, i))) q‖ ≤
      ‖iteratedFDeriv ℝ j (Function.uncurry (transferCoefficient f w₀ e)) q‖ := by
  let T : CarrierVariables n →L[ℝ] M × ℝ := (0 : CarrierVariables n →L[ℝ] M).prod
    (-(innerSL ℝ (b i)))
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro w
    change max ‖(0 : M)‖ ‖-inner ℝ (b i) w‖ ≤ 1 * ‖w‖
    rw [norm_zero, norm_neg, Real.norm_eq_abs, one_mul]
    apply max_le (norm_nonneg w)
    simpa only [b.norm_eq_one, one_mul] using abs_real_inner_le_norm (b i) w
  exact (T.norm_iteratedFDeriv_comp_left (hA.contDiffAt ((hU.prod hD).mem_nhds hq))
    (by simp : (j : ℕ∞ω) ≤ ∞)).trans
      ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans_eq (one_mul _))

variable [FiniteDimensional ℝ E]

/-- Construct the profile of the literal joint primitive fields from primitive
phase and original-amplitude jets on the same box. The coefficient producer is
instantiated, with exactly two phase derivatives spent and a fixed reserve.
The constants precede scale, frequency, varying fields and requested order.
No coefficient-field or modified-amplitude budget is assumed.
Source: `new:eq:carrier-coefficient`, original `app:ch_response:eq:direct-envelope-profile`.
-/
theorem exists_jointAmplitudeFields_jet_profile
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ Pj : Option (E × ι) → ℕ → ℝ, (∀ i j, 0 ≤ Pj i j) ∧
      ∀ (R : ℕ), 3 ≤ R → ∀ (L : ℝ), 1 ≤ L → ∀ (N : ℕ)
        (b : OrthonormalBasis ι ℝ (CarrierVariables n))
        (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
        (α : E → CarrierVariables n → M) (U : Set E) (D : Set (CarrierVariables n)),
      IsOpen U → IsOpen D → Convex ℝ D →
      ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D) →
      ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U D →
      (∀ q ∈ U, gradient (f q) (w₀ q) = 0) →
      (∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w)) →
      (∀ q ∈ U, ∀ w ∈ D, ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ B) →
      (∀ j ≤ N + 2, ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L ^ (j - R)) →
      ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D) →
      (∀ j ≤ N, ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - R)) →
      ∀ i j, j ≤ N → ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (jointAmplitudeFields b f w₀ α i) q‖ ≤
          Pj i j * L ^ (j + 2 - R) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_transferCoefficient_jet_profile (n := n) (E := E)
    Aphase hphase hB
  let Pj : Option (E × ι) → ℕ → ℝ := fun i j =>
    match i with
    | none => Aamp j
    | some (e, _) => (max 1 ‖e‖) * C j
  refine ⟨Pj, ?_, ?_⟩
  · intro i j
    cases i with
    | none => exact hamp j
    | some v => exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (hC j)
  intro R hR L hL N b f w₀ α U D hU hD hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet i j hj q hq
  have hA := contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hu
  cases i with
  | none => exact (norm_jet_amplitudeField_le hU hD hα b f w₀ j hq).trans (hαjet j hj q hq)
  | some v =>
    let m := max 1 ‖v.1‖
    have hm : 0 < m := zero_lt_one.trans_le (le_max_left _ _)
    let e := m⁻¹ • v.1
    have he : ‖e‖ ≤ 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm.le)]
      exact (inv_mul_le_iff₀ hm).mpr (by simp [m])
    have hve : m • e = v.1 := by simp [e, smul_smul, hm.ne']
    have heq : Function.uncurry (transferCoefficient f w₀ v.1) =
        m • Function.uncurry (transferCoefficient f w₀ e) := by
      funext z
      change transferCoefficient f w₀ v.1 z.1 z.2 = m • transferCoefficient f w₀ e z.1 z.2
      rw [← hve, transferCoefficient_smul_direction]
    have hb := hcoeff (R - 2) (by omega) L hL N f w₀ U D hU hD hcD hf hw₀ h₀ hcrit hu hi
      (by simpa only [show R - 2 + 2 = R by omega] using hp) e he j hj q hq
    apply (norm_jet_coefficientField_le α hU hD b v.1 v.2 (hA v.1) j hq).trans
    rw [heq, iteratedFDeriv_const_smul_apply
      (((hA e).contDiffAt ((hU.prod hD).mem_nhds hq)).of_le (by simp)),
      norm_smul, Real.norm_of_nonneg hm.le]
    have hb' := mul_le_mul_of_nonneg_left hb hm.le
    simpa only [show j - (R - 2) = j + 2 - R by omega, ← mul_assoc] using hb'

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
