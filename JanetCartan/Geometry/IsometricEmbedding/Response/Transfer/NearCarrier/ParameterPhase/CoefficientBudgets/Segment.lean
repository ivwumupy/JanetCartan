module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.Differential
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral

/-! # Carrier segment jets

Primitive carrier estimates used by the parameter coefficient budget in
`app:ch_response:thm:response-literal-transfer`. The joint variable is `(x, ε, c)`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer

/-- Joint physical, normalized covector and parameter variables in
`app:ch_response:eq:direct-envelope-profile`. -/
abbrev ParameterCoefficientSpace (n p : ℕ) := Euclidean n × Euclidean n × Euclidean p

/-- Parameter projection used in the carrier jet pullback
(`app:ch_response:thm:response-literal-transfer`). -/
def parameterCoefficientProjection (n p : ℕ) :
    ParameterCoefficientSpace n p →L[ℝ] Euclidean p :=
  (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean p)).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean p))

private theorem projection_norm_le (n p : ℕ) :
    ‖parameterCoefficientProjection n p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  exact (norm_snd_le q.2).trans (by simpa using norm_snd_le q)

/-- Pulling a primitive carrier jet back to the joint variables costs no norm
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_parameterCoefficient_pullback_le {n p : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean p → F} {C : Set (Euclidean p)} (hC : IsOpen C)
    (hf : ContDiffOn ℝ ∞ f C) {q : ParameterCoefficientSpace n p}
    (hq : q.2.2 ∈ C) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w : ParameterCoefficientSpace n p ↦ f w.2.2) q‖ ≤
      ‖iteratedFDeriv ℝ j f q.2.2‖ := by
  exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (parameterCoefficientProjection n p) hC hf hq j).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (projection_norm_le n p)))

private theorem linear_jet_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (q : E) {j : ℕ} (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j L q‖ ≤ ‖L‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv (f := fun x ↦ L x) (n := j)]
  rw [show (fderiv ℝ (fun x ↦ L x)) = (fun _ ↦ L) from funext (fun x ↦ L.fderiv)]
  cases j with
  | zero => simp
  | succ j => simp [iteratedFDeriv_succ_const]

/-- Positive-order jets of the normalized nonlinear segment are controlled by
carrier jets alone (`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_parameterCoefficient_segment_jet_le {n p : ℕ}
    {ζ : Euclidean p → Euclidean n} {C : Set (Euclidean p)}
    (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C)
    {q : ParameterCoefficientSpace n p} (hq : q.2.2 ∈ C)
    {j : ℕ} (hj : 1 ≤ j) {M : ℝ} (hM : 0 ≤ M)
    (hb : ‖iteratedFDeriv ℝ j ζ q.2.2‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun w : ParameterCoefficientSpace n p ↦
      (w.1, ζ w.2.2 + t • w.2.1)) q‖ ≤ (1 + M) ^ j := by
  let Lx : ParameterCoefficientSpace n p →L[ℝ] Euclidean n :=
    ContinuousLinearMap.fst ℝ _ _
  let Le : ParameterCoefficientSpace n p →L[ℝ] Euclidean n :=
    t • (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean p)).comp
      (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean p))
  have hx : ‖Lx‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa [Lx] using norm_fst_le w
  have he : ‖Le‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change ‖t • w.2.1‖ ≤ 1 * ‖w‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans
      ((norm_fst_le w.2).trans (norm_snd_le w))
  have hz : ContDiffAt ℝ ∞ (fun w : ParameterCoefficientSpace n p ↦ ζ w.2.2) q :=
    (hζ.contDiffAt (hC.mem_nhds hq)).comp q contDiffAt_snd.snd
  have hl : ContDiffAt ℝ ∞ (fun w : ParameterCoefficientSpace n p ↦ t • w.2.1) q :=
    Le.contDiff.contDiffAt
  change ‖iteratedFDeriv ℝ j (fun w ↦ (Lx w, ζ w.2.2 + t • w.2.1)) q‖ ≤ _
  rw [iteratedFDeriv_prodMk (Lx.contDiff.contDiffAt) (hz.add hl) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  apply (max_le _ _).trans ((by simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + M) hj))
  · exact (linear_jet_le Lx q hj).trans (hx.trans (by linarith))
  · rw [fun_iteratedFDeriv_add_apply (hz.of_le (by simp)) (hl.of_le (by simp))]
    exact (norm_add_le _ _).trans (by
      have h1 := (norm_parameterCoefficient_pullback_le hC hζ hq j).trans hb
      have h2 := (linear_jet_le Le q hj).trans he
      change _ + ‖iteratedFDeriv ℝ j Le q‖ ≤ _
      linarith)

end JanetCartan.ResponseTransfer
