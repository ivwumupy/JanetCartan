module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.PhaseJets.Identification

/-!
# Reserve-graded jets of the actual phase Hessians

For `app:ch_response:eq:direct-envelope-profile`, primitive joint phase jets
through `N + 2` give joint mixed-matrix and covector-Hessian jets through `N`.
The exact exponent is `j + 2 - Rstar`, with natural subtraction. The mixed
matrix uses the Frobenius norm with the explicit fixed dimension factor `n`.

The consumers are `GradedPrimitives.norm_jet_averagedMixed_inverse_le` and
the parameter-coefficient deduction. The response geometry must still produce
the raw normalized phase profile on the open buffered product. These proofs
are local to that chart and require no smooth extension through zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

local instance phaseJetBoundMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

private theorem norm_jet_fixed_linear_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : F →L[ℝ] G) {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v, ‖T v‖ ≤ C * ‖v‖) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (T ∘ f) x‖ ≤ C * ‖iteratedFDeriv ℝ j f x‖ := by
  exact (T.norm_iteratedFDeriv_comp_left hf (by simp)).trans
    (mul_le_mul_of_nonneg_right (T.opNorm_le_bound hC hT) (norm_nonneg _))

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {X D : Set (Euclidean n)}

/-- Joint smoothness of the literal mixed matrix on the buffered annular
chart (`app:ch_response:eq:direct-envelope-profile`). -/
theorem mixedPhaseMatrix_contDiffOn_of_phase
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D) := by
  have hh := (hS.fderiv_of_isOpen (hX.prod hD) (m := ∞) (by simp)).fderiv_of_isOpen
    (hX.prod hD) (m := ∞) (by simp)
  have hc : ContDiffOn ℝ ∞
      (mixedHessianContraction n ∘ fderiv ℝ (fderiv ℝ (Function.uncurry S))) (X ×ˢ D) :=
    (mixedHessianContraction n).contDiff.comp_contDiffOn hh
  exact hc.congr
    (fun q hq ↦ mixedPhaseMatrix_eq_jointHessian_contraction hX hD hS hq)

/-- Joint smoothness of the actual covector Hessian used by the parameter
coefficient (`app:ch_response:eq:direct-envelope-profile`). -/
theorem covectorHessian_contDiffOn_of_phase
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D)) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean n ↦
      fderiv ℝ (fderiv ℝ (S q.1)) q.2) (X ×ˢ D) := by
  have hh := (hS.fderiv_of_isOpen (hX.prod hD) (m := ∞) (by simp)).fderiv_of_isOpen
    (hX.prod hD) (m := ∞) (by simp)
  have hc : ContDiffOn ℝ ∞
      (covectorHessianContraction n ∘ fderiv ℝ (fderiv ℝ (Function.uncurry S))) (X ×ˢ D) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ)
      (F := Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ)
      (covectorHessianContraction n)).comp_contDiffOn hh
  exact hc.congr
    (fun q hq ↦ covectorHessian_eq_jointHessian_contraction hX hD hS hq)

/-- Every joint mixed-matrix jet is controlled by exactly two more joint
phase derivatives. The constant is the Frobenius dimension factor, without
any assumed partial-Hessian estimate (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_mixedPhaseMatrix_le_phase
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (j : ℕ) {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
      (n : ℝ) * ‖iteratedFDeriv ℝ (j + 2) (Function.uncurry S) q‖ := by
  have he : EqOn (Function.uncurry (FourierIntegral.mixedPhaseMatrix S))
      (mixedHessianContraction n ∘ fderiv ℝ (fderiv ℝ (Function.uncurry S))) (X ×ˢ D) :=
    fun w hw ↦ mixedPhaseMatrix_eq_jointHessian_contraction hX hD hS hw
  have hj := iteratedFDerivWithin_congr (𝕜 := ℝ) he hq j
  rw [iteratedFDerivWithin_of_isOpen j (hX.prod hD) hq,
    iteratedFDerivWithin_of_isOpen j (hX.prod hD) hq] at hj
  rw [hj]
  have hh := ((hS.contDiffAt ((hX.prod hD).mem_nhds hq)).fderiv_right
    (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hb := norm_jet_fixed_linear_le (mixedHessianContraction n) hh (Nat.cast_nonneg n)
    (fun H ↦ norm_mixedHessianContraction_apply_le H) j
  simpa only [norm_iteratedFDeriv_fderiv] using hb

/-- Every joint covector-Hessian jet costs exactly two primitive phase
orders and no dimension factor (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_covectorHessian_le_phase
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (j : ℕ) {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ j (fun w : Euclidean n × Euclidean n ↦
      fderiv ℝ (fderiv ℝ (S w.1)) w.2) q‖ ≤
        ‖iteratedFDeriv ℝ (j + 2) (Function.uncurry S) q‖ := by
  have he : EqOn (fun w : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S w.1)) w.2)
      (covectorHessianContraction n ∘ fderiv ℝ (fderiv ℝ (Function.uncurry S))) (X ×ˢ D) :=
    fun w hw ↦ covectorHessian_eq_jointHessian_contraction hX hD hS hw
  have hj := iteratedFDerivWithin_congr (𝕜 := ℝ) he hq j
  rw [iteratedFDerivWithin_of_isOpen j (hX.prod hD) hq,
    iteratedFDerivWithin_of_isOpen j (hX.prod hD) hq] at hj
  rw [hj]
  have hh := ((hS.contDiffAt ((hX.prod hD).mem_nhds hq)).fderiv_right
    (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hb := norm_jet_fixed_linear_le
    (F := (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ)
    (G := Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ)
    (covectorHessianContraction n) hh (C := 1) zero_le_one
    (fun H ↦ by simpa only [one_mul] using norm_covectorHessianContraction_apply_le H) j
  simpa only [norm_iteratedFDeriv_fderiv, one_mul] using hb

/-- The mixed-matrix profile consumed by the averaged mixed inverse, with
the exact two-derivative reserve shift from the raw phase profile
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_mixedPhaseMatrix_graded_le
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {N j Rstar : ℕ} {A : ℕ → ℝ} {L : ℝ}
    (hSjet : ∀ k ≤ N + 2, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ k (Function.uncurry S) w‖ ≤ A k * L ^ (k - Rstar))
    (hj : j ≤ N) {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
      ((n : ℝ) * A (j + 2)) * L ^ (j + 2 - Rstar) := by
  exact (norm_jet_mixedPhaseMatrix_le_phase hX hD hS j hq).trans
    (by simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hSjet (j + 2) (by omega) q hq) (Nat.cast_nonneg n)))

/-- The corresponding covector-Hessian profile for the parameter coefficient
(`app:ch_response:eq:direct-envelope-profile`). No partial jets are inputs. -/
theorem norm_jet_covectorHessian_graded_le
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {N j Rstar : ℕ} {A : ℕ → ℝ} {L : ℝ}
    (hSjet : ∀ k ≤ N + 2, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ k (Function.uncurry S) w‖ ≤ A k * L ^ (k - Rstar))
    (hj : j ≤ N) {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ j (fun w : Euclidean n × Euclidean n ↦
      fderiv ℝ (fderiv ℝ (S w.1)) w.2) q‖ ≤ A (j + 2) * L ^ (j + 2 - Rstar) :=
  (norm_jet_covectorHessian_le_phase hX hD hS j hq).trans
    (hSjet (j + 2) (by omega) q hq)

/-- The mixed profile in the reserve convention of
`norm_jet_averagedMixed_inverse_le`, with `R = Rstar - 2`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_mixedPhaseMatrix_reserve_le
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {N j Rstar : ℕ} {A : ℕ → ℝ} {L : ℝ} (hR : 2 ≤ Rstar)
    (hSjet : ∀ k ≤ N + 2, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ k (Function.uncurry S) w‖ ≤ A k * L ^ (k - Rstar))
    (hj : j ≤ N) {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
      ((n : ℝ) * A (j + 2)) * L ^ (j - (Rstar - 2)) := by
  rw [reserve_exponent hR]
  exact norm_jet_mixedPhaseMatrix_graded_le hX hD hS hSjet hj hq

/-- The parameter Hessian profile in the common primitive reserve convention
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_covectorHessian_reserve_le
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {N j Rstar : ℕ} {A : ℕ → ℝ} {L : ℝ} (hR : 2 ≤ Rstar)
    (hSjet : ∀ k ≤ N + 2, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ k (Function.uncurry S) w‖ ≤ A k * L ^ (k - Rstar))
    (hj : j ≤ N) {q : Euclidean n × Euclidean n} (hq : q ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ j (fun w : Euclidean n × Euclidean n ↦
      fderiv ℝ (fderiv ℝ (S w.1)) w.2) q‖ ≤ A (j + 2) * L ^ (j - (Rstar - 2)) := by
  rw [reserve_exponent hR]
  exact norm_jet_covectorHessian_graded_le hX hD hS hSjet hj hq

end JanetCartan.ResponseTransfer.GradedPrimitives
