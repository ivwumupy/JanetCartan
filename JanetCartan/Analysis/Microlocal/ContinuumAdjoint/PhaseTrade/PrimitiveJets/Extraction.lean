module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.Literal
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Recovering the rectangular inputs from the pulled-back phase gradient

For `app:ch_background:eq:bg-derivative-trade`, the actual pair `(A, D_z Y)`
is a fixed linear evaluation of the derivative of the pulled-back full phase
gradient. The resulting compact-set estimate includes order zero and retains
all carrier derivatives. Its consumer is the primitive one-high estimate in
`PrimitiveJets`; the additive composition bound remains a separate obligation.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint
variable {n p : ℕ}
/-- The full primitive phase gradient evaluated on the carrier graph, for
`app:ch_background:eq:bg-derivative-trade`. -/
def transversePhaseGradientPullback
    (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean p → Euclidean (n - 1)) (q : Euclidean n × Euclidean p) :
    (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ :=
  fderiv ℝ (Function.uncurry S) (q.1, ζ q.2)

/-- Fixed physical and carrier evaluations of a differentiated phase gradient.
This operation constructs the actual inputs of
`app:ch_background:eq:bg-derivative-trade`. -/
def transversePhaseJetExtraction :
    ((Euclidean n × Euclidean p) →L[ℝ]
      (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ) →L[ℝ]
      TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ :=
  let L : ((Euclidean n × Euclidean p) →L[ℝ]
      (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ) →ₗ[ℝ]
      TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ := {
    toFun := fun (D : (Euclidean n × Euclidean p) →L[ℝ]
      (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ) ↦
      (fun i j ↦ D (EuclideanSpace.single i 1, 0) (0, EuclideanSpace.single j 1),
       fun l j ↦ D (0, EuclideanSpace.single l 1) (0, EuclideanSpace.single j 1))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := (Euclidean n × Euclidean p) →L[ℝ]
      (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ)
    (F' := TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ) L

/-- Smoothness of the pulled-back primitive gradient in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiff_transversePhaseGradientPullback
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (transversePhaseGradientPullback S ζ) :=
  (hS.fderiv_right (by simp)).comp (contDiff_fst.prodMk (hζ.comp contDiff_snd))

/-- The literal footpoint is a fixed component of the pulled-back gradient;
source: `app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseFootpoint_eq_gradientPullback
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    (ζ : Euclidean p → Euclidean (n - 1))
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (q : Euclidean n × Euclidean p)
    (j : Fin (n - 1)) :
    transverseFootpoint S ζ q.1 q.2 j =
      transversePhaseGradientPullback S ζ q (0, EuclideanSpace.single j 1) := by
  have h := ((hS.differentiable (by simp)).differentiableAt.hasFDerivAt.comp (ζ q.2)
    (hasFDerivAt_prodMk_right q.1 (ζ q.2))).fderiv
  exact congrArg (fun L : Euclidean (n - 1) →L[ℝ] ℝ ↦ L (EuclideanSpace.single j 1)) h

/-- Both actual rectangular inputs come from one derivative of the pulled-back
primitive gradient. Physical mixed derivatives commute by the checked phase
identity, and the carrier derivative retains its Jacobian. Source:
`app:ch_background:eq:bg-derivative-trade`. -/
theorem transversePhaseInputs_eq_gradientPullback_derivative
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {ζ : Euclidean p → Euclidean (n - 1)}
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) (hζ : ContDiff ℝ ∞ ζ) :
    transversePhaseInputs S ζ =
      transversePhaseJetExtraction ∘ fderiv ℝ (transversePhaseGradientPullback S ζ) := by
  have hg := contDiff_transversePhaseGradientPullback hS hζ
  have hY (j : Fin (n - 1)) :
      (fun q : Euclidean n × Euclidean p ↦ transverseFootpoint S ζ q.1 q.2 j) =
      (fun q ↦ transversePhaseGradientPullback S ζ q (0, EuclideanSpace.single j 1)) := by
    funext q
    exact transverseFootpoint_eq_gradientPullback ζ hS q j
  have hd (q : Euclidean n × Euclidean p) (j : Fin (n - 1)) :
      HasFDerivAt (fun q : Euclidean n × Euclidean p ↦ transverseFootpoint S ζ q.1 q.2 j)
        ((ContinuousLinearMap.apply ℝ ℝ (0, EuclideanSpace.single j 1)).comp
          (fderiv ℝ (transversePhaseGradientPullback S ζ) q)) q := by
    rw [hY]
    exact (ContinuousLinearMap.apply ℝ ℝ (0, EuclideanSpace.single j 1)).hasFDerivAt.comp q
      (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  funext q
  apply Prod.ext
  · funext i j
    have hphys := partialDeriv_transverseTransportPhase_physical (x := q.1) ζ q.2
      (hS.contDiffAt.of_le (by norm_num)) (EuclideanSpace.single j 1) i
    have hslice := ((hd q j).comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)).fderiv
    have heval := congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hslice
    change transversePhaseMatrix S q.1 (ζ q.2) i j = _
    have hphys' : partialDeriv (fun x ↦ transverseFootpoint S ζ x q.2 j) q.1 i =
        transversePhaseMatrix S q.1 (ζ q.2) i j := by
      simpa [transverseTransportPhase, transverseFootpoint, partialDeriv,
        Matrix.mulVec, dotProduct, PiLp.single_apply] using hphys
    rw [← hphys']
    exact heval
  · funext l j
    have hslice := ((hd q j).comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
    exact congrArg (fun L : Euclidean p →L[ℝ] ℝ ↦ L (EuclideanSpace.single l 1)) hslice
private theorem cNorm_linear_fderiv_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (E →L[ℝ] F) →L[ℝ] G) {K : Set E} (hK : IsCompact K)
    (k : ℕ) {f : E → F} (hf : ContDiff ℝ ∞ f) :
    cNorm K k (L ∘ fderiv ℝ f) ≤
      ((k + 1 : ℕ) : ℝ) * ‖L‖ * cNorm K (k + 1) f := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := cNorm_le_sum_of_bounds (s := K) (r := k)
    (C := fun _ ↦ ‖L‖ * cNorm K (k + 1) f)
    (fun _ _ ↦ mul_nonneg (norm_nonneg L) (cNorm_nonneg K (k + 1) f)) (by
      intro j hj x hx
      rw [L.iteratedFDeriv_comp_left hd.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞)]
      apply L.norm_compContinuousMultilinearMap_le _ |>.trans
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_le_cNorm hK (contDiff_infty.mp hf (k + 1)) hx
          (Nat.add_le_add_right hj 1)) (norm_nonneg L))
  simpa [Finset.sum_const, mul_assoc] using hb

private theorem exists_cNorm_linear_fderiv_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (E →L[ℝ] F) →L[ℝ] G) (k : ℕ) :
    ∃ C > 0, ∀ (K : Set E), IsCompact K → ∀ (f : E → F), ContDiff ℝ ∞ f →
      cNorm K k (L ∘ fderiv ℝ f) ≤ C * cNorm K (k + 1) f := by
  refine ⟨((k + 1 : ℕ) : ℝ) * ‖L‖ + 1, by positivity, ?_⟩
  intro K hK f hf
  exact (cNorm_linear_fderiv_le L hK k hf).trans
    (mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg K (k + 1) f))

/-- Uniform compact-set reduction of the rectangular input jets to the
pulled-back primitive gradient, including `k = 0`. The constant depends only on
dimensions and order. The consuming primitive estimate must still bound that
gradient composition by the additive primitive high budget. Source:
`app:ch_background:eq:bg-derivative-trade`. -/
theorem exists_cNorm_transversePhaseInputs_le_gradientPullback (n p k : ℕ) :
    ∃ C > 0, ∀ (K : Set (Euclidean n × Euclidean p)), IsCompact K →
      ∀ (S : Euclidean n → Euclidean (n - 1) → ℝ)
        (ζ : Euclidean p → Euclidean (n - 1)),
      ContDiff ℝ ∞ (Function.uncurry S) → ContDiff ℝ ∞ ζ →
      cNorm K k (fun q ↦ transversePhaseMatrix S q.1 (ζ q.2)) +
        cNorm K k (transversePhaseInputs S ζ) ≤
        C * cNorm K (k + 1) (transversePhaseGradientPullback S ζ) := by
  let L : ((Euclidean n × Euclidean p) →L[ℝ]
      (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ) →L[ℝ]
      TransverseMatrix n × Matrix (Fin p) (Fin (n - 1)) ℝ := transversePhaseJetExtraction (n := n) (p := p)
  let A : ((Euclidean n × Euclidean p) →L[ℝ]
      (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ) →L[ℝ]
      TransverseMatrix n := (ContinuousLinearMap.fst ℝ (TransverseMatrix n)
    (Matrix (Fin p) (Fin (n - 1)) ℝ)).comp L
  obtain ⟨CA, hCA, hA⟩ := exists_cNorm_linear_fderiv_le A k
  obtain ⟨CL, hCL, hL⟩ := exists_cNorm_linear_fderiv_le L k
  refine ⟨CA + CL, add_pos hCA hCL, ?_⟩
  intro K hK S ζ hS hζ
  have hg := contDiff_transversePhaseGradientPullback hS hζ
  have hinput := transversePhaseInputs_eq_gradientPullback_derivative hS hζ
  have hmatrix : (fun q ↦ transversePhaseMatrix S q.1 (ζ q.2)) =
      A ∘ fderiv ℝ (transversePhaseGradientPullback S ζ) := by
    funext q
    exact congrArg Prod.fst (congrFun hinput q)
  rw [hmatrix, hinput]
  set_option backward.isDefEq.respectTransparency false in
    simpa only [add_mul, L] using add_le_add (hA K hK _ hg) (hL K hK _ hg)
end JanetCartan.ContinuumAdjoint
