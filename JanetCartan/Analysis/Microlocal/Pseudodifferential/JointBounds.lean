module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.RemainderBounds

/-!
# Joint derivative bounds for the diagonal Taylor coefficient

Fixed derivative budgets retaining both physical positions and the source mask
in `app:ch_regular_base:eq:actual-pdo-remainder`.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
namespace JanetCartan.Pseudodifferential
variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: linear substitutions preserve the
primitive derivative order, with their operator norm explicit. -/
theorem norm_iteratedFDeriv_comp_linear_le (L : D →L[ℝ] E) (f : E → F) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : D) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖ ^ n := by
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  simpa using (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ ↦ L)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: restricting a derivative to a fixed
linear coordinate direction costs exactly one primitive derivative. -/
theorem norm_iteratedFDeriv_partialFDeriv_le (L : D →L[ℝ] E) (f : E → F) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun q ↦ (fderiv ℝ f q).comp L) x‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  let A : (E →L[ℝ] F) →L[ℝ] D →L[ℝ] F := (ContinuousLinearMap.compL ℝ D E F).flip L
  have hA : ‖A‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    simpa [A, mul_comm] using B.opNorm_comp_le L
  have hD := hf.fderiv_right (m := ∞) (by simp)
  change ‖iteratedFDeriv ℝ n (A ∘ fderiv ℝ f) x‖ ≤ _
  apply (A.norm_iteratedFDeriv_comp_left hD.contDiffAt (by simp)).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)


section Coordinates
variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the inclusion of the source direction. -/
def sourceCoordinateInclusion : V →L[ℝ] V × V × V :=
  (0 : V →L[ℝ] V).prod ((ContinuousLinearMap.id ℝ V).prod 0)
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the inclusion of the frequency direction. -/
def frequencyCoordinateInclusion : V →L[ℝ] V × V × V :=
  (0 : V →L[ℝ] V).prod ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V))
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the linear substitution along the source segment. -/
def sourceSegmentMap (t : ℝ) : (V × V × V) →L[ℝ] V × V × V :=
  let X := ContinuousLinearMap.fst ℝ V (V × V)
  let Y := (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  let Ξ := (ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  X.prod (((1 - t) • X + t • Y).prod Ξ)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the coordinate substitution
retains the full primitive derivative budget. -/
theorem norm_sourceCoordinateInclusion_le : ‖sourceCoordinateInclusion (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [sourceCoordinateInclusion, Prod.norm_def]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the coordinate substitution
retains the full primitive derivative budget. -/
theorem norm_frequencyCoordinateInclusion_le : ‖frequencyCoordinateInclusion (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [frequencyCoordinateInclusion, Prod.norm_def]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the coordinate substitution
retains the full primitive derivative budget. -/
theorem norm_sourceSegmentMap_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖sourceSegmentMap (V := V) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  have hx : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have hy : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
  have hξ : ‖p.2.2‖ ≤ ‖p‖ := (norm_snd_le p.2).trans (norm_snd_le p)
  change ‖(p.1, (1 - t) • p.1 + t • p.2.1, p.2.2)‖ ≤ 1 * ‖p‖
  rw [one_mul, Prod.norm_def, Prod.norm_def]
  refine max_le hx (max_le ?_ hξ)
  calc
    _ ≤ ‖(1 - t) • p.1‖ + ‖t • p.2.1‖ := norm_add_le _ _
    _ = (1 - t) * ‖p.1‖ + t * ‖p.2.1‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    _ ≤ (1 - t) * ‖p‖ + t * ‖p‖ := by gcongr <;> linarith [ht.1, ht.2]
    _ = ‖p‖ := by ring

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the coordinate substitution
retains the full primitive derivative budget. -/
theorem fderiv_source_eq_joint (c : V → V → V → F) (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (p : V × V × V) :
    fderiv ℝ (fun z ↦ c p.1 z p.2.2) p.2.1 =
      (fderiv ℝ (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2) p).comp
        sourceCoordinateInclusion := by
  have hi : HasFDerivAt (fun z : V ↦ (p.1, z, p.2.2))
      sourceCoordinateInclusion p.2.1 :=
    (hasFDerivAt_const p.1 p.2.1).prodMk
      ((hasFDerivAt_id p.2.1).prodMk (hasFDerivAt_const p.2.2 p.2.1))
  exact ((hc.differentiable (by simp) p).hasFDerivAt.comp p.2.1 hi).fderiv
end Coordinates


section JointSource
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: joint smoothness of the source derivative. -/
theorem contDiff_jointSourceDerivative (c : V → V → V → F)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞ (fun p : V × V × V ↦ fderiv ℝ (fun z ↦ c p.1 z p.2.2) p.2.1) := by
  simp_rw [fderiv_source_eq_joint c hc]
  exact (hc.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the source-segment integrand is jointly smooth. -/
theorem contDiff_jointSourceIntegrand (c : V → V → V → F)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞ (fun q : (V × V × V) × ℝ ↦
      fderiv ℝ (fun z ↦ c q.1.1 z q.1.2.2) ((1 - q.2) • q.1.1 + q.2 • q.1.2.1)) := by
  exact (contDiff_jointSourceDerivative c hc).comp
    (contDiff_fst.fst.prodMk ((((contDiff_const.sub contDiff_snd).smul contDiff_fst.fst).add
      (contDiff_snd.smul contDiff_fst.snd.fst)).prodMk contDiff_fst.snd.snd))

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: all joint derivatives of the Taylor
integrand are bounded by exactly one more derivative of the primitive amplitude. -/
theorem norm_iteratedFDeriv_jointSourceIntegrand_le (c : V → V → V → F)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (p : V × V × V) (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦
      fderiv ℝ (fun z ↦ c q.1 z q.2.2) ((1 - t) • q.1 + t • q.2.1)) p‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2)
        (sourceSegmentMap t p)‖ := by
  let d := fun q : V × V × V ↦ fderiv ℝ (fun z ↦ c q.1 z q.2.2) q.2.1
  change ‖iteratedFDeriv ℝ n (d ∘ sourceSegmentMap t) p‖ ≤ _
  have hd := contDiff_jointSourceDerivative c hc
  have h₁ := norm_iteratedFDeriv_comp_linear_le (sourceSegmentMap t) d hd n p
  have h₂ : ‖iteratedFDeriv ℝ n d (sourceSegmentMap t p)‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2)
        (sourceSegmentMap t p)‖ := by
    dsimp [d]
    simp_rw [fderiv_source_eq_joint c hc]
    exact (norm_iteratedFDeriv_partialFDeriv_le (sourceCoordinateInclusion (V := V)) (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2) hc n (sourceSegmentMap t p)).trans
      (mul_le_of_le_one_left (norm_nonneg _) norm_sourceCoordinateInclusion_le)
  exact h₁.trans ((mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_sourceSegmentMap_le t ht))).trans h₂)
end JointSource
end JanetCartan.Pseudodifferential
