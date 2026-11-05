module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.Integration
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Realization.Amplitude
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Normal

/-!
# Conversion to the finite graph-normal amplitude interface

This is the downstream conversion for `app:ch_background:prop:bg-adjoint`.
The density-jet bound used here must be supplied by a primitive half-order
symbol calculation. This conditional conversion does not supply that bound.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow ContinuumNormal Pseudodifferential AmplitudeBound FourierIntegral

variable {n : ℕ}

/-- The fixed position inclusion for the normal in
`app:ch_background:prop:bg-adjoint`, reusing the established physical projections. -/
def positionInclusion : Euclidean (2 * n) →L[ℝ] Variables n :=
  freezingOutputProjection.prod (freezingSourceProjection.prod 0)

/-- The normalized scalar amplitude in the consumer's paired Euclidean
coordinates (`app:ch_background:prop:bg-adjoint`). -/
def positionAmplitude (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (ξ : Euclidean n) (z : Euclidean (2 * n)) : ℂ :=
  cyclesAmplitude g a m (freezingOutputProjection z, freezingSourceProjection z, ξ)

/-- A scalar normal as an actual one-by-one matrix for the checked graph
normal estimate (`app:ch_background:prop:bg-adjoint`). -/
def matrixAmplitude (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (ξ : Euclidean n) (z : Euclidean (2 * n)) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _ ↦ positionAmplitude g a m ξ z

/-- The constant used only for integration, normalization, and the fixed
position inclusion in `app:ch_background:prop:bg-adjoint`. -/
def graphJetFactor (n : ℕ) (K : Set (Euclidean 2)) : ℝ :=
  (2 * Real.pi) ^ n * volume.real K *
    (max 1 ‖positionInclusion (n := n)‖) ^ (2 * (n + 1))

/-- The downstream conversion costs a nonnegative fixed constant
(`app:ch_background:prop:bg-adjoint`). -/
theorem graphJetFactor_nonneg (K : Set (Euclidean 2)) : 0 ≤ graphJetFactor n K := by
  unfold graphJetFactor
  positivity

/-- Joint smoothness in the exact consumer coordinates
(`app:ch_background:prop:bg-adjoint`). -/
theorem positionAmplitude_contDiff {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) :
    ContDiff ℝ ∞ (Function.uncurry (positionAmplitude g a m)) :=
  (cyclesAmplitude_contDiff h hb hs).comp
    ((freezingOutputProjection.contDiff.comp contDiff_snd).prodMk
      ((freezingSourceProjection.contDiff.comp contDiff_snd).prodMk contDiff_fst))

/-- A density jet bound gives the finite position jet bound after literal
integration and normalization. The primitive-jet producer must discharge
`hjet`; this is not the primitive symbol theorem
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_iteratedFDeriv_positionAmplitude_le {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) {B : ℝ} (hB : 0 ≤ B)
    (hjet : ∀ j ≤ 2 * (n + 1), ∀ p : Variables n, ∀ v ∈ K,
      ‖iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p‖ ≤ B)
    (ξ : Euclidean n) (j : ℕ) (hj : j ≤ 2 * (n + 1)) (z : Euclidean (2 * n)) :
    ‖iteratedFDeriv ℝ j (positionAmplitude g a m ξ) z‖ ≤ graphJetFactor n K * B := by
  let f := physicalAmplitude g a m
  let w : Variables n := (0, 0, (2 * Real.pi) • ξ)
  let F : Euclidean (2 * n) → ℂ := fun z ↦ f (w + positionInclusion z)
  have hf : ContDiff ℝ ∞ f := physicalAmplitude_contDiff h hb hs
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_const.add positionInclusion.contDiff)
  have hcomp := norm_iteratedFDeriv_comp_linear_le positionInclusion
    (fun p ↦ f (w + p)) (hf.comp (contDiff_const.add contDiff_id)) j z
  simp only [iteratedFDeriv_comp_add_left'] at hcomp
  have hbound : ‖iteratedFDeriv ℝ j F z‖ ≤
      (B * volume.real K) * ‖positionInclusion (n := n)‖ ^ j :=
    hcomp.trans (mul_le_mul_of_nonneg_right
      (norm_iteratedFDeriv_physicalAmplitude_le h hb hs j _ (hjet j hj _)) (by positivity))
  have he : positionAmplitude g a m ξ = fun z ↦ (2 * Real.pi) ^ n • F z := by
    funext z
    simp [positionAmplitude, cyclesAmplitude, F, f, w, positionInclusion, Complex.real_smul]
  rw [he, iteratedFDeriv_const_smul_apply' (hF.of_le (by simp)).contDiffAt, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ n)]
  apply (mul_le_mul_of_nonneg_left hbound (by positivity)).trans
  have hp : ‖positionInclusion (n := n)‖ ^ j ≤
      (max 1 ‖positionInclusion (n := n)‖) ^ (2 * (n + 1)) := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  calc
    _ ≤ (2 * Real.pi) ^ n * ((B * volume.real K) *
        (max 1 ‖positionInclusion (n := n)‖) ^ (2 * (n + 1))) := by
      gcongr
    _ = graphJetFactor n K * B := by unfold graphJetFactor; ring

/-- The complete one-by-one matrix satisfies the checked graph-normal
interface once its density jets have been derived. The only additional
premise is explicitly retained for the parent primitive-jet assembly
(`app:ch_background:prop:bg-adjoint`). -/
theorem graphNormalAmplitudeBounds_of_densityJets {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) {R B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ x ∈ X, ∀ i, |x i| ≤ R)
    (hjet : ∀ j ≤ 2 * (n + 1), ∀ p : Variables n, ∀ v ∈ K,
      ‖iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p‖ ≤ B) :
    GraphNormalAmplitudeBounds (matrixAmplitude g a m) R (graphJetFactor n K * B) := by
  constructor
  · let I : ℂ →L[ℝ] Matrix (Fin 1) (Fin 1) ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun c _ _ ↦ c
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact I.contDiff.comp (positionAmplitude_contDiff h hb hs)
  · intro ξ i j z hz l
    have hx : freezingOutputProjection z ∈ X := by
      by_contra hx
      exact hz (cyclesAmplitude_eq_zero_of_not_mem_measurement g a m hs _ (Or.inl hx))
    have hy : freezingSourceProjection z ∈ X := by
      by_contra hy
      exact hz (cyclesAmplitude_eq_zero_of_not_mem_measurement g a m hs _ (Or.inr hy))
    by_cases hl : l.val < n
    · exact hX _ hx ⟨l.val, hl⟩
    · simpa [freezingSourceProjection, show n + (l.val - n) = l.val by omega] using
        hX _ hy ⟨l.val - n, by omega⟩
  · intro ξ is hi z
    simp only [Matrix.frobenius_norm_def, matrixAmplitudeCoordinateDerivList,
      matrixAmplitude, Fin.sum_univ_one, Real.rpow_two, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq_eq_abs, abs_norm]
    exact (norm_euclideanCoordinateDerivList_le_iteratedFDeriv
      ((positionAmplitude_contDiff h hb hs).comp (contDiff_const.prodMk contDiff_id)) is z).trans
      (norm_iteratedFDeriv_positionAmplitude_le h hb hs hB hjet ξ is.length hi z)

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
