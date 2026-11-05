module

public import JanetCartan.Analysis.Sobolev.Local.Inclusion
public import JanetCartan.Analysis.Operator.SmallSupport

/-!
# From a local Sobolev gain to small-support contraction

The initial step of `app:ch_regular:thm:exact-correction`: a complete residual's
L²-to-H¹ bound gives a bounded Lᵖ output, with the same representative. The
embedding constant and cutoffs are uniform over all residuals with that bound.
The construction and one-derivative estimate of the actual residual are inputs
owned by the fixed-domain inverse assembly.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {U : Set (EuclideanSpace ℝ (Fin n))}

/-- Lift a bounded operator whose range and estimate lie in an actual Sobolev
level to that normed space (`app:ch_regular:thm:exact-correction`). -/
def liftToRestrictionSobolev (s : ℕ) (A : D →L[ℝ] LocalL2 U F)
    (hmem : ∀ f, MemRestrictionSobolev U s (A f)) (K : ℝ)
    (hbound : ∀ f, restrictionSobolevNorm U s (A f) ≤ K * ‖f‖) :
    D →L[ℝ] RestrictionSobolevSpace U F s := by
  let T : D →ₗ[ℝ] RestrictionSobolevSpace U F s :=
    { toFun := fun f ↦ RestrictionSobolevSpace.ofL2 s (A f) (hmem f)
      map_add' := fun f g ↦ by
        apply RestrictionSobolevSpace.toL2_injective s
        exact A.map_add f g
      map_smul' := fun a f ↦ by
        apply RestrictionSobolevSpace.toL2_injective s
        exact A.map_smul a f }
  exact T.mkContinuous K hbound

/-- The lift preserves the L² output (`app:ch_regular:thm:exact-correction`). -/
@[simp] theorem toL2_liftToRestrictionSobolev (s : ℕ) (A : D →L[ℝ] LocalL2 U F)
    (hmem : ∀ f, MemRestrictionSobolev U s (A f)) (K : ℝ)
    (hbound : ∀ f, restrictionSobolevNorm U s (A f) ≤ K * ‖f‖) (f : D) :
    RestrictionSobolevSpace.toL2 s (liftToRestrictionSobolev s A hmem K hbound f) = A f := rfl

/-- The lifted operator has the supplied Sobolev bound
(`app:ch_regular:thm:exact-correction`). -/
theorem liftToRestrictionSobolev_norm_le (s : ℕ) (A : D →L[ℝ] LocalL2 U F)
    (hmem : ∀ f, MemRestrictionSobolev U s (A f)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ f, restrictionSobolevNorm U s (A f) ≤ K * ‖f‖) :
    ‖liftToRestrictionSobolev s A hmem K hbound‖ ≤ K :=
  ContinuousLinearMap.opNorm_le_bound _ hK hbound

variable [FiniteDimensional ℝ F]

/-- Turn a complete residual's one-derivative bound into its Lᵖ realization
(`app:ch_regular:thm:exact-correction`). -/
def oneGainToLpBall (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (A : D →L[ℝ] LocalL2 (ball c R) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c R) 1 (A f)) (K : ℝ)
    (hbound : ∀ f, restrictionSobolevNorm (ball c R) 1 (A f) ≤ K * ‖f‖) :
    D →L[ℝ] Lp F (ballSobolevExponent F c hR) (volume.restrict (ball c R)) :=
  (RestrictionSobolevSpace.toLpBall c hR).comp (liftToRestrictionSobolev 1 A hmem K hbound)

/-- The Lᵖ realization agrees with the complete residual's L² output
(`app:ch_regular:thm:exact-correction`). -/
theorem oneGainToLpBall_coeFn (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (A : D →L[ℝ] LocalL2 (ball c R) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c R) 1 (A f)) (K : ℝ)
    (hbound : ∀ f, restrictionSobolevNorm (ball c R) 1 (A f) ≤ K * ‖f‖) (f : D) :
    oneGainToLpBall c hR A hmem K hbound f =ᵐ[volume.restrict (ball c R)] A f :=
  RestrictionSobolevSpace.toLpBall_coeFn c hR _

/-- The exact quantitative input to small-support localization: the Sobolev
embedding constant times the one-gain constant
(`app:ch_regular:thm:exact-correction`). -/
theorem oneGainToLpBall_norm_le (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (A : D →L[ℝ] LocalL2 (ball c R) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c R) 1 (A f)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ f, restrictionSobolevNorm (ball c R) 1 (A f) ≤ K * ‖f‖) :
    ‖oneGainToLpBall c hR A hmem K hbound‖ ≤ ballSobolevEmbeddingConstant F c hR * K :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (RestrictionSobolevSpace.toLpBall_norm_le c hR)
      (liftToRestrictionSobolev_norm_le 1 A hmem hK hbound) (norm_nonneg _)
      (ballSobolevEmbeddingConstant_pos c hR).le)

/-- The same Lᵖ realization in the nested restricted measure expected by
`SmallSupport.exists_local_cutoffs_norm_lt`, with ambient space L²(W)
(`app:ch_regular:thm:exact-correction`). -/
theorem exists_lp_residual_ball (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hUW : ball c R ⊆ W)
    (A : LocalL2 W F →L[ℝ] LocalL2 (ball c R) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c R) 1 (A f)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ f, restrictionSobolevNorm (ball c R) 1 (A f) ≤ K * ‖f‖) :
    ∃ T : LocalL2 W F →L[ℝ]
      Lp F (ballSobolevExponent F c hR) ((volume.restrict W).restrict (ball c R)),
      (∀ f, T f =ᵐ[volume.restrict (ball c R)] A f) ∧
        ‖T‖ ≤ ballSobolevEmbeddingConstant F c hR * K := by
  rw [Measure.restrict_restrict_of_subset hUW]
  exact ⟨oneGainToLpBall c hR A hmem K hbound,
    oneGainToLpBall_coeFn c hR A hmem K hbound,
    oneGainToLpBall_norm_le c hR A hmem hK hbound⟩

/-- A uniform H¹ bound permits one cutoff choice for all complete residuals
with that bound (`app:ch_regular:thm:exact-correction`). Positive dimension is
needed for arbitrarily small volume supports; the embedding itself also holds
in dimension zero. The actual residual's one-gain estimate remains an input. -/
theorem exists_local_cutoffs_of_one_gain_ball (hn : 0 < n)
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hUW : ball c R ⊆ W)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball c R) {K : ℝ} (hK : 0 ≤ K)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ ball c R ∧
      tsupport (χ₃ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ ball c R ∧
      (∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1) ∧
      ∀ A : LocalL2 W F →L[ℝ] LocalL2 (ball c R) F,
        (∀ f, MemRestrictionSobolev (ball c R) 1 (A f)) →
        (∀ f, restrictionSobolevNorm (ball c R) 1 (A f) ≤ K * ‖f‖) →
        ∃ T : LocalL2 W F →L[ℝ]
          Lp F (ballSobolevExponent F c hR) ((volume.restrict W).restrict (ball c R)),
          (∀ f, T f =ᵐ[volume.restrict (ball c R)] A f) ∧
          ‖T‖ ≤ ballSobolevEmbeddingConstant F c hR * K ∧
          ‖SmallSupport.localizedResidual (two_lt_ballSobolevExponent c hR).le
            χ₂ χ₃ isOpen_ball.measurableSet T‖ < θ := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨χ₂, χ₃, h₂, h₃, hnest, hsmall⟩ :=
    SmallSupport.exists_local_cutoffs_norm_lt (F := F) (μ := volume.restrict W)
      (two_lt_ballSobolevExponent (F := F) c hR) isOpen_ball hx
      (ballSobolevEmbeddingConstant F c hR * K) hθ
  refine ⟨χ₂, χ₃, h₂, h₃, hnest, fun A hmem hbound ↦ ?_⟩
  obtain ⟨T, heq, hT⟩ := exists_lp_residual_ball c hR hUW A hmem hK hbound
  exact ⟨T, heq, hT, hsmall T hT⟩

end JanetCartan.LocalSobolev
