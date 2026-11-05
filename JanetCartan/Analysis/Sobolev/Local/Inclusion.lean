module

public import JanetCartan.Analysis.Sobolev.Local.Scale
public import JanetCartan.Analysis.Sobolev.Local.Embedding

/-!
# The bounded local H¹-to-Lᵖ inclusion

For `app:ch_regular:thm:exact-correction`, choose one finite exponent above two
on each ball and realize the proved weak Sobolev estimate as a bounded linear
inclusion. The resulting Lᵖ class agrees with the original L² class.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open scoped NNReal ENNReal

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A finite Sobolev exponent for the ball, including dimensions zero, one,
and two (`app:ch_regular:thm:exact-correction`). -/
def ballSobolevExponent (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) : ℝ≥0 :=
  (exists_memLp_and_norm_le_restrictionSobolevNorm_ball (F := F) c hR).choose

/-- The chosen exponent is strictly greater than two
(`app:ch_regular:thm:exact-correction`). -/
theorem two_lt_ballSobolevExponent (c : EuclideanSpace ℝ (Fin n)) {R : ℝ}
    (hR : 0 < R) : 2 < ballSobolevExponent F c hR :=
  (exists_memLp_and_norm_le_restrictionSobolevNorm_ball (F := F) c hR).choose_spec.1

instance (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    Fact (1 ≤ (ballSobolevExponent F c hR : ℝ≥0∞)) :=
  ⟨by exact_mod_cast (show (1 : ℝ≥0) ≤ ballSobolevExponent F c hR from
    (by norm_num : (1 : ℝ≥0) ≤ 2).trans (two_lt_ballSobolevExponent c hR).le)⟩

/-- A uniform constant for the chosen ball embedding
(`app:ch_regular:thm:exact-correction`). -/
def ballSobolevEmbeddingConstant (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) : ℝ :=
  (exists_memLp_and_norm_le_restrictionSobolevNorm_ball (F := F) c hR).choose_spec.2.choose

/-- Positivity of the embedding constant (`app:ch_regular:thm:exact-correction`). -/
theorem ballSobolevEmbeddingConstant_pos (c : EuclideanSpace ℝ (Fin n)) {R : ℝ}
    (hR : 0 < R) : 0 < ballSobolevEmbeddingConstant F c hR :=
  (exists_memLp_and_norm_le_restrictionSobolevNorm_ball (F := F) c hR).choose_spec.2.choose_spec.1

/-- The chosen exponent and constant obey the proved weak-data estimate
(`app:ch_regular:thm:exact-correction`). -/
theorem ballSobolevEmbedding_bound (c : EuclideanSpace ℝ (Fin n)) {R : ℝ}
    (hR : 0 < R) (u : LocalL2 (ball c R) F) (hu : MemRestrictionSobolev (ball c R) 1 u) :
    MemLp u (ballSobolevExponent F c hR : ℝ≥0∞) (volume.restrict (ball c R)) ∧
      (eLpNorm u (ballSobolevExponent F c hR : ℝ≥0∞)
        (volume.restrict (ball c R))).toReal ≤
        ballSobolevEmbeddingConstant F c hR * restrictionSobolevNorm (ball c R) 1 u :=
  (exists_memLp_and_norm_le_restrictionSobolevNorm_ball (F := F) c hR).choose_spec.2.choose_spec.2 u hu

namespace RestrictionSobolevSpace

/-- The representative-preserving linear inclusion before adding its bound
(`app:ch_regular:thm:exact-correction`). -/
def ballToLpLinear (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    RestrictionSobolevSpace (ball c R) F 1 →ₗ[ℝ]
      Lp F (ballSobolevExponent F c hR) (volume.restrict (ball c R)) where
  toFun u := ((ballSobolevEmbedding_bound c hR (toL2 1 u) (toL2_mem 1 u)).1).toLp _
  map_add' u v := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    simpa only [map_add] using Lp.coeFn_add (toL2 1 u) (toL2 1 v)
  map_smul' a u := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    simpa only [map_smul, RingHom.id_apply] using Lp.coeFn_smul a (toL2 1 u)

/-- The bounded inclusion H¹(U) → Lᵖ(U), constructed from the unconditional
weak Sobolev inequality (`app:ch_regular:thm:exact-correction`). -/
def toLpBall (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    RestrictionSobolevSpace (ball c R) F 1 →L[ℝ]
      Lp F (ballSobolevExponent F c hR) (volume.restrict (ball c R)) :=
  (ballToLpLinear c hR).mkContinuous (ballSobolevEmbeddingConstant F c hR) (by
    intro u
    change ‖((ballSobolevEmbedding_bound c hR (toL2 1 u) (toL2_mem 1 u)).1).toLp _‖ ≤ _
    rw [Lp.norm_toLp]
    exact (ballSobolevEmbedding_bound c hR (toL2 1 u) (toL2_mem 1 u)).2)

/-- The inclusion preserves representatives (`app:not:fourier`). -/
theorem toLpBall_coeFn (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (u : RestrictionSobolevSpace (ball c R) F 1) :
    toLpBall c hR u =ᵐ[volume.restrict (ball c R)] toL2 1 u :=
  MemLp.coeFn_toLp (ballSobolevEmbedding_bound c hR (toL2 1 u) (toL2_mem 1 u)).1

/-- The inclusion has the quantitative bound used before cutoff selection
(`app:ch_regular:thm:exact-correction`). -/
theorem toLpBall_norm_le (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    ‖toLpBall (F := F) c hR‖ ≤ ballSobolevEmbeddingConstant F c hR :=
  LinearMap.mkContinuous_norm_le _ (ballSobolevEmbeddingConstant_pos c hR).le _

/-- Equality in Lᵖ implies equality in the original H¹ restriction space
(`app:not:fourier`). -/
theorem toLpBall_injective (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    Function.Injective (toLpBall (F := F) c hR) := by
  intro u v huv
  apply toL2_injective 1
  apply Lp.ext
  have he := toLpBall_coeFn c hR u
  rw [huv] at he
  exact he.symm.trans (toLpBall_coeFn c hR v)

end RestrictionSobolevSpace
end JanetCartan.LocalSobolev
