module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Derivatives
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Dominated integration of smooth Euclidean coordinate jets

For `app:ch_response:thm:response-literal-transfer`, the low-envelope frequency
integral is smooth and every ordered target derivative commutes with integration.
The inputs are smooth parameter slices, measurable coordinate jets, and integrable
majorants uniform in the target. First-order dominated differentiation is derived
by reconstructing the Fréchet derivative from its finitely many coordinates;
smoothness then follows by induction on the differentiability order.

The consuming frequency-differentiation construction must supply these inputs
for its scalar kernel coordinates and `compactFrequencyJetMajorant`. This module
proves only the analytic implication, with the original product Lebesgue measure.
-/

open MeasureTheory Filter
open scoped ContDiff Topology

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.LowEnvelope
open AmplitudeBound

variable {n : ℕ}

/-- Finite coordinate reconstruction for the dominated first-derivative step
in `app:ch_response:thm:response-literal-transfer`. -/
private theorem fderiv_eq_sum_coordinateDerivs (f : Euclidean n → ℂ)
    (x : Euclidean n) :
    fderiv ℝ f x = ∑ i : Fin n, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
      (fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  ext v
  simpa only [sum_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.coe_proj, map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] using
    (congrArg (fderiv ℝ f x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)).symm

variable {g : (Euclidean n × Euclidean n) → Euclidean n → ℂ}
    {b : List (Fin n) → (Euclidean n × Euclidean n) → ℝ}
    (hg : ∀ p, ContDiff ℝ ∞ (g p))
    (hm : ∀ (α : List (Fin n)) (x : Euclidean n), AEStronglyMeasurable
      (fun p ↦ euclideanCoordinateDerivList α (g p) x) (volume.prod volume))
    (hi : ∀ α, Integrable (b α) (volume.prod volume))
    (hb : ∀ (α : List (Fin n)) (p : Euclidean n × Euclidean n) (x : Euclidean n),
      ‖euclideanCoordinateDerivList α (g p) x‖ ≤ b α p)

include hm hi hb

/-- Every scalar coordinate jet is integrable under the majorants used for
frequency differentiation in `app:ch_response:thm:response-literal-transfer`. -/
theorem integrable_euclideanCoordinateDerivList_of_dominated (α : List (Fin n)) (x : Euclidean n) :
    Integrable (fun p ↦ euclideanCoordinateDerivList α (g p) x) (volume.prod volume) :=
  (hi α).mono' (hm α x) (Eventually.of_forall fun p ↦ hb α p x)

include hg

/-- First-order dominated differentiation of each jet, used by the smoothness
and ordered-derivative inductions for `app:ch_response:thm:response-literal-transfer`. -/
private theorem hasFDerivAt_integral_coordinateJet (α : List (Fin n)) (x : Euclidean n) :
    HasFDerivAt (fun z ↦ ∫ p, euclideanCoordinateDerivList α (g p) z ∂(volume.prod volume))
      (∑ i : Fin n, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
        (∫ p, euclideanCoordinateDerivList (i :: α) (g p) x ∂(volume.prod volume))) x := by
  let L (i : Fin n) :=
    ContinuousLinearMap.smulRightL ℝ (Euclidean n) ℂ (EuclideanSpace.proj (𝕜 := ℝ) i)
  have he (p : Euclidean n × Euclidean n) (z : Euclidean n) :
      fderiv ℝ (euclideanCoordinateDerivList α (g p)) z =
        ∑ i, L i (euclideanCoordinateDerivList (i :: α) (g p) z) :=
    fderiv_eq_sum_coordinateDerivs _ _
  have hterm (i : Fin n) (z : Euclidean n) : Integrable
      (fun p ↦ L i (euclideanCoordinateDerivList (i :: α) (g p) z)) (volume.prod volume) :=
    (L i).integrable_comp (integrable_euclideanCoordinateDerivList_of_dominated hm hi hb (i :: α) z)
  have hD : HasFDerivAt (fun z ↦ ∫ p, euclideanCoordinateDerivList α (g p) z ∂(volume.prod volume))
      (∫ p, fderiv ℝ (euclideanCoordinateDerivList α (g p)) x ∂(volume.prod volume)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (μ := volume.prod volume) (x₀ := x)
      (F := fun z p ↦ euclideanCoordinateDerivList α (g p) z)
      (F' := fun z p ↦ fderiv ℝ (euclideanCoordinateDerivList α (g p)) z)
      (s := Set.univ) (bound := fun p ↦
        ∑ i, ‖(EuclideanSpace.proj (𝕜 := ℝ) i : Euclidean n →L[ℝ] ℝ)‖ * b (i :: α) p)
      (Filter.univ_mem)
    · exact Eventually.of_forall (hm α)
    · exact integrable_euclideanCoordinateDerivList_of_dominated hm hi hb α x
    · change AEStronglyMeasurable
        (fun p ↦ fderiv ℝ (euclideanCoordinateDerivList α (g p)) x) (volume.prod volume)
      exact (integrable_finsetSum Finset.univ (fun i _ ↦ hterm i x)).aestronglyMeasurable.congr
        (Eventually.of_forall fun p ↦ (he p x).symm)
    · apply Eventually.of_forall
      intro p z _
      rw [he]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      change ‖(EuclideanSpace.proj (𝕜 := ℝ) i).smulRight _‖ ≤ _
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_left (hb (i :: α) p z) (norm_nonneg _)
    · exact integrable_finsetSum Finset.univ (fun i _ ↦ (hi (i :: α)).const_mul _)
    · exact Eventually.of_forall fun p z _ ↦
        ((contDiff_euclideanCoordinateDerivList (hg p) α).differentiable (by simp) z).hasFDerivAt
  convert hD using 1
  rw [integral_congr_ae (Eventually.of_forall fun p ↦ he p x)]
  rw [integral_finsetSum _ (fun i _ ↦ hterm i x)]
  exact Finset.sum_congr rfl fun i _ ↦
    ((L i).integral_comp_comm
      (integrable_euclideanCoordinateDerivList_of_dominated hm hi hb (i :: α) x)).symm

/-- Simultaneous smoothness of all integrated coordinate jets, used to obtain
smoothness of the original frequency integral in
`app:ch_response:thm:response-literal-transfer`. -/
private theorem contDiff_integral_coordinateJet (α : List (Fin n)) :
    ContDiff ℝ ∞ (fun z ↦ ∫ p, euclideanCoordinateDerivList α (g p) z ∂(volume.prod volume)) := by
  have hd (β : List (Fin n)) : Differentiable ℝ
      (fun z ↦ ∫ p, euclideanCoordinateDerivList β (g p) z ∂(volume.prod volume)) :=
    fun z ↦ (hasFDerivAt_integral_coordinateJet hg hm hi hb β z).differentiableAt
  have hf (β : List (Fin n)) :
      fderiv ℝ (fun z ↦ ∫ p, euclideanCoordinateDerivList β (g p) z ∂(volume.prod volume)) =
        fun z ↦ ∑ i : Fin n, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
          (∫ p, euclideanCoordinateDerivList (i :: β) (g p) z ∂(volume.prod volume)) :=
    funext fun z ↦ (hasFDerivAt_integral_coordinateJet hg hm hi hb β z).fderiv
  apply contDiff_infty.mpr
  intro k
  have hk : ∀ β : List (Fin n), ContDiff ℝ k
      (fun z ↦ ∫ p, euclideanCoordinateDerivList β (g p) z ∂(volume.prod volume)) := by
    induction k with
    | zero => exact fun β ↦ contDiff_zero.mpr (hd β).continuous
    | succ k ih =>
      intro β
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨hd β, by simp, ?_⟩
      rw [hf]
      exact ContDiff.sum fun i _ ↦ contDiff_const.smulRight (ih (i :: β))
  exact hk α

/-- Smoothness of the scalar frequency integral from dominated coordinate jets,
for `app:ch_response:thm:response-literal-transfer`. The kernel measurability and
majorant hypotheses are supplied by the consuming low-envelope construction. -/
theorem contDiff_integral_of_dominated_coordinateDerivs :
    ContDiff ℝ ∞ (fun z ↦ ∫ p, g p z ∂(volume.prod volume)) :=
  contDiff_integral_coordinateJet hg hm hi hb []

/-- Exact interchange of every ordered target derivative and the product
Lebesgue integral, for `app:ch_response:thm:response-literal-transfer`.
Derivative interchange is deduced from domination, not assumed. -/
theorem euclideanCoordinateDerivList_integral_of_dominated (α : List (Fin n)) (x : Euclidean n) :
    euclideanCoordinateDerivList α (fun z ↦ ∫ p, g p z ∂(volume.prod volume)) x =
      ∫ p, euclideanCoordinateDerivList α (g p) x ∂(volume.prod volume) := by
  induction α generalizing x with
  | nil => rfl
  | cons i α ih =>
    have he : euclideanCoordinateDerivList α (fun z ↦ ∫ p, g p z ∂(volume.prod volume)) =
        (fun z ↦ ∫ p, euclideanCoordinateDerivList α (g p) z ∂(volume.prod volume)) := by
      funext z
      exact ih z
    simp only [euclideanCoordinateDerivList, he,
      (hasFDerivAt_integral_coordinateJet hg hm hi hb α x).fderiv, sum_apply,
      ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj]
    simp

end JanetCartan.ResponseTransfer.LowEnvelope
