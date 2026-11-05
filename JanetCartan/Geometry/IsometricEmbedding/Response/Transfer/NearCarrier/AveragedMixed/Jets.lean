module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Jets.Affine
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Jets.Inverse

/-!
# Joint finite jets of the normalized averaged mixed matrix

The coefficient estimates immediately before
`app:ch_response:eq:direct-envelope-profile`. Primitive mixed-matrix jets on
an open buffered product chart are pulled back along the affine segment and
then integrated. Matrix norms are Frobenius norms; inverse gaps use the fixed
Euclidean operator realization. All constants below are independent of the
grading scale and carrier frequency.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

local instance averagedMixedJetsMatrixTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

section Average

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n}
  {X D V : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V)
  (hcD : Convex ℝ D) (hζ : ζ ∈ D) (hbuffer : ∀ ε ∈ V, ζ + ε ∈ D)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))

include hX hD hcD hζ hbuffer hS in
private theorem segment_smooth_on_chart :
    ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (X ×ˢ V), ContDiffAt ℝ ∞
      (fun w : ℝ × (Euclidean n × Euclidean n) ↦
        FourierIntegral.mixedPhaseMatrix S w.2.1 (ζ + w.1 • w.2.2)) z := by
  intro z hz
  exact mixedPhase_segment_contDiffAt hX hD hS
    ⟨hz.2.1, hcD.add_smul_mem hζ (hbuffer _ hz.2.2) hz.1⟩

include hX hD hV hcD hζ hbuffer hS

/-- The literal normalized average is jointly smooth, derived from primitive
smoothness on the buffered chart (`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedMixedMatrix_normalized_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      averagedMixedMatrix S ζ 1 p.1 p.2) (X ×ˢ V) := by
  simp only [averagedMixedMatrix, one_smul]
  apply contDiffOn_fixedIntervalIntegral (a := 0) (b := 1)
    (F := fun w : ℝ × (Euclidean n × Euclidean n) ↦
      FourierIntegral.mixedPhaseMatrix S w.2.1 (ζ + w.1 • w.2.2)) (hX.prod hV)
  simpa using segment_smooth_on_chart hX hD hcD hζ hbuffer hS

/-- Differentiation under the actual segment integral, with domination proved
from the primitive mixed jets (`app:ch_response:eq:direct-envelope-profile`). -/
theorem iteratedFDeriv_averagedMixedMatrix_normalized {C : ℕ → ℝ} {L : ℝ} {r k : ℕ}
    (hb : ∀ j ≤ r, ∀ q ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
        C j * L ^ j)
    (hk : k ≤ r) {p : Euclidean n × Euclidean n} (hp : p ∈ X ×ˢ V) :
    iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      averagedMixedMatrix S ζ 1 q.1 q.2) p =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k
        (fun q : Euclidean n × Euclidean n ↦
          FourierIntegral.mixedPhaseMatrix S q.1 (ζ + t • q.2)) p := by
  simp only [averagedMixedMatrix, one_smul]
  apply NormalComparison.iteratedFDeriv_unitIntervalIntegral (B := fun j ↦ C j * L ^ j)
    (hX.prod hV) (segment_smooth_on_chart hX hD hcD hζ hbuffer hS) _ hp
  intro j hj t ht q hq
  exact norm_iteratedFDeriv_mixedPhase_segment_le hX hD hS (hb j (hj.trans hk)) ht
    ⟨hq.1, hcD.add_smul_mem hζ (hbuffer _ hq.2) ht⟩

/-- Averaging preserves the primitive finite joint jet grades in the Frobenius
norm (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_averagedMixedMatrix_normalized_le
    {C : ℕ → ℝ} {L : ℝ} {r k : ℕ}
    (hb : ∀ j ≤ r, ∀ q ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
        C j * L ^ j)
    (hk : k ≤ r) {p : Euclidean n × Euclidean n} (hp : p ∈ X ×ˢ V) :
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      averagedMixedMatrix S ζ 1 q.1 q.2) p‖ ≤ C k * L ^ k := by
  rw [iteratedFDeriv_averagedMixedMatrix_normalized hX hD hV hcD hζ hbuffer hS hb hk hp]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun t ht ↦
      norm_iteratedFDeriv_mixedPhase_segment_le hX hD hS (hb k hk)
        (by simpa using uIoc_subset_uIcc ht)
        ⟨hp.1, hcD.add_smul_mem hζ (hbuffer _ hp.2)
          (by simpa using uIoc_subset_uIcc ht)⟩)

/-- Fixed norm conversion gives the operator jet budget from the primitive
Frobenius budget (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_averagedMixedOperator_normalized_le
    {C : ℕ → ℝ} {L : ℝ} {r k : ℕ}
    (hb : ∀ j ≤ r, ∀ q ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
        C j * L ^ j)
    (hk : k ≤ r) {p : Euclidean n × Euclidean n} (hp : p ∈ X ×ˢ V) :
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      averagedMixedOperator S ζ 1 q.1 q.2) p‖ ≤
        ‖(mixedMatrixOperatorEquiv n).toContinuousLinearMap‖ * (C k * L ^ k) := by
  apply ((mixedMatrixOperatorEquiv n).toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    ((averagedMixedMatrix_normalized_contDiffOn hX hD hV hcD hζ hbuffer hS).contDiffAt
      ((hX.prod hV).mem_nhds hp)) (by simp)).trans
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_averagedMixedMatrix_normalized_le hX hD hV hcD hζ hbuffer hS hb hk hp)
    (norm_nonneg _)

end Average

section Inverse

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n}
  {X D V : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V)
  (hcD : Convex ℝ D) (hζ : ζ ∈ D) (hbuffer : ∀ ε ∈ V, ζ + ε ∈ D)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))

include hX hD hV hcD hζ hbuffer hS

/-- The inverse of the actual normalized averaged operator has the joint grade
`L ^ k`. All derivative inputs concern the primitive mixed matrix; the parent
supplies `hu` and `hM` from `averagedMixedOperator_inverse_on_selector`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_averagedMixedOperator_inverse_le
    {C : ℕ → ℝ} {L M : ℝ} {r k : ℕ} (hL : 1 ≤ L)
    (hb : ∀ j ≤ r, ∀ q ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
        C j * L ^ j)
    (hu : ∀ q ∈ X ×ˢ V, IsUnit (averagedMixedOperator S ζ 1 q.1 q.2))
    (hM : ∀ q ∈ X ×ˢ V, ‖Ring.inverse (averagedMixedOperator S ζ 1 q.1 q.2)‖ ≤ 2 * M)
    (hk : k ≤ r) {p : Euclidean n × Euclidean n} (hp : p ∈ X ×ˢ V) :
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      Ring.inverse (averagedMixedOperator S ζ 1 q.1 q.2)) p‖ ≤
        averagedMixedInverseJetConstant n k C M * L ^ k := by
  let f := fun q : Euclidean n × Euclidean n ↦ averagedMixedOperator S ζ 1 q.1 q.2
  have hf : ContDiffOn ℝ ∞ f (X ×ˢ V) :=
    (mixedMatrixOperatorEquiv n).contDiff.comp_contDiffOn
      (averagedMixedMatrix_normalized_contDiffOn hX hD hV hcD hζ hbuffer hS)
  have hd : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDerivWithin ℝ i f (X ×ˢ V) p‖ ≤ (averagedMixedJetBudget n k C * L) ^ i := by
    intro i hi hik
    rw [iteratedFDerivWithin_of_isOpen _ (hX.prod hV) hp, mul_pow]
    calc
      _ ≤ ‖(mixedMatrixOperatorEquiv n).toContinuousLinearMap‖ * (C i * L ^ i) :=
        norm_iteratedFDeriv_averagedMixedOperator_normalized_le
          hX hD hV hcD hζ hbuffer hS hb (hik.trans hk) hp
      _ ≤ averagedMixedJetBudget n k C ^ i * L ^ i := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mixedMatrix_jet_coefficient_le_budget_pow n C hi hik)
          (pow_nonneg (zero_le_one.trans hL) _)
  have he := norm_iteratedFDerivWithin_ringInverse_comp_le
    (hf.of_le (by simp)) (hX.prod hV).uniqueDiffOn hu hp (hM p hp) hd
  rw [iteratedFDerivWithin_of_isOpen _ (hX.prod hV) hp] at he
  simpa only [averagedMixedInverseJetConstant, mul_pow, mul_assoc] using he

/-- Frobenius jet bounds for the literal matrix inverse of the normalized
average. Conversion back from the operator inverse costs only the norm of the
fixed equivalence; the constant is independent of scale and frequency
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_averagedMixedMatrix_inverse_le
    {C : ℕ → ℝ} {L M : ℝ} {r k : ℕ} (hL : 1 ≤ L)
    (hb : ∀ j ≤ r, ∀ q ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
        C j * L ^ j)
    (hu : ∀ q ∈ X ×ˢ V, IsUnit (averagedMixedOperator S ζ 1 q.1 q.2))
    (hM : ∀ q ∈ X ×ˢ V, ‖Ring.inverse (averagedMixedOperator S ζ 1 q.1 q.2)‖ ≤ 2 * M)
    (hk : k ≤ r) {p : Euclidean n × Euclidean n} (hp : p ∈ X ×ˢ V) :
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      (averagedMixedMatrix S ζ 1 q.1 q.2)⁻¹) p‖ ≤
        (‖(mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap‖ *
          averagedMixedInverseJetConstant n k C M) * L ^ k := by
  let f := fun q : Euclidean n × Euclidean n ↦ averagedMixedOperator S ζ 1 q.1 q.2
  have hf : ContDiffOn ℝ ∞ f (X ×ˢ V) :=
    (mixedMatrixOperatorEquiv n).contDiff.comp_contDiffOn
      (averagedMixedMatrix_normalized_contDiffOn hX hD hV hcD hζ hbuffer hS)
  have hi : ContDiffAt ℝ ∞ (fun q ↦ Ring.inverse (f q)) p :=
    (contDiffOn_ringInverse_units.comp hf hu).contDiffAt ((hX.prod hV).mem_nhds hp)
  have he : (fun q : Euclidean n × Euclidean n ↦ (averagedMixedMatrix S ζ 1 q.1 q.2)⁻¹) =
      (mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap ∘ (fun q ↦ Ring.inverse (f q)) := by
    funext q
    exact (mixedMatrixOperatorEquiv_symm_inverse _).symm
  rw [he, mul_assoc]
  exact ((mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    hi (by simp)).trans (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_averagedMixedOperator_inverse_le hX hD hV hcD hζ hbuffer hS
        hL hb hu hM hk hp) (norm_nonneg _))

end Inverse

end JanetCartan.ResponseTransfer
