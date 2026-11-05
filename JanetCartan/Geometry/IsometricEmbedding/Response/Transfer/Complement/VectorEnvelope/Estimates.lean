module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.HighEnvelope
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Vector envelope split and sharp bounds

The complete-complement split of `app:ch_response:thm:response-literal-transfer`
on the same Euclidean vector L² space used by the graph operators. The scalar
cutoff is applied in the proved isometric coordinates; its estimates pass to
the finite Hilbert sum without a dimension factor.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.Complement

variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "VL2" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)

/-- Coordinate estimates retain their constant in the Hilbert norm. Used for
both halves of `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorFourierSobolevNorm_le_of_coordinate_bounds {s p C : ℝ}
    (hC : 0 ≤ C) (u f : VL2)
    (h : ∀ i, fourierSobolevNorm s (finiteL2CoordinateIsometry volume u i) ≤
      C * fourierSobolevNorm p (finiteL2CoordinateIsometry volume f i)) :
    vectorFourierSobolevNorm s u ≤ C * vectorFourierSobolevNorm p f := by
  have hsq : vectorFourierSobolevNorm s u ^ 2 ≤
      (C * vectorFourierSobolevNorm p f) ^ 2 := by
    simp only [vectorFourierSobolevNorm, mul_pow, matrixFourierSobolevNorm_sq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow] using
      pow_le_pow_left₀ (fourierSobolevNorm_nonneg _ _) (h i) 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hsq

namespace EnvelopeCutoff
variable {Λ B R : ℝ} (χ : EnvelopeCutoff d Λ B R)

/-- Apply the actual scalar low cutoff in the finite L² coordinates, for
`app:ch_response:thm:response-literal-transfer`. -/
def vectorLow (f : VL2) : VL2 :=
  (finiteL2CoordinateIsometry volume).symm
    (WithLp.toLp 2 (fun i ↦ χ.low (finiteL2CoordinateIsometry volume f i)))

/-- The exact complementary vector datum in
`app:ch_response:thm:response-literal-transfer`. -/
def vectorHigh (f : VL2) : VL2 := f - χ.vectorLow f

/-- Coordinate identification with the scalar cutoff in
`app:ch_response:thm:response-literal-transfer`. -/
@[simp] theorem coordinate_vectorLow (f : VL2) (i : I) :
    finiteL2CoordinateIsometry volume (χ.vectorLow f) i =
      χ.low (finiteL2CoordinateIsometry volume f i) := by
  simp [vectorLow]

/-- Coordinate identification of the high part in
`app:ch_response:thm:response-literal-transfer`. -/
@[simp] theorem coordinate_vectorHigh (f : VL2) (i : I) :
    finiteL2CoordinateIsometry volume (χ.vectorHigh f) i =
      χ.high (finiteL2CoordinateIsometry volume f i) := by
  simp [vectorHigh, map_sub, high]

/-- Exact reconstruction of the vector source envelope in
`app:ch_response:thm:response-literal-transfer`. -/
theorem vectorLow_add_vectorHigh (f : VL2) : χ.vectorLow f + χ.vectorHigh f = f := by
  simp [vectorHigh]

/-- Every real Sobolev order of the low vector source in
`app:ch_response:thm:response-literal-transfer`. -/
theorem vectorLow_mem_all_orders (s : ℝ) (f : VL2) :
    MemVectorFourierSobolev s (χ.vectorLow f) := by
  intro i
  simpa only [coordinate_vectorLow] using
    χ.low_mem_all_orders s (finiteL2CoordinateIsometry volume f i)

/-- The scalar low bound, with no coordinate loss, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem vectorLow_sobolev_bound {p : ℝ} {f : VL2} (hf : MemVectorFourierSobolev p f) :
    MemVectorFourierSobolev p (χ.vectorLow f) ∧
      vectorFourierSobolevNorm p (χ.vectorLow f) ≤ B * vectorFourierSobolevNorm p f := by
  refine ⟨χ.vectorLow_mem_all_orders p f,
    vectorFourierSobolevNorm_le_of_coordinate_bounds χ.bound_nonneg _ _ ?_⟩
  intro i
  simpa only [coordinate_vectorLow] using (χ.low_sobolev_bound (hf i)).2

/-- The low L² bound needed by `forwardComplement_lowSupport_vector` and
`reverseComplement_lowSupport_of_geometry`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_vectorLow_le (f : VL2) : ‖χ.vectorLow f‖ ≤ B * ‖f‖ := by
  simpa only [vectorFourierSobolevNorm_zero] using
    (χ.vectorLow_sobolev_bound (f := f) (p := 0) (fun i ↦ memFourierSobolev_zero _)).2

/-- Uniform high membership and bound, including bounded frequencies, in
`app:ch_response:thm:response-literal-transfer`. -/
theorem vectorHigh_sobolev_bound {p : ℝ} {f : VL2} (hf : MemVectorFourierSobolev p f) :
    MemVectorFourierSobolev p (χ.vectorHigh f) ∧
      vectorFourierSobolevNorm p (χ.vectorHigh f) ≤
        (1 + B) * vectorFourierSobolevNorm p f := by
  constructor
  · intro i
    simpa only [coordinate_vectorHigh] using (χ.high_sobolev_bound (hf i)).1
  · apply vectorFourierSobolevNorm_le_of_coordinate_bounds
      (by linarith [χ.bound_nonneg])
    intro i
    simpa only [coordinate_vectorHigh] using (χ.high_sobolev_bound (hf i)).2

/-- The sharp vector high-envelope estimate in
`app:ch_response:thm:response-literal-transfer`, reused from the scalar estimate. -/
theorem vectorHigh_tail_bound {t p : ℝ} (hΛ : 0 < Λ) (htp : t ≤ p)
    {f : VL2} (hf : MemVectorFourierSobolev p f) :
    MemVectorFourierSobolev t (χ.vectorHigh f) ∧
      vectorFourierSobolevNorm t (χ.vectorHigh f) ≤
        (1 + B) * Λ ^ (t - p) * vectorFourierSobolevNorm p f := by
  have hB := χ.bound_nonneg
  constructor
  · intro i
    simpa only [coordinate_vectorHigh] using (χ.high_tail_bound hΛ htp (hf i)).1
  · apply vectorFourierSobolevNorm_le_of_coordinate_bounds (by positivity)
    intro i
    simpa only [coordinate_vectorHigh] using (χ.high_tail_bound hΛ htp (hf i)).2

/-- Physical covector cutoff χ(2πξ), with its explicit normalization cost,
for `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorHigh_physical_tail_bound {t p : ℝ} (hΛ : 0 < Λ) (htp : t ≤ p)
    {f : VL2} (hf : MemVectorFourierSobolev p f) :
    MemVectorFourierSobolev t (χ.physicalCovectorCutoff.vectorHigh f) ∧
      vectorFourierSobolevNorm t (χ.physicalCovectorCutoff.vectorHigh f) ≤
        ((1 + B) * (2 * Real.pi) ^ (p - t)) * Λ ^ (t - p) *
          vectorFourierSobolevNorm p f := by
  have hB := χ.bound_nonneg
  constructor
  · intro i
    simpa only [coordinate_vectorHigh] using (χ.high_physical_tail_bound hΛ htp (hf i)).1
  · apply vectorFourierSobolevNorm_le_of_coordinate_bounds (by positivity)
    intro i
    simpa only [coordinate_vectorHigh] using (χ.high_physical_tail_bound hΛ htp (hf i)).2

end EnvelopeCutoff
end JanetCartan.ResponseTransfer.Complement
