module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly

/-!
# Complex output multiplication by a real cutoff

The common measurement restriction of `app:ch_background:defn:bg-row` is
complex linear and self-adjoint. Realification commutes with it, so the full
complex input still supplies both real quadratures.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace JanetCartan.ContinuumRow.CommonMeasurement
variable {n : ℕ}

/-- The complex continuous function associated to the real measurement cutoff
(`app:ch_background:defn:bg-row`). -/
def complexCutoff (χ : C(Torus n, ℝ)) : C(Torus n, ℂ) :=
  ⟨fun x ↦ (χ x : ℂ), Complex.continuous_ofReal.comp χ.continuous⟩

/-- Complex-linear multiplication on the actual complex output L²
(`app:ch_background:eq:bg-T`). -/
def complexMultiplier (χ : C(Torus n, ℝ)) :
    ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ∞ 2 2
    (ContinuousMap.toLp ∞ volume ℂ (complexCutoff χ))

/-- Literal action with normalized torus measure (`app:ch_background:eq:bg-T`). -/
theorem complexMultiplier_coeFn (χ : C(Torus n, ℝ)) (f : ComplexOutputL2 n) :
    complexMultiplier χ f =ᵐ[volume] fun x ↦ (χ x : ℂ) • f x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2)
      (ContinuousMap.toLp ∞ volume ℂ (complexCutoff χ)) f,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) volume (complexCutoff χ)] with x hf hχ
  exact hf.trans (congrArg (fun c : ℂ ↦ c • f x) hχ)

/-- The complex multiplier has the same cutoff bound as its real counterpart
(`app:ch_background:prop:bg-frame`). -/
theorem complexMultiplier_norm_le (χ : C(Torus n, ℝ)) : ‖complexMultiplier χ‖ ≤ ‖χ‖ := by
  calc
    ‖complexMultiplier χ‖ ≤
        ‖(ContinuousLinearMap.lsmul ℂ ℂ (E := EuclideanSpace ℂ (Fin n))).holderL
          volume ∞ 2 2‖ * ‖ContinuousMap.toLp ∞ volume ℂ (complexCutoff χ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (1 * ‖complexCutoff χ‖) := mul_le_mul
      ((ContinuousLinearMap.norm_holderL_le _).trans ContinuousLinearMap.opNorm_lsmul_le)
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
        (by simpa using (ContinuousMap.toLp_norm_le (p := ∞) (𝕜 := ℂ) (E := ℂ)
          (volume : Measure (Torus n))))
        (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ ≤ ‖χ‖ := by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg χ)).mpr
      intro x
      simpa only [complexCutoff, ContinuousMap.coe_mk, Complex.norm_real] using χ.norm_coe_le_norm x

/-- A real cutoff is self-adjoint even on complex output
(`app:ch_background:eq:bg-realification`). -/
theorem complexMultiplier_adjoint (χ : C(Torus n, ℝ)) :
    (complexMultiplier χ).adjoint = complexMultiplier χ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [complexMultiplier_coeFn χ f, complexMultiplier_coeFn χ g] with x hf hg
  rw [hf, hg]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- Taking real part commutes with the measurement multiplier
(`app:ch_background:eq:bg-realification`). -/
theorem realPart_complexMultiplier (χ : C(Torus n, ℝ)) (f : ComplexOutputL2 n) :
    l2RealPart volume (complexMultiplier χ f) = cutoffMultiplier χ (l2RealPart volume f) := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (complexMultiplier χ f),
    complexMultiplier_coeFn χ f, cutoffMultiplier_coeFn χ (l2RealPart volume f),
    euclideanRealPart.coeFn_compLpL f] with x hr hm hc hf
  change (euclideanRealPart.compLpL 2 volume) (complexMultiplier χ f) x = _
  rw [hr, hm, hc]
  change euclideanRealPart ((χ x : ℂ) • f x) = χ x • (euclideanRealPart.compLpL 2 volume) f x
  rw [hf]
  ext i
  simp

/-- Including real output commutes with the SAME complex multiplier
(`app:ch_background:eq:bg-realification`). -/
theorem complexMultiplier_inclusion (χ : C(Torus n, ℝ)) (f : OutputL2 n) :
    complexMultiplier χ (l2ComplexInclusion volume f) =
      l2ComplexInclusion volume (cutoffMultiplier χ f) := by
  apply Lp.ext
  filter_upwards [complexMultiplier_coeFn χ (l2ComplexInclusion volume f),
    euclideanComplexInclusion.coeFn_compLpL (cutoffMultiplier χ f),
    cutoffMultiplier_coeFn χ f, euclideanComplexInclusion.coeFn_compLpL f] with x hm hi hc hf
  rw [hm]
  change (χ x : ℂ) • (euclideanComplexInclusion.compLpL 2 volume) f x =
    (euclideanComplexInclusion.compLpL 2 volume) (cutoffMultiplier χ f) x
  rw [hi, hc, hf]
  ext i
  simp

end JanetCartan.ContinuumRow.CommonMeasurement
