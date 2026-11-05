module

public import JanetCartan.Analysis.Operator.RealQuadratures
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces

/-!
# Recovering the complex carrier bound from both real quadratures

For `app:ch_background:prop:bg-frame`, Step 1, the full complex input is
essential: applying `2 Re T` to `f` and `i f` controls both components of `T f`.
This proves a reverse norm comparison for the actual carrier and its positive
normal. It makes no reverse-norm claim for an arbitrary real compression.
Consumer: the uniform COMPLEX normal bound in `exists_carrierL2Extension`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
variable {n : ℕ}

/-- Both real components recover the full complex output in the literal torus
L² quotient (`app:ch_background:eq:bg-realification`). -/
theorem recover_complex_output (z : ComplexOutputL2 n) :
    l2ComplexInclusion volume (l2RealPart volume z) -
      Complex.I • l2ComplexInclusion volume (l2RealPart volume (Complex.I • z)) = z := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub
      (l2ComplexInclusion volume (l2RealPart volume z))
      (Complex.I • l2ComplexInclusion volume (l2RealPart volume (Complex.I • z))),
    Lp.coeFn_smul Complex.I (l2ComplexInclusion volume (l2RealPart volume (Complex.I • z))),
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL (l2RealPart volume z),
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      (l2RealPart volume (Complex.I • z)),
    (euclideanRealPart (ι := Fin n)).coeFn_compLpL z,
    (euclideanRealPart (ι := Fin n)).coeFn_compLpL (Complex.I • z),
    Lp.coeFn_smul Complex.I z] with x hsub hsmul hr hi hre him hz
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply]
  simp only [l2RealPart, l2ComplexInclusion] at *
  rw [hr, hi, hre, him, hz]
  apply PiLp.ext
  intro i
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- A bound for the real channel on the entire realified complex source also
bounds the complex carrier (`app:ch_background:prop:bg-frame`, Step 1).
The triangle inequality suffices; no sharp comparison constant is needed. -/
theorem norm_carrier_le_realQuadratureChannel
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    ‖T‖ ≤ ‖realQuadratureChannel T‖ := by
  have hinc (r : OutputL2 n) : ‖l2ComplexInclusion volume r‖ ≤ ‖r‖ := by
    simpa only [one_mul] using (l2ComplexInclusion volume).le_of_opNorm_le
      (l2ComplexInclusion_norm_le volume) r
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have h₁ := (realQuadratureChannel T).le_opNorm f
  have h₂ := (realQuadratureChannel T).le_opNorm (Complex.I • f)
  simp only [realQuadratureChannel_apply, norm_smul, Real.norm_ofNat, Complex.norm_I,
    one_mul, map_smul] at h₁ h₂
  have hrec := recover_complex_output (T f)
  have hb : ‖T f‖ ≤ ‖l2RealPart volume (T f)‖ +
      ‖l2RealPart volume (Complex.I • T f)‖ := by
    calc
      ‖T f‖ = ‖l2ComplexInclusion volume (l2RealPart volume (T f)) -
          Complex.I • l2ComplexInclusion volume (l2RealPart volume (Complex.I • T f))‖ :=
        congrArg norm hrec.symm
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (hinc _)
        (by simpa only [norm_smul, Complex.norm_I, one_mul] using
          hinc (l2RealPart volume (Complex.I • T f))))
  linarith

/-- The actual complex normal is bounded by the actual real-quadrature normal.
Together with the full reflected PDO identification this supplies the COMPLEX
bound required by `exists_carrierL2Extension`, without multiplying the reflected
symbol by four again (`app:ch_background:eq:bg-real-symbol`). -/
theorem norm_carrier_normal_le_realQuadratureNormal
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    ‖T.comp T.adjoint‖ ≤
      ‖(realQuadratureChannel T).comp (realQuadratureChannel T).adjoint‖ := by
  have h₁ := ContinuousLinearMap.norm_adjoint_comp_self T.adjoint
  have h₂ := ContinuousLinearMap.norm_adjoint_comp_self (realQuadratureChannel T).adjoint
  simp only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] at h₁ h₂
  rw [h₁, h₂]
  exact mul_self_le_mul_self (norm_nonneg _) (norm_carrier_le_realQuadratureChannel T)

end JanetCartan.ContinuumRow.CarrierNormalRealization
