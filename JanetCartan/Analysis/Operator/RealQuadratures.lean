module

public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Both real quadratures and the normal-operator factor four

This proves the Hilbert-space identities of `app:ch_osc:cor:osc-real` and
`app:ch_waves:eq:real-normal`. For a bounded complex-linear operator `T` with
Euclidean-valued L² output, `realQuadratureChannel T` is `2 Re T`, with the
**entire complex input space** regarded as real. Its real adjoint is `2 T* J`,
where `J` is the usual inclusion of real outputs and `T*` is the complex adjoint.
Consequently its masked normal is `4 Re (T M T*)` on real outputs.

The input Hilbert space may in particular be the scalar complex L² chart space
in the manuscript. The mask is any bounded complex-linear input operator; real
multiplication masks are a special case. Constructing the oscillatory operators
and proving their analytic bounds are separate tasks. The final bound-transfer
theorem takes the complex normal estimate as an explicit premise, as needed for
`app:ch_waves:eq:abstract-normal-two`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- The real channel `2 Re T`, retaining the full complex input
(`app:ch_osc:cor:osc-real`). -/
def realQuadratureChannel (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    E →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ :=
  (2 : ℝ) • (l2RealPart μ ∘L T.restrictScalars ℝ)

omit [CompleteSpace E] in
/-- The channel acts by twice the L² real part (`app:ch_osc:cor:osc-real`). -/
@[simp] theorem realQuadratureChannel_apply
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (f : E) :
    realQuadratureChannel T f = (2 : ℝ) • l2RealPart μ (T f) := rfl

/-- The actual real adjoint is `2 T* J`, with the complex conjugate adjoint `T*`
(`app:ch_osc:eq:osc-factor-four`). -/
theorem realQuadratureChannel_adjoint
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    (realQuadratureChannel T).adjoint =
      (2 : ℝ) • (T.adjoint.restrictScalars ℝ ∘L l2ComplexInclusion μ) := by
  simp [realQuadratureChannel, adjoint_restrictScalars_complex, l2RealPart_adjoint]

/-- The pointwise adjoint formula of `app:ch_osc:eq:osc-factor-four`. -/
@[simp] theorem realQuadratureChannel_adjoint_apply
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (r : Lp (EuclideanSpace ℝ ι) 2 μ) :
    (realQuadratureChannel T).adjoint r =
      (2 : ℝ) • T.adjoint (l2ComplexInclusion μ r) := by
  rw [realQuadratureChannel_adjoint]
  rfl

/-- A complex output operator restricted to real inputs and followed by real part
(`app:ch_waves:eq:real-normal`). -/
def realOutputCompression (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ]
    Lp (EuclideanSpace ℂ ι) 2 μ) :
    Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ :=
  l2RealPart μ ∘L A.restrictScalars ℝ ∘L l2ComplexInclusion μ

/-- The masked normal formed using the real adjoint (`app:ch_osc:eq:osc-factor-four`). -/
def realQuadratureNormal (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (M : E →L[ℂ] E) :
    Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ :=
  realQuadratureChannel T ∘L M.restrictScalars ℝ ∘L (realQuadratureChannel T).adjoint

/-- The exact masked normal identity, including the factor four
(`app:ch_osc:eq:osc-factor-four`). This holds for every bounded complex-linear mask. -/
theorem realQuadratureNormal_eq_four_realPart
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (M : E →L[ℂ] E) :
    realQuadratureNormal T M = (4 : ℝ) • realOutputCompression (T ∘L M ∘L T.adjoint) := by
  rw [realQuadratureNormal, realQuadratureChannel_adjoint]
  ext1 x
  norm_num [realQuadratureChannel, realOutputCompression, map_smul, smul_smul]

/-- The masked normal formula applied to a real output
(`app:ch_osc:eq:osc-factor-four`). -/
theorem realQuadratureNormal_apply
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (M : E →L[ℂ] E)
    (r : Lp (EuclideanSpace ℝ ι) 2 μ) :
    realQuadratureNormal T M r =
      (4 : ℝ) • l2RealPart μ (T (M (T.adjoint (l2ComplexInclusion μ r)))) := by
  rw [realQuadratureNormal_eq_four_realPart]
  rfl

/-- The exact unmasked normal identity `(2 Re T)(2 Re T)* = 4 Re (T T*)`
on real outputs (`app:ch_waves:eq:real-normal`). -/
theorem realQuadratureChannel_normal_eq_four_realPart
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    realQuadratureChannel T ∘L (realQuadratureChannel T).adjoint =
      (4 : ℝ) • realOutputCompression (T ∘L T.adjoint) := by
  rw [realQuadratureChannel_adjoint]
  ext1 x
  norm_num [realQuadratureChannel, realOutputCompression, map_smul, smul_smul]

omit [CompleteSpace E] in
/-- Both quadratures contribute: `C(f + i g) = 2 (Re(T f) - Im(T g))`
componentwise almost everywhere (`app:ch_osc:cor:osc-real`). -/
theorem realQuadratureChannel_both_quadratures_ae
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (f g : E) :
    ∀ᵐ x ∂μ, ∀ i, realQuadratureChannel T (f + Complex.I • g) x i =
      2 * ((T f x i).re - (T g x i).im) := by
  simp only [realQuadratureChannel_apply, map_add T, map_smul T]
  filter_upwards [Lp.coeFn_smul (2 : ℝ) (l2RealPart μ (T f + Complex.I • T g)),
    (euclideanRealPart (ι := ι)).coeFn_compLpL (T f + Complex.I • T g),
    Lp.coeFn_add (T f) (Complex.I • T g), Lp.coeFn_smul Complex.I (T g)] with x h₂ hr ha hi
  intro i
  change ((2 : ℝ) • l2RealPart μ (T f + Complex.I • T g)) x i = _
  rw [h₂]
  change 2 * (((euclideanRealPart.compLpL 2 μ) (T f + Complex.I • T g)) x i) = _
  rw [hr, ha, Pi.add_apply, hi]
  simp [Complex.mul_re, sub_eq_add_neg]

omit [CompleteSpace E] in
/-- Realification costs at most a factor two in operator norm
(`app:ch_osc:cor:osc-real`). -/
theorem realQuadratureChannel_norm_le
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖realQuadratureChannel T‖ ≤ 2 * ‖T‖ := by
  calc
    ‖realQuadratureChannel T‖ = 2 * ‖l2RealPart μ ∘L T.restrictScalars ℝ‖ := by
      simp [realQuadratureChannel, norm_smul]
    _ ≤ 2 * (‖l2RealPart (ι := ι) μ‖ * ‖T.restrictScalars ℝ‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (1 * ‖T‖) := by
      rw [ContinuousLinearMap.norm_restrictScalars]
      gcongr
      exact l2RealPart_norm_le μ
    _ = 2 * ‖T‖ := by ring

omit [CompleteSpace E] in
/-- Realification costs at most a factor four in squared operator norm
(`app:ch_osc:prop:osc-channel`). -/
theorem realQuadratureChannel_norm_sq_le
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖realQuadratureChannel T‖ ^ 2 ≤ 4 * ‖T‖ ^ 2 := by
  calc
    ‖realQuadratureChannel T‖ ^ 2 ≤ (2 * ‖T‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (realQuadratureChannel_norm_le T) 2
    _ = 4 * ‖T‖ ^ 2 := by ring

/-- Restriction to real outputs and taking real part do not increase the norm
(`app:ch_osc:cor:osc-real`). -/
theorem realOutputCompression_norm_le
    (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖realOutputCompression A‖ ≤ ‖A‖ := by
  calc
    ‖realOutputCompression A‖ ≤
        ‖l2RealPart (ι := ι) μ‖ * ‖A.restrictScalars ℝ ∘L l2ComplexInclusion μ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖A.restrictScalars ℝ‖ * ‖l2ComplexInclusion (ι := ι) μ‖) := by
      apply mul_le_mul (l2RealPart_norm_le μ) (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖A‖ * 1) := by
      rw [ContinuousLinearMap.norm_restrictScalars]
      gcongr
      exact l2ComplexInclusion_norm_le μ
    _ = ‖A‖ := by ring

/-- Real output compression preserves differences (`app:ch_osc:cor:osc-real`). -/
theorem realOutputCompression_sub
    (A B : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    realOutputCompression (A - B) = realOutputCompression A - realOutputCompression B := by
  ext1 x
  simp [realOutputCompression]

/-- The masked normal bound transfers with factor four
(`app:ch_osc:cor:osc-real`). -/
theorem realQuadratureNormal_norm_le
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (M : E →L[ℂ] E) :
    ‖realQuadratureNormal T M‖ ≤ 4 * ‖T ∘L M ∘L T.adjoint‖ := by
  rw [realQuadratureNormal_eq_four_realPart, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 4 by positivity)]
  exact mul_le_mul_of_nonneg_left (realOutputCompression_norm_le _) (by positivity)

/-- Differences of masked normals transfer with factor four
(`app:ch_osc:cor:osc-real`). -/
theorem realQuadratureNormal_sub_norm_le
    (T S : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (M : E →L[ℂ] E) :
    ‖realQuadratureNormal T M - realQuadratureNormal S M‖ ≤
      4 * ‖T ∘L M ∘L T.adjoint - S ∘L M ∘L S.adjoint‖ := by
  have h : realQuadratureNormal T M - realQuadratureNormal S M =
      (4 : ℝ) • realOutputCompression (T ∘L M ∘L T.adjoint - S ∘L M ∘L S.adjoint) := by
    rw [realQuadratureNormal_eq_four_realPart, realQuadratureNormal_eq_four_realPart,
      realOutputCompression_sub]
    ext1 x
    simp only [sub_apply, smul_apply, smul_sub]
  rw [h, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 4 by positivity)]
  exact mul_le_mul_of_nonneg_left (realOutputCompression_norm_le _) (by positivity)

/-- Transfer an input complex normal estimate to the real channel with factor four
(`app:ch_waves:eq:abstract-normal-two`, `app:ch_osc:cor:osc-real`).
The complex estimate is a premise, not an oscillatory estimate proved by this lemma. -/
theorem realQuadratureNormal_sub_norm_le_of_complex_bound
    (T S : E →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) (M : E →L[ℂ] E)
    {b : ℝ} (h : ‖T ∘L M ∘L T.adjoint - S ∘L M ∘L S.adjoint‖ ≤ b) :
    ‖realQuadratureNormal T M - realQuadratureNormal S M‖ ≤ 4 * b :=
  (realQuadratureNormal_sub_norm_le T S M).trans (mul_le_mul_of_nonneg_left h (by positivity))

end JanetCartan
