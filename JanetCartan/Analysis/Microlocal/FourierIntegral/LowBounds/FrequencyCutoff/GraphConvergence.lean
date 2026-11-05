module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.VectorGraph
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Tests

/-!
# Literal frequency cut graphs in vector Lebesgue L²

The Schwartz Fourier moments give an explicit common bound on a fixed compact
output support. This supplies the dominator for Step 1 of
`app:ch_regular_base:thm:actual-calculus`, before any bounded uncut operator is
constructed. The consumers are the low-frequency cutoff assembly and its
Fatou/density extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff

variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Literal frequency cut amplitude in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. -/
def cutAmplitude (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (j : ℕ) (x η : Euclidean n) := complexPhysicalCutoff j η • A x η

/-- Continuity of the literal cut amplitude (same Step 1). -/
theorem cutAmplitude_continuous
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hA : Continuous (Function.uncurry A)) (j : ℕ) :
    Continuous (Function.uncurry (cutAmplitude A j)) :=
  ((complexPhysicalCutoff_contDiff j).continuous.comp continuous_snd).smul hA

/-- The literal frequency cut has compact joint support without a physical
source cutoff (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem cutAmplitude_hasCompactSupport
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hsA : ∀ x η, x ∉ K → A x η = 0) (j : ℕ) :
    HasCompactSupport (Function.uncurry (cutAmplitude A j)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hK.prod (complexPhysicalCutoff_hasCompactSupport (n := n) j))
  intro p hp
  constructor
  · by_contra hx
    exact hp (by simp [Function.uncurry, cutAmplitude, hsA p.1 p.2 hx])
  · by_contra hη
    exact hp (by simp [Function.uncurry, cutAmplitude, image_eq_zero_of_notMem_tsupport hη])

/-- Frequency truncation preserves the polynomial majorant, for the common
Schwartz dominator in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem cutAmplitude_norm_le
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {C : ℝ} {k : ℕ} (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (j : ℕ) (x η : Euclidean n) :
    ‖cutAmplitude A j x η‖ ≤ C * (1 + ‖η‖ ^ k) := by
  exact (norm_smul_le _ _).trans
    ((mul_le_mul_of_nonneg_right (complexPhysicalCutoff_norm_le j η) (norm_nonneg _)).trans
      (by simpa using hb x η))

/-- Explicit integrable frequency majorant from Schwartz moments and the
matrix action; consumed by the output bound in the same Step 1. -/
def schwartzFrequencyMajorant (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (C : ℝ) (k : ℕ) (η : Euclidean n) : ℝ :=
  (sourceMatrixAction (r := r)).opNorm * C *
    (‖sourceInputFourierTransform u η‖ + ‖η‖ ^ k * ‖sourceInputFourierTransform u η‖)

/-- The required moments are integrable because the physical Fourier transform
is Schwartz (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem schwartzFrequencyMajorant_integrable
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (C : ℝ) (k : ℕ) :
    Integrable (schwartzFrequencyMajorant u C k) :=
  ((sourceInputFourierTransform u).integrable.norm.add
    ((sourceInputFourierTransform u).integrable_pow_mul volume k)).const_mul _

private theorem sourceFourierIntegrand_norm_le
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (C : ℝ) (k : ℕ)
    (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) (x η : Euclidean n) :
    ‖Complex.exp (Complex.I * (S x η : ℂ)) •
      (A x η).mulVec (sourceInputFourierTransform u η)‖ ≤ schwartzFrequencyMajorant u C k η := by
  simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc
    _ ≤ (sourceMatrixAction (r := r)).opNorm * ‖A x η‖ *
        ‖sourceInputFourierTransform u η‖ := (sourceMatrixAction (r := r)).le_opNorm₂ _ _
    _ ≤ (sourceMatrixAction (r := r)).opNorm * (C * (1 + ‖η‖ ^ k)) *
        ‖sourceInputFourierTransform u η‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb x η) (sourceMatrixAction (r := r)).opNorm_nonneg)
        (norm_nonneg _)
    _ = _ := by unfold schwartzFrequencyMajorant; ring

/-- Explicit common output bound in the actual finite complex Euclidean fiber.
It depends only on Schwartz Fourier moments, the polynomial bound and finite
matrix/fiber conversion norms. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def schwartzGraphBound (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (C : ℝ) (k : ℕ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap‖ *
    ‖((2 * Real.pi) ^ n : ℂ)⁻¹‖ * ∫ η, schwartzFrequencyMajorant u C k η

/-- The literal source-first graph satisfies the explicit output bound. No
bounded graph operator is assumed (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem graphOperator_norm_le_schwartzGraphBound
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (C : ℝ) (k : ℕ)
    (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) (x : Euclidean n) :
    ‖WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)‖ ≤
      schwartzGraphBound u C k := by
  rw [graphOperator_eq_sourceFourierIntegral]
  refine ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap.le_opNorm _).trans ?_
  rw [norm_smul]
  unfold schwartzGraphBound
  rw [mul_assoc]
  gcongr
  exact norm_integral_le_of_norm_le (schwartzFrequencyMajorant_integrable u C k)
    (Eventually.of_forall (sourceFourierIntegrand_norm_le S A u C k hb x))

/-- Continuity in the output variable follows from the same integrable Schwartz
majorant, for Step 1 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem graphOperator_continuous
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    Continuous (fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) := by
  simp_rw [graphOperator_eq_sourceFourierIntegral]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
  apply Continuous.smul (M := ℂ) continuous_const
  apply continuous_of_dominated (bound := schwartzFrequencyMajorant u C k)
  · intro x
    exact (sourceFourierIntegral_integrable S A u x
      (hS.comp (continuous_const.prodMk continuous_id))
      (hA.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable C k (hb x)).1
  · exact fun x ↦ Eventually.of_forall (sourceFourierIntegrand_norm_le S A u C k hb x)
  · exact schwartzFrequencyMajorant_integrable u C k
  · apply Eventually.of_forall
    intro η
    have hs := hS.comp (continuous_id.prodMk (continuous_const (y := η)))
    have ha := hA.comp (continuous_id.prodMk (continuous_const (y := η)))
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp hs))).smul (ha.matrix_mulVec continuous_const)


/-- Output support of the source-independent literal graph, for the compact
L² dominator in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphOperator_eq_zero_of_notMem
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) {K : Set (Euclidean n)}
    (hsA : ∀ x η, x ∉ K → A x η = 0) {x : Euclidean n} (hx : x ∉ K) :
    graphOperator S (fun z _ η ↦ A z η) u x = 0 := by
  simp [graphOperator_eq_sourceFourierIntegral, hsA x _ hx]

/-- The explicit bound times the indicator of the fixed compact output support
is a genuine L² dominator (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem schwartzGraphBound_indicator_memLp
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (C : ℝ) (k : ℕ)
    {K : Set (Euclidean n)} (hK : IsCompact K) :
    MemLp (K.indicator (fun _ ↦ schwartzGraphBound u C k)) 2 volume :=
  memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet _ (Or.inr hK.measure_lt_top.ne)

/-- Domination by the compact output indicator, with no assumed operator bound
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem graphOperator_norm_le_indicator
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    {K : Set (Euclidean n)} (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) (x : Euclidean n) :
    ‖WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)‖ ≤
      K.indicator (fun _ ↦ schwartzGraphBound u C k) x := by
  by_cases hx : x ∈ K
  · simpa [hx] using graphOperator_norm_le_schwartzGraphBound S A u C k hb x
  · simp [hx, graphOperator_eq_zero_of_notMem S A u hsA hx]

/-- The uncut graph on Schwartz data already belongs to vector Lebesgue L²,
using only polynomial growth and compact output support. This is the target
of the cutoff limit in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphOperator_memLp
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    MemLp (fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) 2 volume :=
  (schwartzGraphBound_indicator_memLp u C k hK).mono'
    (graphOperator_continuous S A u hS hA C k hb).aestronglyMeasurable
    (Eventually.of_forall (graphOperator_norm_le_indicator S A u hsA C k hb))

/-- Literal cut graphs belong to the same finite-complex-fiber Lebesgue L²
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem cutGraphOperator_memLp
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) (j : ℕ) :
    MemLp (fun x ↦ WithLp.toLp 2
      (graphOperator S (fun z _ η ↦ cutAmplitude A j z η) u x)) 2 volume :=
  graphOperator_memLp S (cutAmplitude A j) u hS (cutAmplitude_continuous hA j) hK
    (fun x η hx ↦ by simp [cutAmplitude, hsA x η hx]) C k (cutAmplitude_norm_le hb j)

private theorem tendsto_toLp_of_common_bound
    {f : ℕ → Euclidean n → EuclideanSpace ℂ (Fin r)}
    {g : Euclidean n → EuclideanSpace ℂ (Fin r)} {b : Euclidean n → ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume) (hb : MemLp b 2 volume)
    (hfb : ∀ j x, ‖f j x‖ ≤ b x) (hgb : ∀ x, ‖g x‖ ≤ b x)
    (hlim : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x))) :
    Tendsto (fun j ↦ (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr
  have hi : Integrable (fun x ↦ ‖‖b x‖ + ‖b x‖‖ ^ 2) volume :=
    (hb.norm.add hb.norm).integrable_norm_pow (by norm_num)
  have ht : Tendsto (fun j ↦ ∫ x, ‖f j x - g x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have ht := tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖‖b x‖ + ‖b x‖‖ ^ 2)
      (fun j ↦ ((hf j).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      hi (fun j ↦ Eventually.of_forall (fun x ↦ show ‖‖f j x - g x‖ ^ 2‖ ≤ _ from by
        rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity)]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add
          ((hfb j x).trans (le_abs_self _)) ((hgb x).trans (le_abs_self _)))))
      (Eventually.of_forall (fun x ↦ (show Tendsto (fun j ↦ ‖f j x - g x‖ ^ 2)
        atTop (𝓝 (‖g x - g x‖ ^ 2)) from ((hlim x).sub tendsto_const_nhds).norm.pow 2)))
    simpa using ht
  have he (j : ℕ) : eLpNorm (f j - g) 2 volume =
      ENNReal.ofReal ((∫ x, ‖f j x - g x‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
    simpa using MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤) ((hf j).sub hg)
  simp_rw [he]
  simpa only [Function.comp_def, Real.zero_rpow (by positivity : (2 : ℝ)⁻¹ ≠ 0),
    ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (ht.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)))

/-- Strong L² convergence of the literal frequency cut graphs on Schwartz
inputs. The common dominator was derived from Fourier moments and compact
output support; neither graph convergence nor bounded uncut operators are
premises. Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphOperator_tendsto_L2
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    Tendsto (fun j ↦ (cutGraphOperator_memLp S A u hS hA hK hsA C k hb j).toLp
      (fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ cutAmplitude A j z η) u x)))
      atTop (𝓝 ((graphOperator_memLp S A u hS hA hK hsA C k hb).toLp
        (fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)))) := by
  apply tendsto_toLp_of_common_bound _ _ (schwartzGraphBound_indicator_memLp u C k hK)
  · intro j
    exact graphOperator_norm_le_indicator S (cutAmplitude A j) u
      (fun x η hx ↦ by simp [cutAmplitude, hsA x η hx]) C k (cutAmplitude_norm_le hb j)
  · exact graphOperator_norm_le_indicator S A u hsA C k hb
  · intro x
    exact (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).continuousAt.tendsto.comp
      (graphOperator_tendsto S A u x (hS.comp (continuous_const.prodMk continuous_id))
        (hA.comp (continuous_const.prodMk continuous_id)) C k (hb x))


/-- Coordinate continuity for the existing compact graph realization, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem cutAmplitude_entry_continuous
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hA : Continuous (Function.uncurry A)) (j : ℕ) (i l : Fin r) :
    Continuous (fun p : Euclidean n × Euclidean n ↦ cutAmplitude A j p.1 p.2 i l) :=
  (continuous_apply l).comp ((continuous_apply i).comp (cutAmplitude_continuous hA j))

/-- Coordinate compact support for the existing compact graph realization,
for `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem cutAmplitude_entry_hasCompactSupport
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hsA : ∀ x η, x ∉ K → A x η = 0) (j : ℕ) (i l : Fin r) :
    HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ cutAmplitude A j p.1 p.2 i l) :=
  (cutAmplitude_hasCompactSupport hK hsA j).comp_left (g := fun M : Matrix (Fin r) (Fin r) ℂ ↦ M i l) (by simp)

/-- Schwartz inputs in the actual finite-complex-fiber Lebesgue L², used to
identify the compact graphs in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def schwartzVectorToLp (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) :=
  ((u.memLp 2 volume).continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap).toLp
      (fun x ↦ WithLp.toLp 2 (u x))

/-- The L² input has the actual Schwartz representative (same Step 1). -/
theorem schwartzVectorToLp_ae (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    schwartzVectorToLp u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (u x) :=
  MemLp.coeFn_toLp _

/-- The existing compact graph realization, applied to actual Schwartz data,
agrees with the literal graph integral. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem compactVectorGraph_schwartz_ae
    {S : Euclidean n → Euclidean n → ℝ}
    {A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i l, Continuous (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i l))
    (hsA : ∀ i l, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 i l))
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    compactVectorGraph hS hA hsA (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x) := by
  have hi (l : Fin r) : Integrable (fun y ↦ schwartzVectorToLp u y l) := by
    apply (u.integrable.eval l).congr
    filter_upwards [schwartzVectorToLp_ae u] with y hy
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin r) ↦ v l) hy).symm
  refine (compactVectorGraph_ae_graphOperator hS hA hsA _ hi).trans ?_
  apply Eventually.of_forall
  intro x
  dsimp only
  apply congrArg (WithLp.toLp 2)
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [schwartzVectorToLp_ae u] with y hy
  rw [hy]

/-- The L² value of each literal cut graph is exactly the value of the existing
constructed compact vector operator. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem compactVectorGraph_cut_eq_toLp
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) (j : ℕ) :
    compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
        (cutAmplitude_entry_hasCompactSupport hK hsA j) (schwartzVectorToLp u) =
      (cutGraphOperator_memLp S A u hS hA hK hsA C k hb j).toLp
        (fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ cutAmplitude A j z η) u x)) := by
  apply Lp.ext
  exact (compactVectorGraph_schwartz_ae hS (cutAmplitude_entry_continuous hA j)
    (cutAmplitude_entry_hasCompactSupport hK hsA j) u).trans (MemLp.coeFn_toLp _).symm

/-- The constructed compact vector operators converge on each Schwartz input to
its literal uncut graph in L². This is consumed by the low-bound Fatou/density
extension (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem compactVectorGraph_cut_tendsto
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ))
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    Tendsto (fun j ↦ compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j) (schwartzVectorToLp u)) atTop
      (𝓝 ((graphOperator_memLp S A u hS hA hK hsA C k hb).toLp
        (fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)))) := by
  simp_rw [compactVectorGraph_cut_eq_toLp S A u hS hA hK hsA C k hb]
  exact graphOperator_tendsto_L2 S A u hS hA hK hsA C k hb

/-- Actual Schwartz conversion of the existing compact smooth graph tests;
its values are the original coordinate functions, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def graphTestToSchwartz (u : graphTestSpace n r) :
    SchwartzMap (Euclidean n) (Fin r → ℂ) :=
  (u.property.2.comp_left (g := WithLp.ofLp) (by rfl)).toSchwartzMap
    (PiLp.contDiff_ofLp.comp u.property.1)

/-- Conversion preserves every value of the test input (same Step 1). -/
@[simp] theorem graphTestToSchwartz_apply (u : graphTestSpace n r) (x : Euclidean n) :
    graphTestToSchwartz u x = WithLp.ofLp (u.val x) := rfl

/-- The Schwartz conversion has exactly the pre-existing L² inclusion of
compact smooth tests (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
@[simp] theorem schwartzVectorToLp_graphTestToSchwartz (u : graphTestSpace n r) :
    schwartzVectorToLp (graphTestToSchwartz u) = graphTestToLp u := by
  apply Lp.ext
  exact (schwartzVectorToLp_ae _).trans (graphTest_memLp u).coeFn_toLp.symm

/-- The original compact smooth test domain satisfies the literal cutoff limit
in the actual vector Lebesgue L². This is the dense domain consumed by the
low-bound extension in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem compactVectorGraph_cut_tendsto_graphTest
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : graphTestSpace n r)
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    Tendsto (fun j ↦ compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j) (graphTestToLp u)) atTop
      (𝓝 ((graphOperator_memLp S A (graphTestToSchwartz u) hS hA hK hsA C k hb).toLp
        (fun x ↦ WithLp.toLp 2
          (graphOperator S (fun z _ η ↦ A z η) (fun y ↦ WithLp.ofLp (u.val y)) x)))) := by
  have hu : (graphTestToSchwartz u : Euclidean n → Fin r → ℂ) =
      (fun y ↦ WithLp.ofLp (u.val y)) := rfl
  simpa only [schwartzVectorToLp_graphTestToSchwartz, hu] using
    compactVectorGraph_cut_tendsto S A (graphTestToSchwartz u) hS hA hK hsA C k hb

end JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
