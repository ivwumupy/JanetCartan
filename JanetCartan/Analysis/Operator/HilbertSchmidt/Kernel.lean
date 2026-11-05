module

public import JanetCartan.Analysis.Operator.HilbertSchmidt.Trace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The squared-kernel integral

The kernel identity in the proof of `app:ch_waves:thm:sampling`. A kernel column
is a vector in the output Hilbert space, indexed by the scalar input space.
The hypothesis `HasAdjointKernel` connects it to the actual bounded operator
through the almost-everywhere formula for its adjoint; it assumes no norm estimate.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory

namespace JanetCartan

variable {𝕜 E ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The scalar L² norm as a squared integral (`app:ch_waves:thm:sampling`). -/
theorem l2_norm_sq_eq_integral (f : Lp 𝕜 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Exact adjoint action of the integral kernel (`app:ch_waves:thm:sampling`).
For `Tf = ∫ x, f x • k x`, the adjoint is `v ↦ (x ↦ ⟪k x, v⟫)`. -/
def HasAdjointKernel (T : Lp 𝕜 2 μ →L[𝕜] E) (k : X → E) : Prop :=
  ∀ v, (T.adjoint v : X → 𝕜) =ᵐ[μ] fun x ↦ inner 𝕜 (k x) v

/-- The squared-kernel integral is the Hilbert–Schmidt sum, including convergence
(`app:ch_waves:thm:sampling`). -/
theorem hasSum_adjoint_norm_sq_of_kernel [Countable ι]
    (b : HilbertBasis ι 𝕜 E) (T : Lp 𝕜 2 μ →L[𝕜] E) (k : X → E)
    (hk : MemLp k 2 μ) (hT : HasAdjointKernel T k) :
    HasSum (fun i ↦ ‖T.adjoint (b i)‖ ^ 2) (∫ x, ‖k x‖ ^ 2 ∂μ) := by
  have hp (x : X) := hilbertBasis_hasSum_sq_inner b (k x)
  have hs : HasSum (fun i ↦ ∫ x, ‖inner 𝕜 (b i) (k x)‖ ^ 2 ∂μ)
      (∫ x, ‖k x‖ ^ 2 ∂μ) := by
    apply hasSum_integral_of_dominated_convergence
      (fun i x ↦ ‖inner 𝕜 (b i) (k x)‖ ^ 2)
    · intro i
      exact ((hk.const_inner (b i)).aestronglyMeasurable.norm).pow 2
    · intro i
      exact Filter.Eventually.of_forall (fun x ↦ by simp)
    · exact Filter.Eventually.of_forall (fun x ↦ (hp x).summable)
    · simpa only [(hp _).tsum_eq] using
        (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).mp hk
    · exact Filter.Eventually.of_forall hp
  convert hs using 1
  ext i
  rw [l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hT (b i)] with x hx
  rw [hx, norm_inner_symm]

/-- A square-integrable kernel gives a Hilbert–Schmidt operator with exactly
the squared-kernel integral as its squared norm
(`app:ch_waves:thm:sampling`). -/
theorem HasAdjointKernel.hilbertSchmidtSq_eq_integral [Countable ι]
    {T : Lp 𝕜 2 μ →L[𝕜] E} {k : X → E} (hT : HasAdjointKernel T k)
    (hk : MemLp k 2 μ) (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 (Lp 𝕜 2 μ)) :
    IsHilbertSchmidt c T ∧ hilbertSchmidtSq c T = ∫ x, ‖k x‖ ^ 2 ∂μ := by
  have hs := hasSum_adjoint_norm_sq_of_kernel b T k hk hT
  obtain ⟨hA, heq⟩ := isHilbertSchmidt_adjoint b c T.adjoint hs.summable
  rw [ContinuousLinearMap.adjoint_adjoint] at hA heq
  exact ⟨hA, heq.trans hs.tsum_eq⟩

/-- The trace of the kernel normal is the squared-kernel integral
(`app:ch_waves:thm:sampling`). -/
theorem HasAdjointKernel.positiveTrace_normal_eq_integral [Countable ι]
    {T : Lp 𝕜 2 μ →L[𝕜] E} {k : X → E} (hT : HasAdjointKernel T k)
    (hk : MemLp k 2 μ) (b : HilbertBasis ι 𝕜 E) :
    positiveTrace b (T ∘L T.adjoint) = ∫ x, ‖k x‖ ^ 2 ∂μ := by
  rw [positiveTrace_normal]
  exact (hasSum_adjoint_norm_sq_of_kernel b T k hk hT).tsum_eq

/-- Square-integrable kernels give compact operators
(`app:ch_waves:thm:sampling`). -/
theorem HasAdjointKernel.isCompactOperator [Countable ι]
    {T : Lp 𝕜 2 μ →L[𝕜] E} {k : X → E} (hT : HasAdjointKernel T k)
    (hk : MemLp k 2 μ) (b : HilbertBasis ι 𝕜 E) : IsCompactOperator T := by
  obtain ⟨_, c, _⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 μ)
  exact (hT.hilbertSchmidtSq_eq_integral hk b c).1.isCompactOperator

/-- The same squared-kernel integral bounds every finite compression trace
(`app:ch_waves:thm:sampling`). -/
theorem HasAdjointKernel.trace_finiteCompression_normal_le_integral [Countable ι]
    {T : Lp 𝕜 2 μ →L[𝕜] E} {k : X → E} (hT : HasAdjointKernel T k)
    (hk : MemLp k 2 μ) (b : HilbertBasis ι 𝕜 E)
    (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] :
    RCLike.re (LinearMap.trace 𝕜 U (finiteCompression U (T ∘L T.adjoint)).toLinearMap) ≤
      ∫ x, ‖k x‖ ^ 2 ∂μ := by
  obtain ⟨_, c, _⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 μ)
  obtain ⟨hc, heq⟩ := hT.hilbertSchmidtSq_eq_integral hk b c
  exact (trace_finiteCompression_normal_le c T hc U).trans_eq heq

omit [CompleteSpace E] in
include 𝕜 in
/-- The vector-valued L² squared norm as an integral
(`app:ch_waves:thm:sampling`). -/
theorem l2_vector_norm_sq_eq_integral (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := 𝕜) f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

/-- The full squared-kernel double integral for vector-valued L² output
(`app:ch_waves:thm:sampling`). -/
theorem HasAdjointKernel.positiveTrace_normal_eq_double_integral [Countable ι]
    {T : Lp 𝕜 2 μ →L[𝕜] Lp E 2 ν} {k : X → Lp E 2 ν}
    (hT : HasAdjointKernel T k) (hk : MemLp k 2 μ)
    (b : HilbertBasis ι 𝕜 (Lp E 2 ν)) (K : X → Y → E)
    (hK : ∀ᵐ x ∂μ, (k x : Y → E) =ᵐ[ν] K x) :
    positiveTrace b (T ∘L T.adjoint) = ∫ x, ∫ y, ‖K x y‖ ^ 2 ∂ν ∂μ := by
  rw [hT.positiveTrace_normal_eq_integral hk b]
  apply integral_congr_ae
  filter_upwards [hK] with x hx
  rw [l2_vector_norm_sq_eq_integral (𝕜 := 𝕜)]
  exact integral_congr_ae (hx.mono (fun _ h ↦ congrArg (fun z ↦ ‖z‖ ^ 2) h))

variable [NormedSpace ℝ E]

/-- The adjoint-kernel relation implies the actual synthesis integral
(`app:ch_waves:thm:sampling`). -/
theorem HasAdjointKernel.apply_eq_integral
    {T : Lp 𝕜 2 μ →L[𝕜] E} {k : X → E} (hT : HasAdjointKernel T k)
    (hk : MemLp k 2 μ) (f : Lp 𝕜 2 μ) : T f = ∫ x, f x • k x ∂μ := by
  have hi : Integrable (fun x ↦ f x • k x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).smul hk)
  apply ext_inner_left 𝕜
  intro y
  rw [← T.adjoint_inner_left, L2.inner_def, ← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [hT y] with x hx
  simp only [hx, inner_smul_right, RCLike.inner_apply, inner_conj_symm, mul_comm]

/-- The actual synthesis integral implies the adjoint-kernel relation
(`app:ch_waves:thm:sampling`). -/
theorem hasAdjointKernel_of_apply_eq_integral
    {T : Lp 𝕜 2 μ →L[𝕜] E} {k : X → E} (hk : MemLp k 2 μ)
    (hT : ∀ f : Lp 𝕜 2 μ, T f = ∫ x, f x • k x ∂μ) : HasAdjointKernel T k := by
  intro y
  let g := (hk.inner_const y).toLp (fun x ↦ inner 𝕜 (k x) y)
  have hg : (g : X → 𝕜) =ᵐ[μ] (fun x ↦ inner 𝕜 (k x) y) := MemLp.coeFn_toLp _
  have heq : T.adjoint y = g := by
    apply ext_inner_right 𝕜
    intro f
    have hi : Integrable (fun x ↦ f x • k x) μ :=
      memLp_one_iff_integrable.mp ((Lp.memLp f).smul hk)
    rw [T.adjoint_inner_left, hT f, ← integral_inner hi, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    simp only [hx, inner_smul_right, RCLike.inner_apply, inner_conj_symm, mul_comm]
  rw [heq]
  exact hg

end JanetCartan
