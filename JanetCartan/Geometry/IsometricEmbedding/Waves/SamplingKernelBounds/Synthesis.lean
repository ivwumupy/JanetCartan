module

public import JanetCartan.Analysis.Operator.HilbertSchmidt.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Spaces

/-!
# Bounded synthesis from actual square-integrable columns

The kernel construction used by `app:ch_waves:eq:sampling-operator-bounds`.
The only analytic input here is square integrability of the columns; neither an
operator nor its adjoint formula is assumed. The actual oscillatory columns and
their uniform estimates are supplied separately.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace JanetCartan.SamplingKernelBounds

/-- The full complex output in `app:ch_waves:thm:sampling`, with Lebesgue measure. -/
abbrev Output (n : ℕ) := Lp (EuclideanSpace ℂ (Fin n)) 2
  (volume : Measure (Euclidean n))

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {k : X → E}

/-- The analysis map of the columns, used to construct the band operator in
`app:ch_waves:eq:sampling-operator-bounds`. -/
def kernelAnalysis (hk : MemLp k 2 μ) : E →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    ({ toFun := fun v ↦ (hk.inner_const (𝕜 := ℂ) v).toLp (fun x ↦ inner ℂ (k x) v)
       map_add' := fun v w ↦ by
        simpa only [inner_add_right, Pi.add_def] using
          (hk.inner_const (𝕜 := ℂ) v).toLp_add (hk.inner_const (𝕜 := ℂ) w)
       map_smul' := fun c v ↦ by
        simpa only [inner_smul_right, Pi.smul_def, smul_eq_mul, RingHom.id_apply] using
          (hk.inner_const (𝕜 := ℂ) v).toLp_const_smul c } : E →ₗ[ℂ] Lp ℂ 2 μ)
    ‖hk.toLp k‖ (fun v ↦ by
      change ‖(hk.inner_const (𝕜 := ℂ) v).toLp _‖ ≤ ‖hk.toLp k‖ * ‖v‖
      rw [mul_comm]
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (hk.inner_const (𝕜 := ℂ) v), MemLp.coeFn_toLp hk]
        with x h₁ h₂
      rw [h₁, h₂, mul_comm]
      exact norm_inner_le_norm _ _)

/-- The bounded integral operator for `app:ch_waves:eq:sampling-operator-bounds`. -/
def kernelSynthesis (hk : MemLp k 2 μ) : Lp ℂ 2 μ →L[ℂ] E :=
  (kernelAnalysis hk).adjoint

/-- Literal adjoint formula for the constructed operator
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem kernelSynthesis_hasAdjointKernel (hk : MemLp k 2 μ) :
    HasAdjointKernel (kernelSynthesis hk) k := by
  intro v
  rw [kernelSynthesis, ContinuousLinearMap.adjoint_adjoint]
  exact MemLp.coeFn_toLp (hk.inner_const (𝕜 := ℂ) v)

/-- The constructed operator is the actual integral, not an unspecified
realization (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem kernelSynthesis_apply [NormedSpace ℝ E] (hk : MemLp k 2 μ)
    (f : Lp ℂ 2 μ) : kernelSynthesis hk f = ∫ x, f x • k x ∂μ :=
  (kernelSynthesis_hasAdjointKernel hk).apply_eq_integral hk f

/-- Squared-kernel control, used for parameter continuity in
`app:ch_waves:eq:sampling-operator-bounds`. This is not the sharper oscillatory
bound of order `K`, which remains a separate analytic input. -/
theorem norm_kernelSynthesis_sq_le (hk : MemLp k 2 μ) :
    ‖kernelSynthesis hk‖ ^ 2 ≤ ∫ x, ‖k x‖ ^ 2 ∂μ := by
  have h : ‖kernelSynthesis hk‖ ≤ ‖hk.toLp k‖ := by
    rw [kernelSynthesis, ContinuousLinearMap.adjoint.norm_map]
    unfold kernelAnalysis
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    _ ≤ ‖hk.toLp k‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    _ = ∫ x, ‖k x‖ ^ 2 ∂μ := by
      rw [l2_vector_norm_sq_eq_integral (𝕜 := ℂ)]
      exact integral_congr_ae ((MemLp.coeFn_toLp hk).mono
        (fun _ hx ↦ congrArg (fun v ↦ ‖v‖ ^ 2) hx))

/-- The difference of two synthesis operators is synthesis with the literal
kernel difference (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem kernelSynthesis_sub {l : X → E} (hk : MemLp k 2 μ) (hl : MemLp l 2 μ) :
    kernelSynthesis hk - kernelSynthesis hl = kernelSynthesis (hk.sub hl) := by
  apply ContinuousLinearMap.adjoint.injective
  simp only [kernelSynthesis, map_sub, ContinuousLinearMap.adjoint_adjoint]
  ext1 v
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (kernelAnalysis hk v) (kernelAnalysis hl v),
    MemLp.coeFn_toLp (hk.inner_const (𝕜 := ℂ) v),
    MemLp.coeFn_toLp (hl.inner_const (𝕜 := ℂ) v),
    MemLp.coeFn_toLp ((hk.sub hl).inner_const (𝕜 := ℂ) v)] with x hs hkx hlx hdx
  change ((kernelAnalysis hk v - kernelAnalysis hl v) : Lp ℂ 2 μ) x = _
  rw [hs]
  calc
    _ = inner ℂ (k x) v - inner ℂ (l x) v := congrArg₂ (· - ·) hkx hlx
    _ = inner ℂ ((k - l) x) v := by simp only [Pi.sub_apply, inner_sub_left]
    _ = _ := hdx.symm

/-- Squared-kernel domination of the operator difference, the estimate needed
for parameter continuity (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_kernelSynthesis_sub_sq_le {l : X → E}
    (hk : MemLp k 2 μ) (hl : MemLp l 2 μ) :
    ‖kernelSynthesis hk - kernelSynthesis hl‖ ^ 2 ≤ ∫ x, ‖k x - l x‖ ^ 2 ∂μ := by
  rw [kernelSynthesis_sub]
  exact norm_kernelSynthesis_sq_le (hk.sub hl)

end JanetCartan.SamplingKernelBounds
