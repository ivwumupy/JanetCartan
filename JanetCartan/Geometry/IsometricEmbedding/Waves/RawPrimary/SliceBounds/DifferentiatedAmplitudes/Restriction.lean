module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Branches

/-!
# Exact restriction of physical differentiation branches

The physical derivatives in `app:ch_waves:eq:individual-raw-slice` are taken
before freezing time, epsilon, or the input variable. Affine restriction of
the joint branches gives exactly the branches of the restricted field. This
connects the joint chart estimates to `rawSliceBandDerivativeAmplitude`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary.SliceBounds

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The branch construction is local, so equality on the original buffered
chart suffices for every physical order
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem eventuallyEq_sliceDerivativeAmplitude {φ ψ : E → ℝ} {A B : E → F}
    {x : E} (hφ : φ =ᶠ[𝓝 x] ψ) (hA : A =ᶠ[𝓝 x] B)
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) :
    sliceDerivativeAmplitude φ A v b =ᶠ[𝓝 x] sliceDerivativeAmplitude ψ B v b := by
  induction s with
  | zero => exact hA
  | succ s ih =>
    rcases b with ⟨b, t⟩
    have ht := ih (Fin.tail v) t
    cases b
    · filter_upwards [ht.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun f : E →L[ℝ] F ↦ f (v 0)) hy
    · filter_upwards [hφ.fderiv (𝕜 := ℝ), ht] with y hy hz
      simp only [sliceDerivativeAmplitude, ↓reduceIte, hy, hz]

/-- Affine restriction preserves each exact branch, with every physical
direction pushed forward by the same linear map. In particular time
derivatives can be taken before restriction to a spatial slice
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceDerivativeAmplitude_comp_affine
    {U : Set H} (hU : IsOpen U) {φ : H → ℝ} {A : H → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    (T : E →L[ℝ] H) (c : H) {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s)
    {x : E} (hx : c + T x ∈ U) :
    sliceDerivativeAmplitude (fun y ↦ φ (c + T y)) (fun y ↦ A (c + T y)) v b x =
      sliceDerivativeAmplitude φ A (fun i ↦ T (v i)) b (c + T x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rcases b with ⟨b, t⟩
    have hg : HasFDerivAt (fun y ↦ c + T y) T x := T.hasFDerivAt.const_add c
    have hpre : IsOpen ((fun y ↦ c + T y) ⁻¹' U) := hU.preimage (by fun_prop)
    have he : sliceDerivativeAmplitude (fun y ↦ φ (c + T y))
        (fun y ↦ A (c + T y)) (Fin.tail v) t =ᶠ[𝓝 x]
        (fun y ↦ sliceDerivativeAmplitude φ A (fun i ↦ T (Fin.tail v i)) t (c + T y)) := by
      filter_upwards [hpre.mem_nhds hx] with y hy
      exact ih (Fin.tail v) t hy
    cases b
    · change fderiv ℝ _ x (v 0) = _
      rw [he.fderiv_eq]
      have ht := contDiffOn_sliceDerivativeAmplitude hU hφ hA
        (fun i ↦ T (Fin.tail v i)) t
      have hd := ((ht.contDiffAt (hU.mem_nhds hx)).differentiableAt
        (by simp)).hasFDerivAt.comp x hg
      exact congrArg (fun f : E →L[ℝ] F ↦ f (v 0)) hd.fderiv
    · have hd := ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt
        (by simp)).hasFDerivAt.comp x hg
      simp only [sliceDerivativeAmplitude, ↓reduceIte]
      simp only [Function.comp_def] at hd
      rw [hd.fderiv, he.eq_of_nhds]
      rfl

end JanetCartan.RawPrimary.SliceBounds
