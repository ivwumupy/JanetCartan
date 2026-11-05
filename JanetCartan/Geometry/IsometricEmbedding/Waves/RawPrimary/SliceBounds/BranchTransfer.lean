module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Exact component transfer for differentiated amplitudes

The primitive input constructor `exists_rawSlicePrimitiveBranchNormalData`
uses the finite component function space. Its consumer
`exists_wideBandSliceOperator` uses the Euclidean complex norm. The identities
below identify their SAME differentiation branches, including derivatives in
time, without an extra derivative-identity premise
(`app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section

namespace JanetCartan.RawPrimary.SliceBounds

variable {X F H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private theorem sliceDerivativeAmplitude_comp_equiv (e : F ≃L[ℂ] H)
    (φ : X → ℝ) (A : X → F) {s : ℕ} (v : Fin s → X)
    (b : SliceDerivativeBranch s) (x : X) :
    sliceDerivativeAmplitude φ (e ∘ A) v b x = e (sliceDerivativeAmplitude φ A v b x) := by
  let eR : F ≃L[ℝ] H :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rcases b with ⟨b, t⟩
    cases b
    · simp only [sliceDerivativeAmplitude, Bool.false_eq_true, ↓reduceIte]
      have he : sliceDerivativeAmplitude φ (e ∘ A) (Fin.tail v) t =
          eR ∘ sliceDerivativeAmplitude φ A (Fin.tail v) t := by
        funext y
        exact ih (Fin.tail v) t y
      rw [he, ContinuousLinearEquiv.comp_fderiv]
      rfl
    · simp only [sliceDerivativeAmplitude, ↓reduceIte]
      rw [ih, map_smul]

/-- The primitive component branch is exactly the Euclidean-vector branch
used by the channel operator. No smoothness or norm assertion is hidden in
this conversion (`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceDerivativeAmplitude_toLp {r : ℕ} (φ : X → ℝ)
    (A : X → Fin r → ℂ) {s : ℕ} (v : Fin s → X)
    (b : SliceDerivativeBranch s) (x : X) :
    sliceDerivativeAmplitude φ (fun y ↦ WithLp.toLp 2 (A y)) v b x =
      WithLp.toLp 2 (sliceDerivativeAmplitude φ A v b x) :=
  sliceDerivativeAmplitude_comp_equiv (PiLp.continuousLinearEquiv 2 ℂ _).symm φ A v b x

/-- The exact `L^(s-q)` normalization commutes with component conversion.
Together with `sliceDerivativeAmplitude_toLp`, this connects the primitive
normal-data producer to the unchanged integral branches
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem normalizedSliceDerivativeAmplitude_toLp {r : ℕ} (φ : X → ℝ)
    (A : X → Fin r → ℂ) {s : ℕ} (v : Fin s → X)
    (b : SliceDerivativeBranch s) (L : ℝ) (x : X) :
    normalizedSliceDerivativeAmplitude φ (fun y ↦ WithLp.toLp 2 (A y)) v b L x =
      WithLp.toLp 2 (normalizedSliceDerivativeAmplitude φ A v b L x) := by
  simp only [normalizedSliceDerivativeAmplitude, sliceDerivativeAmplitude_toLp]
  rfl

end JanetCartan.RawPrimary.SliceBounds
