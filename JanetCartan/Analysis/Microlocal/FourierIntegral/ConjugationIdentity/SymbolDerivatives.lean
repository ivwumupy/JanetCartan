module

public import JanetCartan.Analysis.Matrix.AdjugateSymbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Differentiating the normalized symbol identity

The derivative identities used by `two_term_transport_identity` in
`app:ch_regular_base:eq:direct-graph-identity` follow from the actual identity
`H c = h I`. All derivatives below are real Fréchet derivatives. The local
regularity assumptions allow the normalization to be singular at zero.
-/

@[expose] public noncomputable section

open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

variable {n r : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- First covector derivative of `H c = h I`, consumed by
`two_term_transport_identity` (`app:ch_regular_base:eq:direct-graph-identity`).
The derivative of the linear pencil is its actual coefficient matrix. -/
theorem pencil_mul_partialDeriv
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) 𝕜)
    (c : Euclidean n → Matrix (Fin r) (Fin r) 𝕜) (h : Euclidean n → 𝕜)
    (ξ : Euclidean n) (j : Fin n)
    (hc : DifferentiableAt ℝ c ξ) (hh : DifferentiableAt ℝ h ξ)
    (hid : (fun ζ ↦ H ζ * c ζ) =ᶠ[𝓝 ξ] fun ζ ↦ h ζ • 1) :
    H ξ * partialDeriv c ξ j =
      partialDeriv h ξ j • 1 - H (EuclideanSpace.single j 1) * c ξ := by
  have heq := ((H.hasFDerivAt.mul' hc.hasFDerivAt).congr_of_eventuallyEq
    hid.symm).unique (hh.hasFDerivAt.smul_const (1 : Matrix (Fin r) (Fin r) 𝕜))
  have hd := congrArg (fun L ↦ L (EuclideanSpace.single j 1)) heq
  exact eq_sub_iff_add_eq.mpr hd

/-- Second covector derivative of the same identity on an open symbol chart.
This supplies the second derivative premise of `two_term_transport_identity`
without assuming that premise (`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem pencil_mul_secondPartialDeriv
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) 𝕜)
    (c : Euclidean n → Matrix (Fin r) (Fin r) 𝕜) (h : Euclidean n → 𝕜)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (hc : ContDiffOn ℝ 2 c Ω) (hh : ContDiffOn ℝ 2 h Ω)
    (hid : ∀ ζ ∈ Ω, H ζ * c ζ = h ζ • 1)
    {ξ : Euclidean n} (hξ : ξ ∈ Ω) (j l : Fin n) :
    H ξ * partialDeriv (fun ζ ↦ partialDeriv c ζ l) ξ j =
      partialDeriv (fun ζ ↦ partialDeriv h ζ l) ξ j • 1 -
        H (EuclideanSpace.single j 1) * partialDeriv c ξ l -
        H (EuclideanSpace.single l 1) * partialDeriv c ξ j := by
  have hcx := hc.contDiffAt (hΩ.mem_nhds hξ)
  have hhx := hh.contDiffAt (hΩ.mem_nhds hξ)
  have dc : DifferentiableAt ℝ c ξ := hcx.differentiableAt (by norm_num)
  have dc1 : DifferentiableAt ℝ (fun ζ ↦ partialDeriv c ζ l) ξ :=
    ((hcx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have dh1 : DifferentiableAt ℝ (fun ζ ↦ partialDeriv h ζ l) ξ :=
    ((hhx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have heq : (fun ζ ↦ H ζ * partialDeriv c ζ l) =ᶠ[𝓝 ξ]
      fun ζ ↦ partialDeriv h ζ l • 1 - H (EuclideanSpace.single l 1) * c ζ := by
    filter_upwards [hΩ.mem_nhds hξ] with ζ hζ
    apply pencil_mul_partialDeriv H c h ζ l
    · exact (hc.contDiffAt (hΩ.mem_nhds hζ)).differentiableAt (by norm_num)
    · exact (hh.contDiffAt (hΩ.mem_nhds hζ)).differentiableAt (by norm_num)
    · filter_upwards [hΩ.mem_nhds hζ] with z hz using hid z hz
  have hder := ((H.hasFDerivAt.mul' dc1.hasFDerivAt).congr_of_eventuallyEq
    heq.symm).unique
      ((dh1.hasFDerivAt.smul_const (1 : Matrix (Fin r) (Fin r) 𝕜)).sub
        (dc.hasFDerivAt.const_mul (H (EuclideanSpace.single l 1))))
  have hd := congrArg (fun L ↦ L (EuclideanSpace.single j 1)) hder
  change H ξ * partialDeriv (fun ζ ↦ partialDeriv c ζ l) ξ j +
    H (EuclideanSpace.single j 1) * partialDeriv c ξ l =
      partialDeriv (fun ζ ↦ partialDeriv h ζ l) ξ j • 1 -
        H (EuclideanSpace.single l 1) * partialDeriv c ξ j at hd
  have hd' := eq_sub_iff_add_eq.mpr hd
  rw [hd']
  abel

/-- The actual normalized adjugate satisfies the first derivative identity in
`app:ch_regular_base:eq:direct-graph-identity`; invertibility is not used. -/
theorem mul_partialDeriv_normalizedAdjugateSymbol
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ)
    (ξ : Euclidean n) (j : Fin n)
    (hc : DifferentiableAt ℝ (normalizedAdjugateSymbol H) ξ)
    (hh : DifferentiableAt ℝ (normalizedDeterminantSymbol H) ξ) :
    H ξ * partialDeriv (normalizedAdjugateSymbol H) ξ j =
      partialDeriv (normalizedDeterminantSymbol H) ξ j • 1 -
        H (EuclideanSpace.single j 1) * normalizedAdjugateSymbol H ξ :=
  pencil_mul_partialDeriv H _ _ ξ j hc hh
    (Filter.Eventually.of_forall (mul_normalizedAdjugateSymbol H))

/-- The actual normalized adjugate satisfies the second derivative identity in
`app:ch_regular_base:eq:direct-graph-identity`. Smoothness is required only on
the supplied open chart, which may exclude the zero covector. -/
theorem mul_secondPartialDeriv_normalizedAdjugateSymbol
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (hc : ContDiffOn ℝ 2 (normalizedAdjugateSymbol H) Ω)
    (hh : ContDiffOn ℝ 2 (normalizedDeterminantSymbol H) Ω)
    {ξ : Euclidean n} (hξ : ξ ∈ Ω) (j l : Fin n) :
    H ξ * partialDeriv (fun ζ ↦ partialDeriv (normalizedAdjugateSymbol H) ζ l) ξ j =
      partialDeriv (fun ζ ↦ partialDeriv (normalizedDeterminantSymbol H) ζ l) ξ j • 1 -
        H (EuclideanSpace.single j 1) * partialDeriv (normalizedAdjugateSymbol H) ξ l -
        H (EuclideanSpace.single l 1) * partialDeriv (normalizedAdjugateSymbol H) ξ j :=
  pencil_mul_secondPartialDeriv H _ _ hΩ hc hh
    (fun ζ _ ↦ mul_normalizedAdjugateSymbol H ζ) hξ j l

/-- Symmetry of the actual phase Hessian, supplying the symmetry input to
`two_term_transport_identity` (`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem phase_secondPartialDeriv_symm (S : Euclidean n → ℝ) {x : Euclidean n}
    (hS : ContDiffAt ℝ 2 S x) (j l : Fin n) :
    partialDeriv (fun z ↦ partialDeriv S z l) x j =
      partialDeriv (fun z ↦ partialDeriv S z j) x l := by
  have hd := (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq (v : Euclidean n) :
      fderiv ℝ (fun z ↦ fderiv ℝ S z v) x = (fderiv ℝ (fderiv ℝ S) x).flip v := by
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  simp only [partialDeriv, heq, ContinuousLinearMap.flip_apply]
  exact hS.isSymmSndFDerivAt (by norm_num) _ _

end JanetCartan.FourierIntegral
