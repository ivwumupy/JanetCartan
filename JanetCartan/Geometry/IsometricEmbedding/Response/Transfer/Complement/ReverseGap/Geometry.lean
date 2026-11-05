module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import JanetCartan.Analysis.Calculus.BufferedInverse
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Source-gradient geometry for the reverse complement

These are conditional geometric deductions for
`app:ch_response:thm:response-literal-transfer`. In particular the derivative
gap below must hold on an entire convex buffered chart. Pointwise invertibility
of `mixedPhaseMatrix` alone does not provide the inverse estimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace JanetCartan.ResponseTransfer

/-- Degree-one phase homogeneity gives degree-one homogeneity of the physical
source gradient, using equality on a neighborhood of `x`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem sourceGradient_smul_of_phase_homogeneous {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {x ζ : Euclidean n} {ρ : ℝ}
    (hS : DifferentiableAt ℝ (fun y ↦ S y ζ) x)
    (hhom : ∀ᶠ y in 𝓝 x, S y (ρ • ζ) = ρ * S y ζ) :
    gradient (fun y ↦ S y (ρ • ζ)) x = ρ • gradient (fun y ↦ S y ζ) x := by
  have heq : (fun y ↦ S y (ρ • ζ)) =ᶠ[𝓝 x] (fun y ↦ ρ * S y ζ) := hhom
  rw [heq.gradient_eq]
  simp only [gradient, fderiv_const_mul hS, map_smul]

/-- The reverse demodulated phase uses `x` as its source variable. This identity
connects the shared `phaseIncrement` with the gap in the complete-complement
paragraph of `app:ch_response:thm:response-literal-transfer`. No Fourier `2π`
factor is inserted: `θ`, `η`, and `ρ • ζ` are physical covectors. -/
theorem gradient_reverse_phaseIncrement {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {x ζ η θ : Euclidean n} {ρ : ℝ}
    (hη : DifferentiableAt ℝ (fun y ↦ S y η) x)
    (hζρ : DifferentiableAt ℝ (fun y ↦ S y (ρ • ζ)) x) :
    gradient (fun y ↦ -phaseIncrement S ζ ρ y (η - ρ • ζ) + inner ℝ θ y) x =
      gradient (fun y ↦ S y (ρ • ζ)) x - gradient (fun y ↦ S y η) x + θ := by
  have heq : (fun y ↦ -phaseIncrement S ζ ρ y (η - ρ • ζ) + inner ℝ θ y) =
      (fun y ↦ S y (ρ • ζ) - S y η + inner ℝ θ y) := by
    funext y
    simp [phaseIncrement]
  rw [heq]
  have hinner := (InnerProductSpace.toDual ℝ (Euclidean n) θ).hasFDerivAt (x := x)
  have hder : fderiv ℝ (fun y ↦ S y (ρ • ζ) - S y η + inner ℝ θ y) x =
      fderiv ℝ (fun y ↦ S y (ρ • ζ)) x - fderiv ℝ (fun y ↦ S y η) x +
        InnerProductSpace.toDual ℝ (Euclidean n) θ := by
    simpa only [Pi.sub_def, Pi.add_def, InnerProductSpace.toDual_apply_apply] using
      ((hζρ.hasFDerivAt.sub hη.hasFDerivAt).add hinner).fderiv
  change (InnerProductSpace.toDual ℝ (Euclidean n)).symm _ = _
  rw [hder, map_add, map_sub]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The shared mixed matrix is exactly the coordinate matrix of the derivative
of `η ↦ S_x(x,η)`. Thus the derivative-gap hypothesis below concerns the actual
`mixedPhaseMatrix`, with no change of Euclidean norm or coordinate convention
(`app:ch_response:thm:response-literal-transfer`). -/
theorem mixedPhaseMatrix_eq_sourceGradient_derivative {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (x η : Euclidean n)
    (hS : DifferentiableAt ℝ (fun ξ ↦ gradient (fun y ↦ S y ξ) x) η)
    (i j : Fin n) :
    FourierIntegral.mixedPhaseMatrix S x η i j =
      (fderiv ℝ (fun ξ ↦ gradient (fun y ↦ S y ξ) x) η
        (EuclideanSpace.single j 1)) i := by
  have heq : (fun ξ ↦ partialDeriv (fun y ↦ S y ξ) x i) =
      (fun ξ ↦ (gradient (fun y ↦ S y ξ) x) i) := by
    funext ξ
    have h := inner_gradient_left (𝕜 := ℝ) (f := fun y ↦ S y ξ)
      (x := x) (y := EuclideanSpace.single i 1)
    simpa only [partialDeriv, EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply,
      star_trivial] using h.symm
  unfold FourierIntegral.mixedPhaseMatrix
  rw [heq]
  unfold partialDeriv
  have hd : fderiv ℝ (fun ξ ↦ (gradient (fun y ↦ S y ξ) x) i) η =
      (EuclideanSpace.proj i).comp (fderiv ℝ (fun ξ ↦ gradient (fun y ↦ S y ξ) x) η) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      ((EuclideanSpace.proj i).hasFDerivAt.comp η hS.hasFDerivAt).fderiv
  rw [hd]
  rfl

/-- A normalized half-size derivative gap on the full convex chart gives its
quantitative inverse estimate, uniformly whenever the reference inverse norm
is bounded by `C`. This is the explicit producer obligation for
`reverseSource_gap_uniform`, from `app:lem:buffered-inverse-stability` and the
complete complement of `app:ch_response:thm:response-literal-transfer`. -/
theorem reverseSource_inverse_bound_of_derivative_gap {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {x : Euclidean n}
    {D : Set (Euclidean n)} (hD : Convex ℝ D)
    (G : Euclidean n ≃L[ℝ] Euclidean n) {C : ℝ}
    (hG : ‖(G.symm : Euclidean n →L[ℝ] Euclidean n)‖ ≤ C)
    (hS : ∀ η ∈ D, DifferentiableAt ℝ (fun ξ ↦ gradient (fun y ↦ S y ξ) x) η)
    (hgap : ∀ η ∈ D,
      ‖(G.symm : Euclidean n →L[ℝ] Euclidean n).comp
        (fderiv ℝ (fun ξ ↦ gradient (fun y ↦ S y ξ) x) η) -
          ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ 1 / 2) :
    ∀ u ∈ D, ∀ v ∈ D, ‖u - v‖ ≤
      (2 * C) * ‖gradient (fun y ↦ S y u) x - gradient (fun y ↦ S y v) x‖ := by
  intro u hu v hv
  have hl := normalized_lower_lipschitz_of_derivative_gap hD G hS hgap hu hv
  have hn := (G.symm : Euclidean n →L[ℝ] Euclidean n).le_opNorm
    (gradient (fun y ↦ S y u) x - gradient (fun y ↦ S y v) x)
  have hb := mul_le_mul_of_nonneg_right hG
    (norm_nonneg (gradient (fun y ↦ S y u) x - gradient (fun y ↦ S y v) x))
  change ‖G.symm (gradient (fun y ↦ S y u) x - gradient (fun y ↦ S y v) x)‖ ≤
    ‖(G.symm : Euclidean n →L[ℝ] Euclidean n)‖ *
      ‖gradient (fun y ↦ S y u) x - gradient (fun y ↦ S y v) x‖ at hn
  nlinarith

/-- The full topological support of the shared complementary amplitude stays
outside the selector's inner neighborhood. No part of the original amplitude
is discarded, so radial/angular shoulders and bounded-frequency pieces are
retained (`app:ch_response:thm:response-literal-transfer`). -/
theorem tsupport_complementaryAmplitude_subset_far {n r : ℕ}
    (A : FourierIntegral.FullAmplitude n r) (ζ : Euclidean n) (ρ c : ℝ)
    (q : Euclidean n → ℂ) (hq : ∀ δ, ‖δ‖ < c * ρ → q δ = 1)
    (x y : Euclidean n) :
    tsupport (fun η ↦ complementaryAmplitude A ζ ρ q x y η) ⊆
      {η | c * ρ ≤ ‖η - ρ • ζ‖} := by
  apply closure_minimal
  · intro η hη
    change complementaryAmplitude A ζ ρ q x y η ≠ 0 at hη
    by_contra hfar
    have hqη := hq (η - ρ • ζ) (lt_of_not_ge hfar)
    exact hη (by simp [complementaryAmplitude, hqη])
  · exact isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)

end JanetCartan.ResponseTransfer
