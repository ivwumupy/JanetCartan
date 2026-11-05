module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Basic

/-!
# The compact graph normal in cycle frequency

The first identity in Step 1 of `app:ch_regular_base:thm:actual-calculus` is
proved for the actual compact graph. The source has Lebesgue measure and no
physical cutoff. The averaged-gradient chart is required only for positions
in the output carrier. Its hypotheses are primitive geometry, to be supplied
by `jc-hamilton-phase` and `jc-compatible-phase-geometry`.

This leaf proves the exact kernel substitution, including the cancellation of
the physical `(2π)⁻ⁿ` prefactor. Uniform derivative bounds, identification with
the bounded PDO, and removal of the frequency cutoff are separate obligations
of `LowBounds`; none is an assumption or a conclusion of this leaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds

open NormalComparison NormalKernel

variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Primitive chart data for `app:ch_regular_base:eq:actual-normal-amplitude`.
Only physical output pairs in `K` require phase differentiability. Thus this
interface imposes no smoothness at the zero covector when `0 ∉ D`.
The Hamilton and compatible-geometry producers must instantiate every field. -/
structure AveragedGradientChart (S : E → E → ℝ) (K D : Set E)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E) (δ : ℝ) : Prop where
  measurable : MeasurableSet D
  gap_pos : 0 < δ
  segment : ∀ x ∈ K, ∀ y ∈ K, ∀ u ∈ D, ∀ t ∈ uIcc (0 : ℝ) 1,
    DifferentiableAt ℝ (fun z ↦ S z u) (y + t • (x - y))
  integrable : ∀ x ∈ K, ∀ y ∈ K, ∀ u ∈ D, IntervalIntegrable
    (fun t : ℝ ↦ fderiv ℝ (fun z ↦ S z u) (y + t • (x - y))) volume 0 1
  derivative : ∀ x ∈ K, ∀ y ∈ K, ∀ u ∈ D,
    HasFDerivWithinAt (averagedGradient S x y) (J x y u) D u
  injective : ∀ x ∈ K, ∀ y ∈ K, InjOn (averagedGradient S x y) D
  leftInverse : ∀ x ∈ K, ∀ y ∈ K, ∀ u ∈ D,
    η x y (averagedGradient S x y u) = u
  gap : ∀ x ∈ K, ∀ y ∈ K, ∀ u ∈ D, δ ≤ |(J x y u).det|

/-- The existing zero-extended full cross amplitude evaluated at the physical
covector `2πξ`. Both output positions and both amplitude cutoffs remain present
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def cycleCrossNormalAmplitude (D : Set E) (S : E → E → ℝ)
    (A B : E → E → Matrix (Fin r) (Fin r) ℂ)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (x y ξ : E) : Matrix (Fin r) (Fin r) ℂ :=
  extendedCrossNormalAmplitude
    {q | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}
    A B η J (x, y, (2 * Real.pi) • ξ)

/-- Entrywise change of variables for the literal complete cross-normal kernel
in `app:ch_regular_base:eq:actual-normal-kernel`. The support hypotheses allow
the geometry to be used only on the physical output carrier. No transformed
amplitude estimate or operator identity is assumed. -/
theorem crossNormalEntry_eq_cycleIntegral
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    (A B : E → E → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hB : ∀ y u, y ∉ K → B y u = 0)
    (x y : E) (i j : Fin r) :
    ((2 * Real.pi) ^ n : ℂ)⁻¹ * (∫ u,
      Complex.exp (Complex.I * ((S x u - S y u : ℝ) : ℂ)) *
        (A x u * (B y u).conjTranspose) i j) =
    ∫ ξ, Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) *
      cycleCrossNormalAmplitude D S A B η J x y ξ i j := by
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · let F : E → ℂ := fun u ↦
        Complex.exp (Complex.I * ((S x u - S y u : ℝ) : ℂ)) *
          (A x u * (B y u).conjTranspose) i j
      have hrestrict : (∫ u, F u) = ∫ u in D, F u := by
        apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
        intro u hu
        simp [F, hA x u (Or.inr hu)]
      have himage := measurable_image_of_fderivWithin G.measurable
        (G.derivative x hx y hy) (G.injective x hx y hy)
      have hsub : (∫ u, F u) = ∫ ξ,
          Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) *
            extendedCrossNormalAmplitude
              {q | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}
              A B η J (x, y, ξ) i j := by
        rw [hrestrict, integral_eq_inverse_jacobian_integral D G.measurable
          (averagedGradient S x y) (η x y) (J x y)
          (G.derivative x hx y hy) (G.injective x hx y hy)
          (G.leftInverse x hx y hy)
          (fun u hu ↦ abs_pos.mp (G.gap_pos.trans_le (G.gap x hx y hy u hu))),
          ← integral_indicator himage]
        apply integral_congr_ae
        filter_upwards [] with ξ
        by_cases hξ : ξ ∈ averagedGradient S x y '' D
        · obtain ⟨u, hu, rfl⟩ := hξ
          simp only [indicator_of_mem (mem_image_of_mem _ hu)]
          rw [G.leftInverse x hx y hy u hu]
          have hp := phase_sub_eq_inner_averagedGradient S x y u
            (G.segment x hx y hy u hu) (G.integrable x hx y hy u hu)
          rw [extendedCrossNormalAmplitude, indicator_of_mem
            (show (x, y, averagedGradient S x y u) ∈
              {q : NormalVariables n | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}
              from mem_image_of_mem _ hu)]
          simp only [crossNormalAmplitude, crossNormalNumerator,
            G.leftInverse x hx y hy u hu, F, hp, Matrix.smul_apply,
            Complex.real_smul]
          ring
        · rw [indicator_of_notMem hξ, extendedCrossNormalAmplitude,
            indicator_of_notMem (show (x, y, ξ) ∉
              {q : NormalVariables n | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}
              from hξ)]
          simp
      change ((2 * Real.pi) ^ n : ℂ)⁻¹ * (∫ u, F u) = _
      rw [hsub]
      have hscale := Measure.integral_comp_smul_of_nonneg volume
        (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) *
          extendedCrossNormalAmplitude
            {q | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}
            A B η J (x, y, ξ) i j)
        (2 * Real.pi) (hR := by positivity)
      simp only [Euclidean, finrank_euclideanSpace_fin, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat] at hscale
      rw [← hscale]
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [cycleCrossNormalAmplitude, inner_smul_right, Complex.ofReal_mul]
      congr 2
      ring
    · have hz : ∀ u, B y u = 0 := fun u ↦ hB y u hy
      simp [cycleCrossNormalAmplitude, extendedCrossNormalAmplitude,
        crossNormalAmplitude, crossNormalNumerator, hz, Set.indicator]
  · have hz : ∀ u, A x u = 0 := fun u ↦ hA x u (Or.inl hx)
    simp [cycleCrossNormalAmplitude, extendedCrossNormalAmplitude,
      crossNormalAmplitude, crossNormalNumerator, hz, Set.indicator]

/-- The actual compact graph cross normal, after averaged-gradient substitution
and conversion to Mathlib cycle frequency. This proves the complete kernel
identity required by `app:ch_regular_base:eq:actual-normal-amplitude` on every
Euclidean L² input, with no physical source cutoff and no assumed normal map. -/
theorem compactGraph_cross_ae_cycleIntegral
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    {A B : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : E × E ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : E × E ↦ B p.1 p.2 j k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hcarrierB : ∀ y u, y ∉ K → B y u = 0)
    (f : NormalOutputL2 n r) (i : Fin r) :
    (compactGraph hS hA hsA ((compactGraph hS hB hsB).adjoint f)) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, (∫ ξ,
        Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) *
          cycleCrossNormalAmplitude D S A B η J x y ξ i j) * f j y := by
  have he := compactGraph_cross_ae hS hA hsA hB hsB f i
  simp_rw [crossNormalEntry_eq_cycleIntegral G A B hcarrierA hcarrierB] at he
  exact he

end JanetCartan.FourierIntegral.LowBounds
