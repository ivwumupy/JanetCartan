module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterKernel
public import JanetCartan.Iteration.PhysicalMean.CanonicalQuadraticProfile
public import JanetCartan.Iteration.PhysicalForwardMean.SingleScalar

/-!
# The native scalar tester with the restored original carrier mask

The aggregate tester and the individual row use the SAME mask: the spatial
incidence/spectator factor times the bare detector and radial band. Only the
aggregate has the square-root outer node mass and the half derivative, exactly
as in `app:ch_mean_pairs:eq:block-fields`. Multiply only the scalar output by
χcoeff, on whose support each original patch cutoff is already one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace JanetCartan.PhysicalSampling.OriginalCoefficientTester
open PhysicalSamplingShells Sampling SeparatedSampling SamplingKernelBounds
open RawInputPartition CanonicalRowComparison PhysicalMean PhysicalForwardMean NormalComparison

/-- Contract the actual full-prefix exterior operator, retain its outer measure
and restore the literal no-half-derivative node amplitude *before* applying
`originalWeightedHalfMask`. There is no assumption on the norm of the result. -/
theorem restrict_outer_native {A : Type*} [Fintype A] {n J p : ℕ} (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ)
    (D Dout : A → BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n)
    (φ : A → ((Fin 3 → Fin (p+1)) × Point) → Euclidean (n-1) → Euclidean n → ℝ)
    (detector : A → Euclidean (n-1) → ℝ) (a : A → Point → ℝ) (χrow : A → Euclidean n → ℝ)
    (χ : Euclidean n → ℝ) (hc : Continuous χ) (hr : ∀ x, χ x ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ i x, x ∈ tsupport χ → χrow i x = 1)
    (hkernel : ∀ i j q x η, scalarBandKernel hn (D i) (j,q) x η =
      (forwardScalarBandMask n (detector i) j.val η : ℂ)*oscillatoryFactor 1 (φ i q η x)*(χrow i x : ℂ))
    (houter : ∀ i j c z x η, scalarBandKernel hn (Dout i) (j,c,z) x η =
      (a i z : ℂ)*scalarBandKernel hn (D i) (j,c,z) x η)
    (h : ℝ) (U : A → Lattice → Point) :
    let T := nativeScalarOperator hn B ψ w h U Dout J
    let mass := sampleWeight B ψ w h U
    let m := fun (u : (SampleIndex p B ψ w h U × RefinedIndex J) × Euclidean (n-1)) ↦
      a u.1.1.1 (node h (U u.1.1.1) u.1.1.2) * singleBareScalarMask (detector u.1.1.1) (u.1.2,u.2)
    ‖restrictOutput χ hc hr T‖ ≤ ‖T‖ ∧
      ∀ f : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J),
        restrictOutput χ hc hr T f =ᵐ[volume] fun x ↦ ∫ u,
          sampledMomentKernel (nativeForwardScalarPhase B ψ w h U φ) (originalWeightedHalfMask mass m)
            (fun _ y ↦ (χ y : ℂ)) x u * f u ∂sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J := by
  intro T mass m
  apply restricted_moment_kernel _ _ _ (fun u x ↦ χrow u.1.1.1 x) χ hc hr (fun u ↦ hplateau u.1.1.1) T
  intro f
  refine (nativeScalarOperator_ae_integral hn B ψ w h U Dout J f).trans ?_
  apply Filter.Eventually.of_forall
  intro x
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [nativeScalarKernel, u.1.2.1.isLt, ite_true, houter, hkernel, nativeForwardScalarPhase,
    sampledMomentKernel, originalWeightedHalfMask, m, mass,
    Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [singleBareScalarMask,forwardScalarBandMask,Complex.ofReal_mul]
  ring

end JanetCartan.PhysicalSampling.OriginalCoefficientTester
