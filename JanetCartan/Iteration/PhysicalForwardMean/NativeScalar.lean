module

public import JanetCartan.Iteration.PhysicalSamplingShells.Realization
public import JanetCartan.Iteration.PhysicalMean.MomentRows
public import JanetCartan.Iteration.PhysicalMean.ScalarRow
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawBandBounds

/-!
# Exact native original scalar tester for the forward/adjoint mean estimates

This leaf identifies the actual same-event native scalar operator with the
shared moment-kernel convention. Its mask retains the physical Fourier scalar,
frequency HALF derivative, original smooth radial band, original real detector,
original square-root sample weights and unchanged prefix indicator. The native
measure already contains the annular restrictions, so NO annular indicator is
inserted into the mask. There is no individual-row or bare-scalar substitution.
The norm is the existing same-event full aggregated norm, with no band count.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open PhysicalSamplingShells PhysicalMean Sampling Sampling.Realization Sampling.RawKernel
open SamplingKernelBounds SeparatedSampling CanonicalRowComparison RawInputPartition NormalComparison

/-- The literal scalar band mask, including the physical Fourier factor and
exactly one original half derivative (`app:ch_mean_pairs:eq:block-normal`). -/
def forwardScalarBandMask (n : ℕ) (d : Euclidean (n - 1) → ℝ) (j : ℕ)
    (η : Euclidean (n - 1)) : ℝ :=
  (2 * Real.pi) ^ (-((n : ℝ) / 2)) * Real.sqrt ‖η‖ * d η * radialBand n j η

/-- Coordinate extraction from the actual scalar auxiliary kernel produces
exactly the full half-weighted scalar mask, not a bare channel kernel. -/
theorem scalarAuxiliaryKernel_scalarBandKernel_eq
    {n J : ℕ} {P : Type*} [TopologicalSpace P]
    (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n))
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℝ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦ S q.1.1 q.1.2 q.2))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous (fun η ↦ (d η : ℂ))) {B : ℝ} (hB : 0 ≤ B)
    (hdb : ∀ η, ‖(d η : ℂ)‖ ≤ B)
    (j : Fin J) (p : P) (x : Euclidean n) (η : Euclidean (n - 1)) :
    scalarBandKernel hn (scalarAuxiliaryKernel hn χ S ζ τ (fun η ↦ (d η : ℂ))
      hS hζ hτ hτ₀ hd hB hdb) (j,p) x η =
      (forwardScalarBandMask n d j.val η : ℂ) *
        oscillatoryFactor 1 (rawPrimaryPhaseDifference (S p) (ζ p) (τ p) x η) * (χ x : ℂ) := by
  unfold scalarBandKernel scalarAuxiliaryKernel
  rw [bandKernelData_kernel]
  simp only [PiLp.smul_apply, scalarAuxiliaryAmplitude_component, smul_eq_mul, Complex.real_smul,
    weightedRadialBand, forwardScalarBandMask, Complex.ofReal_mul,
    oscillatoryFactor, one_mul]
  ring_nf

variable {n J p : ℕ} {A : Type*} [Fintype A]
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- Evaluate the original phase at exactly the originally selected sample
carrier and color. This definition does not change the sample event. -/
def nativeForwardScalarPhase
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (φ : A → CP → Euclidean (n - 1) → Euclidean n → ℝ)
    (u : (SampleIndex p B ψ w h U × RefinedIndex J) × Euclidean (n - 1))
    (x : Euclidean n) : ℝ :=
  φ u.1.1.1 (color p u.1.1.2.val.1, node h (U u.1.1.1) u.1.1.2) u.2 x

/-- The SAME full native mask. Its band-mask argument is concretely
`forwardScalarBandMask`; no halfweight, sample weight or original prefix is
removed (`new:eq:amplitude-test`). -/
def nativeForwardScalarMask
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (b : A → Fin J → Euclidean (n - 1) → ℝ) (L : ℕ)
    (u : (SampleIndex p B ψ w h U × RefinedIndex J) × Euclidean (n - 1)) : ℝ :=
  if u.1.2.1.val < L then Real.sqrt (sampleWeight B ψ w h U u.1.1) * b u.1.1.1 u.1.2.1 u.2
  else 0

omit [Fintype A] in
/-- Literal equality of the actual aggregated scalar kernel with the moment
kernel, on the unchanged native shell measure. The input `hkernel` is an exact
coordinate formula, produced by `scalarAuxiliaryKernel_scalarBandKernel_eq`,
not an analytic success or operator-norm premise. -/
theorem nativeScalarKernel_eq_sampledMomentKernel (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (φ : A → CP → Euclidean (n - 1) → Euclidean n → ℝ)
    (b : A → Fin J → Euclidean (n - 1) → ℝ) (χ : Euclidean n → ℝ)
    (hkernel : ∀ a j q x η, scalarBandKernel hn (D a) (j,q) x η =
      (b a j η : ℂ) * oscillatoryFactor 1 (φ a q η x) * (χ x : ℂ))
    (x : Euclidean n)
    (u : (SampleIndex p B ψ w h U × RefinedIndex J) × Euclidean (n - 1)) :
    nativeScalarKernel hn B ψ w h U D L x u =
      sampledMomentKernel (nativeForwardScalarPhase B ψ w h U φ)
        (nativeForwardScalarMask B ψ w h U b L) (fun _ y ↦ (χ y : ℂ)) x u := by
  by_cases hj : u.1.2.1.val < L
  · simp only [nativeScalarKernel, nativeForwardScalarMask, hj, ite_true, hkernel,
      sampledMomentKernel, nativeForwardScalarPhase, Complex.ofReal_mul,
      Complex.star_def, Complex.conj_ofReal]
    ring
  · simp only [nativeScalarKernel, nativeForwardScalarMask, hj, ite_false,
      sampledMomentKernel, Complex.ofReal_zero, zero_mul]

/-- The actual original same-event scalar operator supplies `hT0` of the
forward and adjoint coordinate estimates, with ALL halfweights retained.
No new operator or sample is chosen (`app:ch_mean_pairs:eq:block-normal`). -/
theorem nativeScalarOperator_ae_sampledMomentKernel (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (φ : A → CP → Euclidean (n - 1) → Euclidean n → ℝ)
    (b : A → Fin J → Euclidean (n - 1) → ℝ) (χ : Euclidean n → ℝ)
    (hkernel : ∀ a j q x η, scalarBandKernel hn (D a) (j,q) x η =
      (b a j η : ℂ) * oscillatoryFactor 1 (φ a q η x) * (χ x : ℂ))
    (v : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J)) :
    nativeScalarOperator hn B ψ w h U D L v =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel (nativeForwardScalarPhase B ψ w h U φ)
        (nativeForwardScalarMask B ψ w h U b L) (fun _ y ↦ (χ y : ℂ)) x u * v u
          ∂sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J := by
  simpa only [nativeScalarKernel_eq_sampledMomentKernel hn B ψ w h U D L φ b χ hkernel] using
    nativeScalarOperator_ae_integral hn B ψ w h U D L v

end JanetCartan.PhysicalForwardMean
