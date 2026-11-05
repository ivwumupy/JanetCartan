module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PhysicalSeries
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MultiplierKernel

/-!
# Integral kernels of finite physical regularizations

For `app:ch_osc:lem:osc-amplitude`, compact physical cutoffs make every L² input
integrable before applying the compact-frequency multiplier. This identifies the
finite operator regularizations with literal oscillatory integrals.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace JanetCartan.AmplitudeBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The compact input cutoff in `app:ch_osc:lem:osc-amplitude` makes the
modulated L² input integrable; no extra L¹ assumption on the input is needed. -/
theorem integrable_cutoffModulation
    (q : E → Torus n) (hq : Measurable q) (ψ : E → ℂ)
    (hψ : AEStronglyMeasurable ψ) (hbound : ∀ᵐ y, ‖ψ y‖ ≤ 1)
    (hs : HasCompactSupport ψ) (k : Fin n → ℤ) (f : Lp (α := E) ℂ 2) :
    Integrable (cutoffModulation q hq ψ hψ hbound k f : E → ℂ) := by
  let g := cutoffModulation q hq ψ hψ hbound k f
  have hi := ((Lp.memLp g).locallyIntegrable (by norm_num)).integrableOn_isCompact hs
  apply (hi.integrable_indicator (isClosed_tsupport ψ).measurableSet).congr
  filter_upwards [cutoffModulation_coeFn q hq ψ hψ hbound k f] with y hy
  by_cases h : y ∈ tsupport ψ
  · simp only [Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem h]
    change 0 = cutoffModulation q hq ψ hψ hbound k f y
    rw [hy, image_eq_zero_of_notMem_tsupport h, zero_mul, zero_mul]

/-- Literal realization of one cutoff-modulated compact-frequency coefficient
in `app:ch_osc:lem:osc-amplitude`. -/
theorem cutoff_fourierMultiplier_ae_kernel
    (q r : E → Torus n) (hq : Measurable q) (hr : Measurable r)
    (χ ψ : E → ℂ) (hχ : AEStronglyMeasurable χ) (hψ : AEStronglyMeasurable ψ)
    (hχbound : ∀ᵐ x, ‖χ x‖ ≤ 1) (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1)
    (hs : HasCompactSupport ψ) (k : Fin n → ℤ) (ρ : ℝ)
    (a : Lp (α := E) ℂ ∞) (f : Lp (α := E) ℂ 2) :
    cutoffModulation q hq χ hχ hχbound k
      (fourierMultiplier (compactFrequencySymbol ρ a)
        (cutoffModulation r hr ψ hψ hψbound k f)) =ᵐ[volume]
      fun x ↦ ∫ ξ in Metric.closedBall 0 ρ, ∫ y,
        Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
          ((χ x * UnitAddTorus.mFourier k (q x)) * a ξ *
            (ψ y * UnitAddTorus.mFourier k (r y))) * f y := by
  let g := cutoffModulation r hr ψ hψ hψbound k f
  filter_upwards [cutoffModulation_coeFn q hq χ hχ hχbound k
    (fourierMultiplier (compactFrequencySymbol ρ a) g),
    fourierMultiplier_compactFrequencySymbol_ae_kernel ρ a g
      (integrable_cutoffModulation r hr ψ hψ hψbound hs k f)] with x hx hg
  rw [hx, hg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [cutoffModulation_coeFn r hr ψ hψ hψbound k f] with y hy
  change _ * (_ * a ξ * g y) = _
  change _ * (_ * a ξ * cutoffModulation r hr ψ hψ hψbound k f y) = _
  rw [hy]
  ring

/-- The finite physical Fourier amplitude in `app:ch_osc:lem:osc-amplitude`,
including both outer cutoffs. -/
def finiteCutoffAmplitude
    (q r : E → Torus n) (χ ψ : E → ℂ) (a : (Fin n → ℤ) → E → ℂ)
    (s : Finset (Fin n → ℤ)) (x y ξ : E) : ℂ :=
  ∑ k ∈ s, (χ x * UnitAddTorus.mFourier k (q x)) * a k ξ *
    (ψ y * UnitAddTorus.mFourier k (r y))

/-- Absolute integrability of each finite kernel term on frequency × input
position in `app:ch_osc:lem:osc-amplitude`. -/
theorem integrable_cutoff_coefficient_kernel
    (q r : E → Torus n) (hr : Measurable r)
    (χ ψ : E → ℂ) (hψ : AEStronglyMeasurable ψ)
    (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1) (hs : HasCompactSupport ψ)
    (k : Fin n → ℤ) (ρ : ℝ) (a : Lp (α := E) ℂ ∞)
    (f : Lp (α := E) ℂ 2) (x : E) :
    Integrable (fun p : E × E ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
        ((χ x * UnitAddTorus.mFourier k (q x)) * a p.1 *
          (ψ p.2 * UnitAddTorus.mFourier k (r p.2))) * f p.2)
      ((volume.restrict (Metric.closedBall 0 ρ)).prod volume) := by
  have hi : Integrable (fun y ↦ ψ y * UnitAddTorus.mFourier k (r y) * f y) :=
    (integrable_cutoffModulation r hr ψ hψ hψbound hs k f).congr
      (cutoffModulation_coeFn r hr ψ hψ hψbound k f)
  convert (integrable_compactFrequency_kernel ρ a hi x).const_mul
    (χ x * UnitAddTorus.mFourier k (q x)) using 1
  funext p
  ring

/-- Absolute convergence of the inner physical integral in each finite kernel
term of `app:ch_osc:lem:osc-amplitude`. -/
theorem integrable_cutoff_coefficient_kernel_inner
    (q r : E → Torus n) (hr : Measurable r)
    (χ ψ : E → ℂ) (hψ : AEStronglyMeasurable ψ)
    (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1) (hs : HasCompactSupport ψ)
    (k : Fin n → ℤ) (a : E → ℂ) (f : Lp (α := E) ℂ 2) (x ξ : E) :
    Integrable (fun y ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        ((χ x * UnitAddTorus.mFourier k (q x)) * a ξ *
          (ψ y * UnitAddTorus.mFourier k (r y))) * f y) := by
  have hi : Integrable (fun y ↦ ψ y * UnitAddTorus.mFourier k (r y) * f y) :=
    (integrable_cutoffModulation r hr ψ hψ hψbound hs k f).congr
      (cutoffModulation_coeFn r hr ψ hψ hψbound k f)
  convert (integrable_compactFrequency_kernel_inner a hi x ξ).const_mul
    (χ x * UnitAddTorus.mFourier k (q x)) using 1
  funext y
  ring

/-- The finite operator regularization is the literal oscillatory integral with
its finite Fourier amplitude (`app:ch_osc:lem:osc-amplitude`). Every L² input is
allowed because the physical input cutoff is compactly supported. -/
theorem regularizedAmplitudeOperator_cutoff_ae_kernel
    (q r : E → Torus n) (hq : Measurable q) (hr : Measurable r)
    (χ ψ : E → ℂ) (hχ : AEStronglyMeasurable χ) (hψ : AEStronglyMeasurable ψ)
    (hχbound : ∀ᵐ x, ‖χ x‖ ≤ 1) (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1)
    (hs : HasCompactSupport ψ) (a : (Fin n → ℤ) → Lp (α := E) ℂ ∞)
    (s : Finset (Fin n → ℤ)) (ρ : ℝ) (f : Lp (α := E) ℂ 2) :
    regularizedAmplitudeOperator
      (cutoffModulation q hq χ hχ hχbound)
      (cutoffModulation r hr ψ hψ hψbound) a s ρ f =ᵐ[volume]
      fun x ↦ ∫ ξ in Metric.closedBall 0 ρ, ∫ y,
        Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
          finiteCutoffAmplitude q r χ ψ (fun k ↦ a k) s x y ξ * f y := by
  classical
  let F (k : Fin n → ℤ) := cutoffModulation q hq χ hχ hχbound k
    (fourierMultiplier (compactFrequencySymbol ρ (a k))
      (cutoffModulation r hr ψ hψ hψbound k f))
  have he : regularizedAmplitudeOperator
      (cutoffModulation q hq χ hχ hχbound)
      (cutoffModulation r hr ψ hψ hψbound) a s ρ f = ∑ k ∈ s, F k := by
    simp [regularizedAmplitudeOperator, finiteAmplitudeOperator, modulatedTerm, F]
  rw [he]
  filter_upwards [Lp.coeFn_fun_finsetSum s F,
    (ae_all_iff.mpr fun k ↦ cutoff_fourierMultiplier_ae_kernel q r hq hr χ ψ
      hχ hψ hχbound hψbound hs k ρ (a k) f)] with x hx hk
  rw [hx]
  simp only [finiteCutoffAmplitude, Finset.mul_sum, Finset.sum_mul]
  have hinner (ξ : E) :
      (∫ y, ∑ k ∈ s, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        ((χ x * UnitAddTorus.mFourier k (q x)) * a k ξ *
          (ψ y * UnitAddTorus.mFourier k (r y))) * f y) =
      ∑ k ∈ s, ∫ y, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        ((χ x * UnitAddTorus.mFourier k (q x)) * a k ξ *
          (ψ y * UnitAddTorus.mFourier k (r y))) * f y :=
    integral_finsetSum s fun k _ ↦
      integrable_cutoff_coefficient_kernel_inner q r hr χ ψ hψ hψbound hs k (a k) f x ξ
  simp_rw [hinner]
  rw [integral_finsetSum s (fun k _ ↦
    (integrable_cutoff_coefficient_kernel q r hr χ ψ hψ hψbound hs k ρ (a k) f x).integral_prod_left)]
  exact Finset.sum_congr rfl fun k _ ↦ hk k

section Physical

variable {d : ℕ}
  (b : EuclideanSpace ℝ (Fin d) → Torus (2 * d) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  (hf : ∀ ξ, IsSmoothPeriodic (b ξ)) (A : ℝ)
  (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)
  (ℓ : ℝ) (χ ψ : EuclideanSpace ℝ (Fin d) → ℂ)
  (hχ : AEStronglyMeasurable χ) (hψ : AEStronglyMeasurable ψ)
  (hχbound : ∀ᵐ x, ‖χ x‖ ≤ 1) (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1)
  (hs : HasCompactSupport ψ)

/-- The literal finite oscillatory integral in `app:ch_osc:lem:osc-amplitude`,
using the amplitude's actual Fourier coefficients and the unit-period convention. -/
def regularizedPhysicalAmplitudeKernel (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ ξ in Metric.closedBall 0 ρ, ∫ y,
    Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
      finiteCutoffAmplitude (leftPositionChart ℓ) (rightPositionChart ℓ) χ ψ
        (fun k ξ ↦ UnitAddTorus.mFourierCoeff (b ξ) k) s x y ξ * f y

include hb hd hf hzero hderiv hχ hψ hχbound hψbound hs

/-- Identification of the concrete regularization with its literal integral in
`app:ch_osc:lem:osc-amplitude`. In particular the coefficient symbols' chosen
representatives introduce no compatibility assumption. -/
theorem regularizedPhysicalAmplitudeOperator_ae_kernel
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    regularizedPhysicalAmplitudeOperator b hb hd hf A hzero hderiv ℓ χ ψ
      hχ hψ hχbound hψbound s ρ f =ᵐ[volume]
        regularizedPhysicalAmplitudeKernel b ℓ χ ψ s ρ f := by
  apply (regularizedAmplitudeOperator_cutoff_ae_kernel
    (leftPositionChart ℓ) (rightPositionChart ℓ)
    (measurable_leftPositionChart ℓ) (measurable_rightPositionChart ℓ) χ ψ hχ hψ
    hχbound hψbound hs (periodicAmplitudeSymbol b hb hd hf A hzero hderiv) s ρ f).trans
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (ae_all_iff.mpr fun k ↦ periodicAmplitudeSymbol_coeFn b hb hd hf A hzero hderiv k)]
    with ξ hξ
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  exact Finset.sum_congr rfl fun k _ ↦ by
    dsimp only
    rw [hξ k]

/-- The literal finite oscillatory kernel maps every L² input into L²
(`app:ch_osc:lem:osc-amplitude`). -/
theorem memLp_regularizedPhysicalAmplitudeKernel
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    MemLp (regularizedPhysicalAmplitudeKernel b ℓ χ ψ s ρ f) 2 :=
  (memLp_congr_ae (regularizedPhysicalAmplitudeOperator_ae_kernel b hb hd hf A hzero
    hderiv ℓ χ ψ hχ hψ hχbound hψbound hs s ρ f)).mp (Lp.memLp _)

/-- The L² class of the literal finite integral in
`app:ch_osc:lem:osc-amplitude`. -/
def regularizedPhysicalAmplitudeKernelLp
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  MemLp.toLp (p := 2) (μ := volume)
    (regularizedPhysicalAmplitudeKernel b ℓ χ ψ s ρ f)
    (memLp_regularizedPhysicalAmplitudeKernel b hb hd hf A hzero hderiv
      ℓ χ ψ hχ hψ hχbound hψbound hs s ρ f)

/-- The L² realization of the literal integral equals the bounded operator
regularization (`app:ch_osc:lem:osc-amplitude`). -/
theorem toLp_regularizedPhysicalAmplitudeKernel
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    regularizedPhysicalAmplitudeKernelLp b hb hd hf A hzero hderiv
      ℓ χ ψ hχ hψ hχbound hψbound hs s ρ f =
    regularizedPhysicalAmplitudeOperator b hb hd hf A hzero hderiv ℓ χ ψ
      hχ hψ hχbound hψbound s ρ f := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (regularizedPhysicalAmplitudeOperator_ae_kernel b hb hd hf A hzero hderiv
      ℓ χ ψ hχ hψ hχbound hψbound hs s ρ f).symm

/-- Uniform L² bound for the literal finite regularized integrals in
`app:ch_osc:lem:osc-amplitude`. The constant is independent of both truncations. -/
theorem norm_regularizedPhysicalAmplitudeKernel_le
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ‖regularizedPhysicalAmplitudeKernelLp b hb hd hf A hzero hderiv
      ℓ χ ψ hχ hψ hχbound hψbound hs s ρ f‖ ≤
      ((coefficientSumConstant d * smoothCoefficientConstant d) * A) * ‖f‖ := by
  rw [toLp_regularizedPhysicalAmplitudeKernel]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right (norm_regularizedPhysicalAmplitudeOperator_le b hb hd hf
      A hzero hderiv ℓ χ ψ hχ hψ hχbound hψbound s ρ) (norm_nonneg f))

/-- Distributional removal of both truncations of the literal oscillatory
integrals in `app:ch_osc:lem:osc-amplitude`. This requires only exhaustion of the
finite physical sums and of frequency space. -/
theorem tendsto_regularizedPhysicalAmplitudeKernel_temperedDistribution
    {β : Type*} {m : Filter β} (s : β → Finset (Fin (2 * d) → ℤ)) (ρ : β → ℝ)
    (hsexhaust : ∀ k, ∀ᶠ j in m, k ∈ s j) (hρ : Filter.Tendsto ρ m Filter.atTop)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Filter.Tendsto (fun j ↦ Lp.toTemperedDistribution
      (regularizedPhysicalAmplitudeKernelLp b hb hd hf A hzero hderiv
        ℓ χ ψ hχ hψ hχbound hψbound hs (s j) (ρ j) f)) m
      (nhds (Lp.toTemperedDistribution (physicalAmplitudeOperator b hb hd hf A hzero hderiv
        ℓ χ ψ hχ hψ hχbound hψbound f))) := by
  simp_rw [toLp_regularizedPhysicalAmplitudeKernel]
  exact tendsto_regularizedPhysicalAmplitudeOperator_temperedDistribution b hb hd hf A
    hzero hderiv ℓ χ ψ hχ hψ hχbound hψbound s ρ hsexhaust hρ f

end Physical

end JanetCartan.AmplitudeBound
