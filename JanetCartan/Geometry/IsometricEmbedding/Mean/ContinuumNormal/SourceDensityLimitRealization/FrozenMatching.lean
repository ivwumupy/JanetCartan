module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.Weights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenMatching

/-!
# Retain the initialized frozen carrier

Only the origin-weighted branch is identified with the old frozen carrier.
Equality of literal kernels gives equality on dense tests, so no independent
existential operators are identified without proof. Consumer: the frozen
branch of `exists_initialized_density_limit_coercivity_of_retained_geometry`
(`bg-Nsigma`, `bg-full-complex-amplitude`, `bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport ActualFlow FlowAmplitude
open CarrierVariation.FamilyInputs.PositiveReference

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {V : Set CarrierParameter}
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ z ∈ V, (densityFootpoint T Y (0, z)).2 = parameter z)
    (hangular : ∀ z η, angular z η ≠ 0 → z ∈ V)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)

include hzero hparam hangular

/-- The origin-weighted kernel equals the existing initialized frozen
kernel on every actually used support. This assertion deliberately does not
apply to the divided-footpoint weight (`bg-Nsigma`, `bg-frame`). -/
theorem originWeighted_kernel_eq_initialized :
    let e₀ := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0
    let ef := normalizedCarrierData T Q F row col Φ Y (fun q ↦ Real.sqrt (1 + v q))
      hr hcell angular high 0
    carrierKernel (weightNormal e₀ (fun p ↦ Real.sqrt (1 + v (0, parameter p.2)))) =
      carrierKernel ef := by
  intro e₀ ef
  funext x z
  by_cases hz : angular z.1 (‖z.2‖⁻¹ • z.2) = 0
  · simp [carrierKernel, carrierAmplitude, weightNormal, e₀, ef, normalizedCarrierData, data, hz]
  have hzV := hangular z.1 (‖z.2‖⁻¹ • z.2) hz
  have hinit : Y (0, (0, parameter z.1)) = (0, parameter z.1) := by
    have he : densityFootpoint T Y (0, z.1) = (0, parameter z.1) :=
      Prod.ext (hzero z.1 hzV) (hparam z.1 hzV)
    simpa [densityFootpoint_eq, coordinates_apply, adaptedCoordinates_apply] using he
  have hnormal (x : Euclidean n) : ef.normalField x z.1 =
      Real.sqrt (1 + v (0, parameter z.1)) • e₀.normalField x z.1 := by
    change normalizedNormal T Q F row col Φ Y _ 0 x z.1 = _
    rw [normalizedNormal_zero, frozenSeedNormal_initial_factor, hinit]
    congr 1
    exact (normalizedNormal_zero T Q F row col Φ Y (fun _ ↦ 1) x z.1).symm
  by_cases hx : x ∈ e₀.outputChart
  · have hxf : x ∈ ef.outputChart := hx
    simp only [carrierKernel, weightNormal, indicator_of_mem hx, indicator_of_mem hxf]
    change Complex.exp _ • euclideanComplexInclusion
      (carrierAmplitude (weightNormal e₀ (fun p ↦ Real.sqrt (1 + v (0, parameter p.2)))) x z) =
      Complex.exp _ • euclideanComplexInclusion (carrierAmplitude ef x z)
    congr 2
    dsimp [carrierAmplitude, weightNormal]
    rw [hnormal]
    rfl
  · have hxf : x ∉ ef.outputChart := hx
    simp only [carrierKernel, weightNormal, indicator_of_notMem hx, indicator_of_notMem hxf]

/-- Dense literal test actions identify the constructed origin branch with
any supplied initialized frozen carrier. The supplied operator is retained;
its normal can therefore be transported from the constructed realization
(`bg-frame`, `bg-full-complex-amplitude`). -/
theorem originWeighted_realization_eq_initialized
    (Vorigin Vfrozen : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (horigin : ∀ f : carrierInitialTestSpace n,
      Vorigin (carrierInitialTestToLp f) =ᵐ[volume]
        carrierTestIntegral (weightNormal
          (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0)
          (fun p ↦ Real.sqrt (1 + v (0, parameter p.2)))) f.val)
    (hfrozen : ∀ f : carrierInitialTestSpace n,
      Vfrozen (carrierInitialTestToLp f) =ᵐ[volume]
        carrierTestIntegral
          (normalizedCarrierData T Q F row col Φ Y (fun q ↦ Real.sqrt (1 + v q))
            hr hcell angular high 0) f.val) : Vorigin = Vfrozen := by
  have hk := originWeighted_kernel_eq_initialized T Q F row col Φ Y hr hcell angular high
    hzero hparam hangular v
  apply DFunLike.coe_injective
  apply denseRange_carrierInitialTestToLp.equalizer Vorigin.continuous Vfrozen.continuous
  funext f
  apply Lp.ext
  have hi := congrArg (fun k : Torus n → CarrierVariable n → EuclideanSpace ℂ (Fin n) ↦
    fun x ↦ ∫ z, f.val z • k x z ∂carrierMeasure n) hk
  filter_upwards [horigin f, hfrozen f] with x hx hy
  exact hx.trans ((congrFun hi x).trans hy.symm)

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
