module

public import JanetCartan.Iteration.PhysicalForwardMean.SingleForward
public import JanetCartan.Iteration.PhysicalForwardMean.SingleScalar

/-!
# Actual original individual raw forward frontend

This specializes the individual k+1/2 forward bound to scalar36's actual
original native bare kernel. Every qualitative scalar-mask/phase premise and
exact tester factorization is proved, not re-assumed. Only the SAME full-A13
profiles and SAME normalized full-phase28 profiles/germs remain quantitative
inputs of the parent mean14 construction. This is not an unconditional Main
claim until that common original-data parent is instantiated.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open PhysicalMean PhysicalSamplingShells PhysicalScalarChannel RawInputPartition
open Sampling Sampling.MeasuredAmplitude SamplingKernelBounds
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ContinuumRow Pseudodifferential AmplitudeBound

variable {m J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
local notation "I" => RefinedIndex J
local notation "E" => Euclidean (m + 1)
local notation "Eta" => Euclidean (m + 1 - 1)
local notation "X" => I × Eta
local notation "μ" => annularShellMeasure (n := m + 1) (refinedRadius (J := J))

/-- Exact original FULL individual raw operator with scalar36's BARE tester,
original native shell measure and sharp k+1/2 input moments. Scalar geometry,
cutoffs and the halfweight are not additional success premises. The remaining
full amplitude/phase profiles have the independent actual producers13/28
(`app:ch_mean_pairs:eq:block-fields`). -/
theorem originalSingleForward_physical_halfMoment_bounds
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : E → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
    (χ : ContDiffBump (0 : E)) (center : E × (Euclidean 3 × Eta))
    {ρ : ℝ} (hρ : 0 < ρ) (τ : ℝ) (z : Euclidean 3)
    {ηb : Eta} {r : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r)
    (Φ : I → Eta → E → ℝ) (A : I → Eta → E → ℂ)
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (hA : ∀ i, ContDiff ℝ ∞ (Function.uncurry (A i)))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ i η, tsupport (A i η) ⊆ K)
    (hagree : ∀ u : X, singleBareScalarMask (originalForwardDetector hηb hr) u ≠ 0 →
      ∀ x ∈ K, singleRetainedForwardPhase T Q center hρ τ z u x = Φ u.1 u.2 x)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s0 : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hAj : ∀ i η, singleBareScalarMask (originalForwardDetector hηb hr) (i,η) ≠ 0 →
      ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (A i η) x‖ ≤
        a j * Λ ^ (j - (s0 + ((m + 1) / 2 + 1))))
    (hΦj : ∀ i η, singleBareScalarMask (originalForwardDetector hηb hr) (i,η) ≠ 0 →
      ∀ x ∈ K, ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y / ‖η‖) x‖ ≤
        p j * Λ ^ (j - 1 - (s0 + ((m + 1) / 2 + 1))))
    (Tbare : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hTbare : ∀ f : Lp ℂ 2 μ, Tbare f =ᵐ[volume] fun x ↦
      ∫ u, originalBareNativeKernel T Q χ center hρ hηb hr τ z x u * f u ∂μ)
    (v : Lp ℂ 2 μ) :
    let w := fun x ↦ ∫ u, physicalForwardKernel (singleRetainedForwardPhase T Q center hρ τ z)
      (fun u : X ↦ forwardScalarBandMask (m + 1) (originalForwardDetector hηb hr) u.1.1.val u.2)
      (fun u ↦ A u.1 u.2) x u * v u ∂μ
    ContDiff ℝ ∞ w ∧ tsupport w ⊆ K ∧
      (∀ ds : List (Fin (m + 1)), MemLp (euclideanCoordinateDerivList ds w) 2 volume) ∧
      ∀ ds : List (Fin (m + 1)),
        (eLpNorm (euclideanCoordinateDerivList ds w) 2 volume).toReal ≤
          forwardDerivativeConstant (m + 1) Rbox a p ds.length * ‖Tbare‖ *
            ∑ k ∈ Finset.range (ds.length+1), Λ ^ (ds.length-k-s0) *
              (eLpNorm (fun u : X ↦ ((‖u.2‖ ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * v u) 2 μ).toReal := by
  have ht : ∀ f : Lp ℂ 2 μ, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel (singleRetainedForwardPhase T Q center hρ τ z)
        (singleBareScalarMask (originalForwardDetector hηb hr)) (fun _ y ↦ (χ y : ℂ)) x u * f u ∂μ := by
    intro f
    simpa only [originalBareNativeKernel_eq_sampledMomentKernel] using hTbare f
  have hw := singleForward_physical_halfMoment_bounds (n := m + 1) (J := J)
    (singleRetainedForwardPhase T Q center hρ τ z) Φ A
    (singleBareScalarMask (originalForwardDetector hηb hr))
    (continuous_singleRetainedForwardPhase T Q center hρ τ z) hΦ hA
    (continuous_singleBareScalarMask (contDiff_originalForwardDetector hηb hr).continuous)
    (hasCompactSupport_singleBareScalarMask (originalForwardDetector hηb hr))
    (fun _ hu ↦ le_of_lt (one_lt_norm_of_singleBareScalarMask_ne_zero hηb hr hu))
    hK hAK hagree χ χ.continuous χ.hasCompactSupport hχK Rbox hbox hΛ a p ha hp hAj hΦj Tbare ht v
  simpa only [singleBareScalarMask_mul_sqrt] using hw

end JanetCartan.PhysicalForwardMean
