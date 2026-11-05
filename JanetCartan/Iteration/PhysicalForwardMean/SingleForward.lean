module

public import JanetCartan.Iteration.PhysicalForwardMean.Sampled
public import JanetCartan.Iteration.PhysicalForwardMean.HalfInput

/-!
# Individual forward bound through the original bare scalar tester

The operator being estimated remains the literal HALF-WEIGHTED original raw
operator on the original SINGLE refined-shell measure. Scalar36's bare tester
acts on the exactly halfweighted input. This proves the k+1/2 moment estimate
needed by mean14's individual fields (`app:ch_mean_pairs:eq:block-fields`).
There is no sample weight, one-point sample measure, cutoff-size loss or count.
The only quantitative jets are actual full-A13 and normalized full-phase28.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open PhysicalMean PhysicalSamplingShells RawInputPartition Pseudodifferential AmplitudeBound

variable {n J : ℕ}
local notation "I" => RefinedIndex J
local notation "E" => Euclidean n
local notation "X" => I × Euclidean (n - 1)
local notation "μ" => annularShellMeasure (n := n) (refinedRadius (J := J))

/-- Pointwise equality of the ORIGINAL halfweighted raw integral and the bare
kernel integral applied to the halfweighted native L² input. Equality is of
literal integrals, before any physical differentiation or L² identification. -/
theorem singleForwardIntegral_eq_halfInput
    (φ : X → E → ℝ) (A : X → E → ℂ) (mBare : X → ℝ) (v : Lp ℂ 2 μ) (x : E) :
    (∫ u, physicalForwardKernel φ (fun u ↦ mBare u * Real.sqrt ‖u.2‖) A x u * v u ∂μ) =
      ∫ u, physicalForwardKernel φ mBare A x u * radialHalfInput refinedRadius v u ∂μ := by
  apply integral_congr_ae
  filter_upwards [radialHalfInput_coe_ae refinedRadius v] with u hu
  rw [hu]
  simp only [physicalForwardKernel, sampledMomentKernel, Complex.ofReal_mul]
  ring

/-- SAME complete individual raw operator, exact original single-shell input
measure, actual bare scalar tester, and sharp k+1/2 input moments. No desired
output bound, output regularity, frequency derivative estimate or cutoff-power
factor is supplied as a hypothesis (`app:ch_mean_pairs:eq:block-fields`). -/
theorem singleForward_physical_halfMoment_bounds
    (φ : X → E → ℝ) (Φ : I → Euclidean (n - 1) → E → ℝ)
    (A : I → Euclidean (n - 1) → E → ℂ) (mBare : X → ℝ)
    (hφ : Continuous (Function.uncurry φ))
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (hA : ∀ i, ContDiff ℝ ∞ (Function.uncurry (A i)))
    (hm : Continuous mBare) (hms : HasCompactSupport mBare)
    (hhigh : ∀ u, mBare u ≠ 0 → 1 ≤ ‖u.2‖)
    {K : Set E} (hK : IsCompact K) (hAK : ∀ i η, tsupport (A i η) ⊆ K)
    (hagree : ∀ u, mBare u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s0 : ℕ} {T : ℝ} (hT : 1 ≤ T) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hAj : ∀ i η, mBare (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (A i η) x‖ ≤ a j * T ^ (j - (s0 + (n / 2 + 1))))
    (hΦj : ∀ i η, mBare (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y / ‖η‖) x‖ ≤
        p j * T ^ (j - 1 - (s0 + (n / 2 + 1))))
    (Tbare : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hTbare : ∀ f : Lp ℂ 2 μ, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ mBare (fun _ y ↦ (χ y : ℂ)) x u * f u ∂μ)
    (v : Lp ℂ 2 μ) :
    let w := fun x ↦ ∫ u, physicalForwardKernel φ (fun u ↦ mBare u * Real.sqrt ‖u.2‖)
      (fun u ↦ A u.1 u.2) x u * v u ∂μ
    ContDiff ℝ ∞ w ∧ tsupport w ⊆ K ∧
      (∀ ds : List (Fin n), MemLp (euclideanCoordinateDerivList ds w) 2 volume) ∧
      ∀ ds : List (Fin n),
        (eLpNorm (euclideanCoordinateDerivList ds w) 2 volume).toReal ≤
          forwardDerivativeConstant n Rbox a p ds.length * ‖Tbare‖ *
            ∑ k ∈ Finset.range (ds.length+1), T ^ (ds.length-k-s0) *
              (eLpNorm (fun u : X ↦ ((‖u.2‖ ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * v u) 2 μ).toReal := by
  intro w
  let t : TopologicalSpace (RefinedIndex J) := inferInstance
  let f : RefinedIndex J → ℝ := fun i ↦ ((Fintype.equivFin (RefinedIndex J) i).val : ℝ)
  have hf : Function.Injective f := by
    intro i j hij
    apply (Fintype.equivFin (RefinedIndex J)).injective
    apply Fin.ext
    change ((Fintype.equivFin (RefinedIndex J) i).val : ℝ) =
      ((Fintype.equivFin (RefinedIndex J) j).val : ℝ) at hij
    exact_mod_cast hij
  let mt : MetricSpace (RefinedIndex J) := MetricSpace.induced f hf inferInstance
  have hmt : t = mt.toUniformSpace.toTopologicalSpace := by
    have ht : t = ⊥ := DiscreteTopology.eq_bot
    have hm : mt.toUniformSpace.toTopologicalSpace = ⊥ := by
      let : MetricSpace (RefinedIndex J) := mt
      exact DiscreteTopology.eq_bot
    exact ht.trans hm.symm
  let : MetricSpace (RefinedIndex J) := mt.replaceTopology hmt
  let vhalf := radialHalfInput refinedRadius v
  let wbare := fun x ↦ ∫ u, physicalForwardKernel φ mBare (fun u ↦ A u.1 u.2) x u * vhalf u ∂μ
  have heq : w = wbare := funext (singleForwardIntegral_eq_halfInput φ (fun u ↦ A u.1 u.2) mBare v)
  have hw := sampledForward_physical_coordinate_bounds (n := n) (ι := RefinedIndex J)
    μ φ Φ A mBare hφ hΦ hA hm hms hhigh
    hK hAK hagree χ hχ hχs hχK Rbox hbox hT a p ha hp hAj hΦj Tbare hTbare vhalf
  change ContDiff ℝ ∞ wbare ∧ tsupport wbare ⊆ K ∧ _ at hw
  rw [heq]
  refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩
  intro ds
  have hnorm := hw.2.2.2 ds (fun k _ ↦ memLp_radialMoment_annularShell refinedRadius vhalf k)
  simpa only [vhalf, eLpNorm_radialHalfInput_moment] using hnorm

end JanetCartan.PhysicalForwardMean
