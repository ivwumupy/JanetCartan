module

public import JanetCartan.Iteration.PhysicalForwardMean.Sampled

/-!
# Derived qualitative regularity of the original complete mean kernels

Consumer: `fixedSourceQuadratic_source_profile`. The normalized phase, ALL
physical kernel jets and every full differentiated branch are constructed from
the primitive joint phase/amplitude certificates. The actual operator mask is
never changed. Normalization through eta=0 is the checked auxiliary analysis
extension of PhysicalForwardMean, equal to the original normalized phase on
every active high-pass frequency.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalMean
open PhysicalForwardMean RawPrimary.SliceBounds

/-- The complete joint regularity obligations for the actual grouped quadratic
source follow from the original full kernel primitives, not output estimates.
No norm of a frequency derivative or discrete label enters any bound. -/
theorem originalSampledForward_qualitative {n N : ℕ} {ι : Type*}
    [TopologicalSpace ι] [DiscreteTopology ι]
    (φ : (ι × Euclidean (n-1)) → Euclidean n → ℝ)
    (Φ : ι → Euclidean (n-1) → Euclidean n → ℝ)
    (amp : Fin N → Fin n → ι → Euclidean (n-1) → Euclidean n → ℂ)
    (m : (ι × Euclidean (n-1)) → ℝ)
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (hamp : ∀ a c i, ContDiff ℝ ∞ (Function.uncurry (amp a c i)))
    (hm : Continuous m) (hhigh : ∀ z, ‖z.2‖ ≤ 1 → m z = 0)
    {K : Set (Euclidean n)} (hampK : ∀ a c i η, tsupport (amp a c i η) ⊆ K)
    (hagree : ∀ z, m z ≠ 0 → ∀ x ∈ K, φ z x = Φ z.1 z.2 x) :
    let θ := fun z : ι × Euclidean (n-1) ↦ normalizedForwardPhase (Φ z.1) z.2
    (∀ z, ContDiff ℝ ∞ (θ z)) ∧
    (∀ z, m z ≠ 0 → ∀ x ∈ K, φ z x = ‖z.2‖*θ z x) ∧
    (∀ a c i j, Continuous (fun z : Euclidean n × Euclidean (n-1) ↦
      iteratedFDeriv ℝ j (fun y ↦ physicalForwardKernel (fun η ↦ φ (i,η))
        (fun η ↦ m (i,η)*Real.sqrt ‖η‖) (amp a c i) y z.2) z.1)) ∧
    (∀ ds : List (Fin n), ∀ a c (b : SliceDerivativeBranch ds.length),
      Continuous (fun z : (ι × Euclidean (n-1)) × Euclidean n ↦
        sliceDerivativeAmplitude (θ z.1) (amp a c z.1.1 z.1.2)
          (fun j ↦ EuclideanSpace.single (ds.get j) 1) b z.2)) ∧
    (∀ z, m z ≠ 0 → ∀ j x, iteratedFDeriv ℝ j (θ z) x =
      iteratedFDeriv ℝ j (fun y ↦ Φ z.1 z.2 y/‖z.2‖) x) := by
  intro θ
  have hactive (z : ι × Euclidean (n-1)) (hz : m z ≠ 0) : 1 ≤ ‖z.2‖ :=
    le_of_lt (lt_of_not_ge fun h ↦ hz (hhigh z h))
  have hθfull (i : ι) : ContDiff ℝ ∞ (Function.uncurry (normalizedForwardPhase (Φ i))) :=
    contDiff_normalizedForwardPhase (Φ i) (hΦ i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    have hs : ContDiff ℝ ∞ (fun x : Euclidean n ↦ (z.2,x)) := contDiff_const.prodMk contDiff_id
    simpa only [θ, Function.comp_def, Function.uncurry_apply_pair] using (hθfull z.1).comp hs
  · intro z hz x hx
    rw [hagree z hz x hx]
    exact (norm_mul_normalizedForwardPhase (Φ z.1) z.2 (hactive z hz) x).symm
  · intro a c i j
    let mf := fun z : ι × Euclidean (n-1) ↦ m z*Real.sqrt ‖z.2‖
    let Af := fun z : ι × Euclidean (n-1) ↦ amp a c z.1 z.2
    have hkernel : physicalForwardKernel φ mf Af =
        physicalForwardKernel (fun z ↦ Φ z.1 z.2) mf Af := by
      funext x z
      by_cases hmz : m z = 0
      · simp [physicalForwardKernel, sampledMomentKernel, mf, hmz]
      by_cases haz : Af z x = 0
      · simp [physicalForwardKernel, sampledMomentKernel, haz]
      · simp only [physicalForwardKernel, sampledMomentKernel,
          hagree z hmz x (hampK a c z.1 z.2 (subset_tsupport _ haz))]
    have hfull : Continuous (fun z : Euclidean n × (ι × Euclidean (n-1)) ↦
        iteratedFDeriv ℝ j (fun y ↦ physicalForwardKernel φ mf Af y z.2) z.1) := by
      rw [hkernel]
      exact continuous_discrete_physicalForwardKernel_jets Φ (amp a c) mf hΦ (hamp a c)
        (hm.mul continuous_snd.norm.sqrt) j
    exact hfull.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  · intro ds a c b
    exact continuous_discrete_forwardBranchAmplitude (fun i ↦ normalizedForwardPhase (Φ i))
      (amp a c) hθfull (hamp a c) _ b
  · intro z hz j x
    exact iteratedFDeriv_normalizedForwardPhase_on_highFrequency (Φ z.1) z.2 (hactive z hz) j x

end JanetCartan.PhysicalMean
