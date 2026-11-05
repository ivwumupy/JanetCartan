module

public import JanetCartan.Iteration.PhysicalForwardMean.CoordinateBounds
public import JanetCartan.Iteration.PhysicalForwardMean.FamilyContinuity
public import JanetCartan.Iteration.PhysicalForwardMean.NormalizedPhase

/-!
# Original sampled forward field with all physical coordinate bounds

This is the actual native sampled-family consumer for mean14. The normalized
analysis phase is CONSTRUCTED from the already smooth original phase extension,
which agrees with the literal original phase only on the active original source
support. Computed kernel-jet and branch regularity, physical derivative
interchange and output smoothness/membership are all discharged. The full
corrected amplitude is retained. Only its primitive physical jets (primary13)
and the normalized literal phase jets (phase28) remain quantitative inputs.
Constants depend on n, the fixed physical box, order and primitive profiles,
not on the arbitrary sample type, shell count, input cutoff or scale.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open PhysicalMean Pseudodifferential AmplitudeBound

variable {n : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]
local notation "E" => Euclidean n
local notation "X" => ι × Euclidean (n - 1)

/-- The literal original sampled forward integral is ONE compact C∞ physical
representative, with all its coordinate derivative norms bounded by the exact
native input moments. There is no output-size or derivative-success hypothesis.
Only source-local primitive full-amplitude and original normalized-phase profiles
are inputs; their actual producers are primary13 and phase28
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-fields`). -/
theorem sampledForward_physical_coordinate_bounds
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : X → E → ℝ) (Φ : ι → Euclidean (n - 1) → E → ℝ)
    (A : ι → Euclidean (n - 1) → E → ℂ) (m : X → ℝ)
    (hφ : Continuous (Function.uncurry φ))
    (hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)))
    (hA : ∀ i, ContDiff ℝ ∞ (Function.uncurry (A i)))
    (hm : Continuous m) (hms : HasCompactSupport m)
    (hhigh : ∀ u, m u ≠ 0 → 1 ≤ ‖u.2‖)
    {K : Set E} (hK : IsCompact K) (hAK : ∀ i η, tsupport (A i η) ⊆ K)
    (hagree : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s0 : ℕ} {T : ℝ} (hT : 1 ≤ T) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hAj : ∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (A i η) x‖ ≤ a j * T ^ (j - (s0 + (n / 2 + 1))))
    (hΦj : ∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y / ‖η‖) x‖ ≤
        p j * T ^ (j - 1 - (s0 + (n / 2 + 1))))
    (T0 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT0 : ∀ f : Lp ℂ 2 μ, T0 f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u * f u ∂μ)
    (v : Lp ℂ 2 μ) :
    let w := fun x ↦ ∫ u, physicalForwardKernel φ m (fun u ↦ A u.1 u.2) x u * v u ∂μ
    ContDiff ℝ ∞ w ∧ tsupport w ⊆ K ∧
      (∀ ds : List (Fin n), MemLp (euclideanCoordinateDerivList ds w) 2 volume) ∧
      ∀ ds : List (Fin n),
        (∀ k ≤ ds.length, MemLp (fun u : X ↦ (‖u.2‖ : ℂ)^k * v u) 2 μ) →
        (eLpNorm (euclideanCoordinateDerivList ds w) 2 volume).toReal ≤
          forwardDerivativeConstant n Rbox a p ds.length * ‖T0‖ *
            ∑ k ∈ Finset.range (ds.length+1), T ^ (ds.length-k-s0) *
              (eLpNorm (fun u : X ↦ (‖u.2‖ : ℂ)^k * v u) 2 μ).toReal := by
  intro w
  let A0 := fun u : X ↦ A u.1 u.2
  let θ : X → E → ℝ := fun u ↦ normalizedForwardPhase (d := n - 1) (n := n) (Φ u.1) u.2
  let lam := fun u : X ↦ ‖u.2‖
  have hAs (u : X) : ContDiff ℝ ∞ (A0 u) := by
    have hs : ContDiff ℝ ∞ (fun x : E ↦ (u.2,x)) := contDiff_const.prodMk contDiff_id
    exact (hA u.1).comp hs
  have hθfull (i : ι) : ContDiff ℝ ∞ (Function.uncurry (normalizedForwardPhase (Φ i))) :=
    contDiff_normalizedForwardPhase (d := n - 1) (n := n) (Φ i) (hΦ i)
  have hθs (u : X) : ContDiff ℝ ∞ (θ u) := by
    have hs : ContDiff ℝ ∞ (fun x : E ↦ (u.2,x)) := contDiff_const.prodMk contDiff_id
    simpa only [θ, Function.comp_def, Function.uncurry_apply_pair] using (hθfull u.1).comp hs
  have hphase (u : X) (hu : m u ≠ 0) (x : E) (hx : x ∈ K) : φ u x = lam u * θ u x := by
    rw [hagree u hu x hx]
    exact (norm_mul_normalizedForwardPhase (Φ u.1) u.2 (hhigh u hu) x).symm
  have hkernel : physicalForwardKernel φ m A0 =
      physicalForwardKernel (fun u : X ↦ Φ u.1 u.2) m A0 := by
    funext x u
    by_cases hu : m u = 0
    · simp [physicalForwardKernel, sampledMomentKernel, hu]
    by_cases hz : A0 u x = 0
    · simp [physicalForwardKernel, sampledMomentKernel, hz]
    · simp only [physicalForwardKernel, sampledMomentKernel,
        hagree u hu x (hAK u.1 u.2 (subset_tsupport _ hz))]
  have hjets (j : ℕ) : Continuous (fun q : E × X ↦ iteratedFDeriv ℝ j
      (fun y ↦ physicalForwardKernel φ m A0 y q.2) q.1) := by
    rw [hkernel]
    exact continuous_discrete_physicalForwardKernel_jets Φ A m hΦ hA hm j
  have hw := physicalForwardIntegral_smooth φ θ lam m A0 hθs hAs hK
    (fun u ↦ hAK u.1 u.2) hms hphase hjets v
  refine ⟨hw.1, hw.2.1, hw.2.2, ?_⟩
  intro ds hweight
  have hbc (b : RawPrimary.SliceBounds.SliceDerivativeBranch ds.length) :
      Continuous (fun q : X × E ↦ RawPrimary.SliceBounds.sliceDerivativeAmplitude
        (θ q.1) (A0 q.1) (fun i ↦ EuclideanSpace.single (ds.get i) 1) b q.2) :=
    continuous_discrete_forwardBranchAmplitude (fun i ↦ normalizedForwardPhase (Φ i)) A hθfull hA _ b
  have hθjets (u : X) (hu : m u ≠ 0) (x : E) (hx : x ∈ K)
      (j : ℕ) (hj : 1 ≤ j) (_hj' : j ≤ ds.length + (n / 2 + 1)) :
      ‖iteratedFDeriv ℝ j (θ u) x‖ ≤ p j * T ^ (j - 1 - (s0 + (n / 2 + 1))) := by
    rw [show θ u = fun y ↦ Φ u.1 u.2 y / ‖u.2‖ from
      normalizedForwardPhase_eq_on_highFrequency (Φ u.1) u.2 (hhigh u hu)]
    exact hΦj u.1 u.2 hu x hx j hj
  exact (norm_physicalForwardIntegral_coordinate_le μ φ θ lam m A0 hφ hm hms hθs hAs hK
    (fun u ↦ hAK u.1 u.2) hphase hjets χ hχ hχs hχK Rbox hbox hT a p ha hp ds
    (fun u hu x hx j _ ↦ hAj u.1 u.2 hu x hx j) hθjets hbc T0 hT0 v hweight).2

end JanetCartan.PhysicalForwardMean
