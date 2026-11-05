module

public import JanetCartan.Iteration.PhysicalSampling.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.IncidenceBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicMasks

/-!
# The scalar plateau from the original pre-selection source cap

The original initializer chooses its unchanged measurement/source radius with
`6*rMeasure < a'_i ≤ aExtra_i`. Choose the user cap below the already fixed
scalar inner radius before that initializer. Any further minimum with the
source-inverse or raw-wave cap preserves this inequality. The SAME original
measurement, source and coefficient supports then lie in the scalar plateau;
none is shrunk or replaced after selection (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.PhysicalSampling

/-- The original `6*r < a' ≤ aExtra` selection puts the entire unchanged
five-radius coefficient ball inside the scalar plateau. This includes the
original three-radius measurement and four-radius source supports. -/
theorem scalarCutoff_plateau_of_original_cap
    {n : ℕ} (χ : ContDiffBump (0 : Euclidean n))
    {r a' aExtra : ℝ} (hr : 0 < r) (hradius : 6 * r < a')
    (ha' : a' ≤ aExtra) (hcap : aExtra ≤ χ.rIn) :
    closedBall (0 : Euclidean n) (5 * r) ⊆ interior {x | χ x = 1} ∧
      ∀ i : Fin 3, tsupport (ContinuumRow.FixedCutoffs.physical (n := n) hr i) ⊆
        interior {x | χ x = 1} := by
  have hsmall : 5 * r < χ.rIn := by linarith
  have hplateau : ball (0 : Euclidean n) χ.rIn ⊆ interior {x | χ x = 1} := by
    apply interior_maximal _ isOpen_ball
    intro x hx
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hball := (closedBall_subset_ball hsmall).trans hplateau
  refine ⟨hball, ?_⟩
  intro i
  exact (ContinuumRow.FixedCutoffs.physical_tsupport_four hr i).trans
    ((closedBall_subset_closedBall (by linarith : 4 * r ≤ 5 * r)).trans hball)

/-- Further pre-selection caps, including the original strong-source inverse
cap, do not alter the plateau conclusion for the SAME selected cutoffs. -/
theorem scalarCutoff_plateau_of_min_original_cap
    {n : ℕ} (χ : ContDiffBump (0 : Euclidean n))
    {r a' userExtra inverseExtra : ℝ} (hr : 0 < r) (hradius : 6 * r < a')
    (ha' : a' ≤ min userExtra inverseExtra) (hcap : userExtra ≤ χ.rIn) :
    closedBall (0 : Euclidean n) (5 * r) ⊆ interior {x | χ x = 1} ∧
      ∀ i : Fin 3, tsupport (ContinuumRow.FixedCutoffs.physical (n := n) hr i) ⊆
        interior {x | χ x = 1} :=
  scalarCutoff_plateau_of_original_cap χ hr hradius ha'
    ((min_le_left _ _).trans hcap)

/-- A per-incidence carrier cap is chosen BEFORE the original selector. Its
unchanged `a'` carrier radius, not the larger auxiliary `a`, then puts the entire
original sampling weight inside the fixed scalar parameter plateau. This does
not require choosing a global incidence cap after the finite cover. -/
theorem exists_originalCarrier_scalar_plateau_cap
    (z₀ : Euclidean 3) {d : ℝ} (hd : 0 < d)
    (ψ : SeparatedSampling.Point → ℝ)
    (hplateau : ∀ z, WithLp.toLp 2 z ∈ closedBall z₀ d → ψ z = 1) :
    ∃ cap > (0 : ℝ), ∀ {a' : ℝ} (ha' : 0 < a'), a' ≤ cap →
      ∀ z, Sampling.originalConicCarrierWeight z₀ ha' z ≠ 0 → ψ z = 1 := by
  obtain ⟨cap, hcap, _hcapd, hmaps⟩ :=
    ContinuumRow.NormalizedSelection.exists_carrierSupport_in_parameter_ball z₀ hd hd
  refine ⟨cap, hcap, ?_⟩
  intro a' ha' hacap z hz
  apply hplateau z
  obtain ⟨w, hw, heq⟩ := Sampling.originalConicCarrierWeight_parameter_support z₀ ha' hz
  rw [← heq]
  apply ball_subset_closedBall (hmaps ?_)
  exact ⟨closedBall_subset_closedBall (by linarith : a' / 2 ≤ cap / 2) hw.1,
    closedBall_subset_closedBall (by linarith : a' / 2 ≤ cap / 2) hw.2⟩

end JanetCartan.PhysicalSampling
