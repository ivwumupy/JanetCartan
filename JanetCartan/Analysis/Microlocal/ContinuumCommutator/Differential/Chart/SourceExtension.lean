module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# A fixed compact smooth source extension

For `app:ch_background:eq:bg-commutator`, extend a periodic test by a fixed
smooth cutoff supported inside the unit cell and equal to one on a neighborhood
of the full source box. The cutoff is constructed from the box alone, before
choosing an amplitude or its high budget. Every ordered derivative of the
extension agrees with the periodic derivative on the source box. This removes
only artificial extension derivatives, not derivatives of physical masks in
an amplitude.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Compactness of the fixed source box (`app:ch_background:eq:bg-commutator`). -/
theorem isCompact_chartBox (r : ℝ) : IsCompact (chartBox (d := d) r) := by
  have h := (PiLp.homeomorph 2 (fun _ : Fin d ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_pi_infinite (fun _ : Fin d ↦ isCompact_Icc (a := -r) (b := r)))
  convert h using 1
  ext x
  simp [chartBox, PiLp.homeomorph, abs_le]

/-- Geometric data for the artificial extension cutoff. No operator identity
or estimate is part of this structure (`app:ch_background:eq:bg-commutator`). -/
structure SourceCutoff (d : ℕ) (r : ℝ) where
  toFun : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ ∞ toFun
  range : ∀ x, toFun x ∈ Icc (0 : ℝ) 1
  compact : HasCompactSupport toFun
  support_cell : tsupport toFun ⊆ {x | ∀ i, |x i| < (1 / 2 : ℝ)}
  plateau : chartBox r ⊆ interior {x | toFun x = 1}

/-- A source cutoff exists for every fixed box of radius less than `1/2`;
it is independent of amplitude budgets (`app:ch_background:eq:bg-commutator`). -/
theorem nonempty_sourceCutoff {r : ℝ} (hr : r < 1 / 2) : Nonempty (SourceCutoff d r) := by
  have ho : IsOpen {x : E | ∀ i, |x i| < (1 / 2 : ℝ)} := by
    rw [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (EuclideanSpace.proj i).continuous.abs continuous_const
  obtain ⟨χ, hc, hb, hs, ht, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_chartBox (d := d) r) ho (fun x hx i ↦ (hx i).trans_lt hr)
  exact ⟨⟨χ, hc, hb, hs, ht, hp⟩⟩

namespace SourceCutoff
variable {r : ℝ} (χ : SourceCutoff d r)

/-- The compact smooth extension of a periodic test
(`app:ch_background:eq:bg-commutator`). -/
def extend (u : Torus d → ℂ) (x : E) : ℂ := (χ.toFun x : ℂ) * periodicLift u x

/-- The fixed cutoff introduces no loss of smoothness
(`app:ch_background:eq:bg-commutator`). -/
theorem smooth_extend {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) :
    ContDiff ℝ ∞ (χ.extend u) := (Complex.ofRealCLM.contDiff.comp χ.smooth).mul hu.2

/-- The extension is a genuine compact Euclidean test
(`app:ch_background:eq:bg-commutator`). -/
theorem compact_extend (u : Torus d → ℂ) : HasCompactSupport (χ.extend u) :=
  (χ.compact.comp_left Complex.ofReal_zero).mul_right

/-- On a neighborhood of every source point the extension equals the periodic
lift (`app:ch_background:eq:bg-commutator`). -/
theorem extend_eventuallyEq (u : Torus d → ℂ) {x : E} (hx : x ∈ chartBox r) :
    χ.extend u =ᶠ[𝓝 x] periodicLift u := by
  filter_upwards [isOpen_interior.mem_nhds (χ.plateau hx)] with y hy
  have hy' : y ∈ {x | χ.toFun x = 1} := interior_subset hy
  change χ.toFun y = 1 at hy'
  simp [extend, hy']

/-- All artificial extension derivatives vanish on the source box. The word
order matches the Euclidean commutator and periodic weak derivative APIs
(`app:ch_background:eq:bg-commutator`). -/
theorem derivative_extend_eq {u : Torus d → ℂ} (hu : IsSmoothPeriodic u)
    (is : List (Fin d)) {x : E} (hx : x ∈ chartBox r) :
    euclideanCoordinateDerivList is (χ.extend u) x =
      periodicLift (periodicCoordinateDerivList is u) x := by
  rw [periodicLift_coordinateDerivList_eq hu]
  exact (euclideanCoordinateDerivList_eventuallyEq (χ.extend_eventuallyEq u hx) is).self_of_nhds

/-- Replacing the periodic source by its compact extension leaves the actual
Lebesgue operator unchanged (`app:ch_background:eq:bg-commutator`). -/
theorem fullAmplitudeOperator_extend
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : Torus d → ℂ) :
    fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (χ.extend u) =
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (periodicLift u) :=
  fullAmplitudeOperator_congr_on_source b hs
    (fun _ hx ↦ (χ.extend_eventuallyEq u hx).self_of_nhds)

/-- Any two choices of artificial extension give exactly the same operator
(`app:ch_background:eq:bg-commutator`). -/
theorem fullAmplitudeOperator_extension_independent (ψ : SourceCutoff d r)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : Torus d → ℂ) :
    fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (χ.extend u) =
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (ψ.extend u) := by
  rw [χ.fullAmplitudeOperator_extend b hs u, ψ.fullAmplitudeOperator_extend b hs u]

/-- Differentiated compact source tests give the genuine periodic source
terms. Physical amplitude cutoffs are retained in `b`
(`app:ch_background:eq:bg-commutator`). -/
theorem fullAmplitudeOperator_derivative_extend
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) {u : Torus d → ℂ}
    (hu : IsSmoothPeriodic u) (is : List (Fin d)) :
    fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
      (euclideanCoordinateDerivList is (χ.extend u)) =
    fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
      (periodicLift (periodicCoordinateDerivList is u)) :=
  fullAmplitudeOperator_congr_on_source b hs (fun _ hx ↦ χ.derivative_extend_eq hu is hx)

/-- Periodization of the compact-test output is the literal chart kernel
(`app:ch_background:eq:bg-commutator`). -/
theorem torusKernelOperator_eq_extend (hr : r < 1 / 2)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (u : Torus d → ℂ) :
    torusKernelOperator b u = amplitudePeriodization
      (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (χ.extend u)) := by
  rw [χ.fullAmplitudeOperator_extend b hs u, torusKernelOperator_eq hr b hs u]

end SourceCutoff
end JanetCartan.Pseudodifferential.DifferentialChart
