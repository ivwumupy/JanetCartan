module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Postcomposition
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Cutoff

/-!
# The actual exterior cutoff in the higher commutator

The exterior normal is the literal `ContinuumRow.cutoffMultiplier (χ ^ 2)`.
Its commutator is the already constructed ordered Leibniz operator. This closes
the exterior summand of `app:ch_background:eq:bg-commutator` on the same real
vector-valued L² and Sobolev spaces as `Translation.Assembly`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
open PeriodicSobolevSpace ContinuumRow
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The two existing multiplier constructions agree as actual L² operators,
with unchanged measure (`app:ch_background:eq:bg-commutator`). -/
theorem cutoffMultiplier_eq_multiplication (q : C(Torus n, ℝ)) :
    cutoffMultiplier q = Exterior.multiplication q q.continuous := by
  ext1 u
  apply Lp.ext
  exact (cutoffMultiplier_coeFn q u).trans
    (Exterior.multiplication_ae q q.continuous u).symm

/-- The coefficient of the actual exterior normal is smooth
(`app:ch_background:eq:bg-commutator`). -/
theorem smooth_cutoff_square (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ) :
    IsSmoothPeriodic (χ ^ 2 : C(Torus n, ℝ)) := by
  refine ⟨(χ ^ 2).continuous, ?_⟩
  change ContDiff ℝ ∞ (fun x ↦ periodicLift χ x ^ 2)
  exact hχ.2.pow 2

/-- The real vector-valued exterior commutator at the parent's explicit order
`s`, using the existing Leibniz construction (`app:ch_background:eq:bg-commutator`). -/
def cutoffCommutator (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1) :
    PeriodicSobolevSpace n V s →L[ℝ] PeriodicL2 n V :=
  (Exterior.commutator (χ ^ 2 : C(Torus n, ℝ)) (smooth_cutoff_square χ hχ) is).comp
    (inclusion (show is.length - 1 ≤ s by omega))

/-- The fixed exterior constant is uniform over ordered words of the same
length and depends only on the cutoff and order (`app:ch_background:eq:bg-commutator`). -/
def cutoffCommutatorConstant (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ) (s : ℕ) : ℝ :=
  Exterior.commutatorConstant (F := V) (χ ^ 2 : C(Torus n, ℝ)) (smooth_cutoff_square χ hχ) (s + 1)

/-- Positivity of the fixed cutoff constant (`app:ch_background:eq:bg-commutator`). -/
theorem cutoffCommutatorConstant_pos (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (s : ℕ) : 0 < cutoffCommutatorConstant χ hχ s :=
  Exterior.commutatorConstant_pos _ _ _

/-- The exterior summand needs only the Sobolev norm, with a constant fixed
before all amplitudes and budgets (`app:ch_background:eq:bg-commutator`). -/
theorem norm_cutoffCommutator_le (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1)
    (u : PeriodicSobolevSpace n V s) :
    ‖cutoffCommutator χ hχ s is hlen u‖ ≤ cutoffCommutatorConstant χ hχ s * ‖u‖ := by
  have hs : s = is.length - 1 := by omega
  subst s
  have he : cutoffCommutator χ hχ (is.length - 1) is hlen u =
      Exterior.commutator (χ ^ 2 : C(Torus n, ℝ)) (smooth_cutoff_square χ hχ) is u := rfl
  rw [he, cutoffCommutatorConstant, ← hlen]
  exact Exterior.norm_commutator_le _ _ _ _

/-- Exact smooth identity for the literal exterior normal. This is proved
from the ordered Leibniz formula, with no commutator premise
(`app:ch_background:eq:bg-commutator`). -/
theorem cutoffCommutator_ofSmooth (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1)
    (f : Torus n → V) (hf : IsSmoothPeriodic f) :
    HasPeriodicWeakDerivativeList is
      (cutoffMultiplier (χ ^ 2) (toL2 s (ofSmooth s f hf)))
      (cutoffMultiplier (χ ^ 2) (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) + cutoffCommutator χ hχ s is hlen (ofSmooth s f hf)) := by
  have hs : s = is.length - 1 := by omega
  subst s
  change HasPeriodicWeakDerivativeList is
    (cutoffMultiplier (χ ^ 2) (toL2 _ (ofSmooth _ f hf)))
    (cutoffMultiplier (χ ^ 2) (toL2 0 (ofSmooth 0 _ (hf.coordinateDerivList is))) +
      Exterior.commutator (χ ^ 2 : C(Torus n, ℝ)) (smooth_cutoff_square χ hχ) is (ofSmooth _ f hf))
  rw [cutoffMultiplier_eq_multiplication, Exterior.commutator_ofSmooth,
    ← add_sub_assoc, add_sub_cancel_left,
    Exterior.multiplication_ofSmooth (smooth_cutoff_square χ hχ) hf (is.length - 1) 0]
  exact (Exterior.smooth_smul (smooth_cutoff_square χ hχ) hf).hasPeriodicWeakDerivativeList is 0 0

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
