module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.LowPhase
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Support
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Amplitude

/-!
# Contractions for the literal elapsed graph grades

These coordinate maps connect the original two-time primitives to the packed
variables of `FiniteChain.Graph.exists_graph_factor_sobolev_bound_of_primitive_grades`.
Both physical positions are retained, with the product norms used by that theorem.
Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FiniteChain.Graph
open FourierIntegral.FullAmplitudePrimitiveBudget.Local

variable {d : ℕ}

/-- Forget only the two localizer covectors in `app:ch_regular:eq:joint-kernel-phase`.
The two physical amplitude positions remain in their literal order. -/
def graphAmplitudePoint : JointVariables (Euclidean (d + 1)) →L[ℝ] Point (d + 1) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Packing the graph variables costs no derivative powers in the primitive
grades (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_graphAmplitudePoint_le : ‖graphAmplitudePoint (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖(p.1, p.2.1)‖ ≤ 1 * ‖p‖
  simpa only [Prod.norm_def, one_mul] using
    max_le (norm_fst_le p) ((norm_fst_le p.2).trans (norm_snd_le p))

/-- Pointwise form of the existing affine pullback estimate. This is used for
the exact derivative grades, without replacing `L^k` by a higher power
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_affine_contraction_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (l : E →L[ℝ] F) (hl : ‖l‖ ≤ 1) (v : F)
    {U : Set F} (hU : IsOpen U) {f : F → G} (hf : ContDiffOn ℝ ∞ f U)
    {p : E} (hp : l p + v ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f (l z + v)) p‖ ≤
      ‖iteratedFDeriv ℝ k f (l p + v)‖ :=
  (norm_iteratedFDeriv_preAffine_le l v hU hf hp k).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hl))

/-- The two original times and the original spatial base, before freezing
the physical covector in the noncomparable graph estimate
(`app:ch_regular:eq:chain-tail`). -/
def elapsedBaseLinear : (Euclidean (d + 1) × Euclidean (d + 1)) →L[ℝ]
    (ℝ × ℝ × Euclidean d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (p.1 0, p.1 0, spatialPart p.1)
      map_add' := by intro x y; ext <;> rfl
      map_smul' := by intro a x; ext <;> rfl }

/-- Freezing frequency still gives a contraction in both physical positions
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_elapsedBaseLinear_le : ‖elapsedBaseLinear (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change max |p.1 0| (max |p.1 0| ‖spatialPart p.1‖) ≤ 1 * ‖p‖
  rw [one_mul]
  have ht := (PiLp.norm_apply_le p.1 0).trans (norm_fst_le p)
  exact max_le ht (max_le ht ((norm_spatialPart_le _).trans (norm_fst_le p)))

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
