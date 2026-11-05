module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Classical
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Completion of the classical derivative norm

For `app:ch_osc:prop:osc-retarded-tube`, complete the actual compactly supported
smooth jet image in a finite product of L² spaces. The product norm is equivalent
to the square root of the sum of squared derivative norms. No weak-derivative or
Fourier identification is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace JanetCartan.RetardedSobolev.Spaces

/-- The closed classical jet image (`app:ch_osc:prop:osc-retarded-tube`). -/
def sobolevSubmodule {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : Submodule ℂ (JetIndex d m → Lp ℂ 2 μ) :=
  (jetMap m μ).range.topologicalClosure

/-- Integer Sobolev completion for an explicit measure
(`app:ch_osc:prop:osc-retarded-tube`). Use volume for the ambient space. -/
abbrev Sobolev {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] := sobolevSubmodule m μ

instance {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : NormedAddCommGroup (Sobolev m μ) :=
  Submodule.normedAddCommGroup _

instance {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : NormedSpace ℂ (Sobolev m μ) :=
  Submodule.normedSpace _

instance {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : CompleteSpace (Sobolev m μ) :=
  inferInstanceAs (CompleteSpace (jetMap m μ).range.topologicalClosure)

/-- The canonical inclusion of test fields into their jet completion
(`app:ch_osc:prop:osc-retarded-tube`). -/
def ofTest {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : Test d →ₗ[ℂ] Sobolev m μ :=
  (jetMap m μ).codRestrict _ fun f ↦
    (jetMap m μ).range.le_topologicalClosure (LinearMap.mem_range_self _ f)

/-- The classical inclusion is dense (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem denseRange_ofTest {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] : DenseRange (ofTest m μ) := by
  exact ((denseRange_inclusion_iff (s := Set.range (jetMap m μ)) subset_closure).2
    subset_rfl).comp (Set.rangeFactorization_surjective.denseRange)
    (continuous_inclusion subset_closure)

/-- The zeroth jet, including in dimension zero
(`app:ch_osc:prop:osc-retarded-tube`). -/
def zeroIndex (d m : ℕ) : JetIndex d m :=
  ⟨⟨0, by omega⟩, Fin.elim0, ⟨0, by omega⟩⟩

/-- The zeroth jet is the original field (`app:ch_osc:prop:osc-retarded-tube`). -/
@[simp] theorem jet_zeroIndex {d m : ℕ} (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    jet (zeroIndex d m) f = fun p ↦ f (p.2, p.1) := by
  funext p
  simp [jet, zeroIndex, transverseJet]

/-- No smooth fields are identified by the ambient completion
(`app:ch_osc:prop:osc-retarded-tube`). Full support of the measure is essential. -/
theorem ofTest_injective {d : ℕ} (m : ℕ) (μ : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] :
    Function.Injective (ofTest m μ) := by
  intro f g h
  have hz := congrArg (fun u : Sobolev m μ ↦ u.val (zeroIndex d m)) h
  change (jet_memLp μ _ f).toLp _ = (jet_memLp μ _ g).toLp _ at hz
  have ha := (MemLp.toLp_eq_toLp_iff _ _).mp hz
  simp only [jet_zeroIndex] at ha
  have he := Measure.eq_of_ae_eq ha
    (f.property.1.continuous.comp continuous_swap)
    (g.property.1.continuous.comp continuous_swap)
  apply Subtype.ext
  funext x
  exact congrFun he (x.2, x.1)

/-- Extend a classical linear operator under its precise derivative norm bound
(`app:ch_osc:prop:osc-retarded-tube`). The estimate is a hypothesis for the
classical operator, not a claim about either concrete retarded integral. -/
theorem exists_unique_bounded_extension {d e m n : ℕ}
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (T : Test d →ₗ[ℂ] Test e) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f, ‖jetMap n ν (T f)‖ ≤ C * ‖jetMap m μ f‖) :
    ∃ A : Sobolev m μ →L[ℂ] Sobolev n ν,
      ‖A‖ ≤ C ∧ (∀ f, A (ofTest m μ f) = ofTest n ν (T f)) ∧
      ∀ B : Sobolev m μ →L[ℂ] Sobolev n ν,
        (∀ f, B (ofTest m μ f) = ofTest n ν (T f)) → B = A := by
  let F := (ofTest n ν).comp T
  let A := F.extendOfNorm (ofTest m μ)
  have hb : ∀ f, ‖F f‖ ≤ C * ‖ofTest m μ f‖ := hT
  refine ⟨A, LinearMap.opNorm_extendOfNorm_le (denseRange_ofTest m μ) hC hb,
    fun f ↦ LinearMap.extendOfNorm_eq (denseRange_ofTest m μ) ⟨C, hb⟩ f, ?_⟩
  intro B hB
  exact (LinearMap.extendOfNorm_unique (denseRange_ofTest m μ) C hb B
    (LinearMap.ext hB)).symm

end JanetCartan.RetardedSobolev.Spaces
