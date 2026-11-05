module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.ClassicalDerivatives

/-!
# Bounded derivatives of the classical completion

The output Fourier comparison for `app:ch_regular:eq:chain-tail` uses these
concrete extensions of the classical derivatives. Their norm bounds follow
from reindexing actual jets, not from an assumed Sobolev comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces

variable {d : ℕ}

/-- The bounded actual directional derivative on completed Cartesian jets,
for the scalar Fourier induction in `app:ch_regular:eq:chain-tail`. -/
def completedDirectionalDerivative (m : ℕ) (v : ℝ × (Fin d → ℝ)) :
    Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) :=
  ((ofTest m volume).comp (directionalTest v)).extendOfNorm (ofTest (m + 1) volume)

/-- The derivative bound is fixed by the direction before the datum and
operator in `app:ch_regular:eq:chain-tail`. -/
theorem norm_completedDirectionalDerivative_apply_le (m : ℕ) (v : ℝ × (Fin d → ℝ))
    (u : Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ‖completedDirectionalDerivative m v u‖ ≤ directionCost v * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_ofTest (m + 1) volume)
    (directionCost v) (norm_jetMap_directionalTest_le m v) u

/-- The completed derivative agrees with the actual classical derivative on
every test field (`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem completedDirectionalDerivative_ofTest (m : ℕ) (v : ℝ × (Fin d → ℝ))
    (f : Test d) :
    completedDirectionalDerivative m v (ofTest (m + 1) volume f) =
      ofTest m volume (directionalTest v f) :=
  LinearMap.extendOfNorm_eq (denseRange_ofTest (m + 1) volume)
    ⟨directionCost v, norm_jetMap_directionalTest_le m v⟩ f

/-- Lowering the classical derivative budget cannot increase the jet norm
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_jetMap_lower_le (m : ℕ) (f : Test d) :
    ‖jetMap m volume f‖ ≤ ‖jetMap (m + 1) volume f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have he : jetMap m volume f i = jetMap (m + 1) volume f (raiseJetIndex i) := by
    apply Lp.ext
    filter_upwards [(jet_memLp volume i f).coeFn_toLp,
      (jet_memLp volume (raiseJetIndex i) f).coeFn_toLp] with p hp hq
    simpa only [jetMap, LinearMap.coe_mk, AddHom.coe_mk] using
      hp.trans ((congrFun (jet_raiseJetIndex i f).symm p).trans hq.symm)
  rw [he]
  exact norm_le_pi_norm _ _

/-- The concrete order-lowering map on the classical completion, for the
Fourier induction in `app:ch_regular:eq:chain-tail`. -/
def lowerOrder (m : ℕ) :
    Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) :=
  (ofTest m volume).extendOfNorm (ofTest (m + 1) volume)

/-- Lowering the budget is a contraction (`app:ch_regular:eq:chain-tail`). -/
theorem norm_lowerOrder_apply_le (m : ℕ)
    (u : Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ‖lowerOrder m u‖ ≤ ‖u‖ := by
  simpa only [lowerOrder, one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (f := ofTest m volume) (denseRange_ofTest (m + 1) volume) 1
    (fun f => by
      change ‖jetMap m volume f‖ ≤ 1 * ‖jetMap (m + 1) volume f‖
      simpa only [one_mul] using norm_jetMap_lower_le m f) u

/-- Order lowering retains the same actual test field
(`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem lowerOrder_ofTest (m : ℕ) (f : Test d) :
    lowerOrder m (ofTest (m + 1) volume f) = ofTest m volume f :=
  LinearMap.extendOfNorm_eq (denseRange_ofTest (m + 1) volume)
    ⟨1, fun f => by
      change ‖jetMap m volume f‖ ≤ 1 * ‖jetMap (m + 1) volume f‖
      simpa only [one_mul] using norm_jetMap_lower_le m f⟩ f

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
