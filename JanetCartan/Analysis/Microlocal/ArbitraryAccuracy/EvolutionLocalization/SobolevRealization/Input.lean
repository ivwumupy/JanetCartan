module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Completion
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The order-zero Cartesian completion is L²

The input identification for `app:ch_regular:lem:finite-chain` and
`app:ch_regular:eq:chain-tail`. The completion uses space-first coordinates;
its test fields use time-first coordinates. The swap below is literal.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces

variable {d : ℕ}

/-- Evaluation of an actual completed jet, used to realize the output in
`app:ch_regular:eq:chain-tail`. -/
def completedJet (m : ℕ) (i : JetIndex d m) :
    Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)) :=
  (ContinuousLinearMap.proj i).comp (sobolevSubmodule m volume).subtypeL

/-- Evaluation retains the original completed L² class
(`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem completedJet_apply (m : ℕ) (i : JetIndex d m)
    (u : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    completedJet m i u = u.val i := rfl

/-- No norm loss occurs when extracting one jet in
`app:ch_regular:eq:chain-tail`. -/
theorem norm_completedJet_le (m : ℕ) (i : JetIndex d m)
    (u : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ‖completedJet m i u‖ ≤ ‖u‖ :=
  norm_le_pi_norm u.val i

/-- The exact test representative of a completed jet in
`app:ch_regular:eq:chain-tail`. -/
theorem completedJet_ofTest_ae (m : ℕ) (i : JetIndex d m) (f : Test d) :
    completedJet m i (ofTest m volume f) =ᵐ[volume] jet i f :=
  (jet_memLp volume i f).coeFn_toLp

private theorem zeroOrder_index_eq (i : JetIndex d 0) : i = zeroIndex d 0 := by
  obtain ⟨⟨k, hk⟩, w, ⟨j, hj⟩⟩ := i
  have hk0 : k = 0 := by omega
  subst k
  have hj0 : j = 0 := by omega
  subst j
  congr
  exact Subsingleton.elim _ _

/-- At order zero the single jet preserves the completion norm exactly
(`app:ch_regular:lem:finite-chain`). -/
def zeroJetIsometry :
    Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)) where
  toLinearMap := (completedJet 0 (zeroIndex d 0)).toLinearMap
  norm_map' u := by
    apply le_antisymm (norm_completedJet_le _ _ u)
    change ‖u.val‖ ≤ ‖u.val (zeroIndex d 0)‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [zeroOrder_index_eq i]

/-- Smooth compactly supported time-first fields are dense in the space-first
L² input of `app:ch_regular:eq:chain-tail`. -/
theorem denseRange_zeroJet_ofTest :
    DenseRange (fun f : Test d => completedJet 0 (zeroIndex d 0) (ofTest 0 volume f)) := by
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hc, hg, he⟩ := MemLp.exist_eLpNorm_sub_le
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp v)
    (show (0 : ℝ) < ε / 2 by positivity)
  let f : Test d := ⟨g ∘ Prod.swap, hg.comp (contDiff_snd.prodMk contDiff_fst),
    hc.comp_homeomorph (Homeomorph.prodComm _ _)⟩
  refine ⟨completedJet 0 (zeroIndex d 0) (ofTest 0 volume f), ⟨f, rfl⟩, ?_⟩
  rw [Lp.dist_def]
  have hf : completedJet 0 (zeroIndex d 0) (ofTest 0 volume f) =ᵐ[volume] g := by
    simpa only [jet_zeroIndex, f, Function.comp_apply, Prod.swap_prod_mk] using
      completedJet_ofTest_ae 0 (zeroIndex d 0) f
  have hae : (⇑v - ⇑(completedJet 0 (zeroIndex d 0) (ofTest 0 volume f))) =ᵐ[volume]
      (⇑v - g) := by
    filter_upwards [hf] with x hx
    exact congrArg (v x - ·) hx
  rw [eLpNorm_congr_ae hae]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) he).trans_lt (by linarith)

/-- Every Cartesian L² datum is the zeroth jet of a completed test field.
This closes the input completion obligation in `app:ch_regular:eq:chain-tail`. -/
theorem zeroJetIsometry_surjective : Function.Surjective (zeroJetIsometry (d := d)) := by
  have hd : DenseRange (zeroJetIsometry (d := d)) :=
    denseRange_zeroJet_ofTest.mono (by rintro _ ⟨f, rfl⟩; exact ⟨ofTest 0 volume f, rfl⟩)
  have hc : IsClosed (Set.range (zeroJetIsometry (d := d))) :=
    zeroJetIsometry.isometry.isClosedEmbedding.isClosed_range
  intro u
  have hu := hd u
  rw [hc.closure_eq] at hu
  exact hu

/-- Isometric identification of the actual order-zero completion and Cartesian
L². Its inverse supplies the input of the matrix extension in
`app:ch_regular:eq:chain-tail`. -/
def zeroJetEquiv :
    Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)) :=
  LinearIsometryEquiv.ofSurjective zeroJetIsometry zeroJetIsometry_surjective

/-- The isometric identification retains the exact zeroth jet in
`app:ch_regular:eq:chain-tail`. -/
@[simp] theorem zeroJetEquiv_apply
    (u : Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ))) :
    zeroJetEquiv u = completedJet 0 (zeroIndex d 0) u := rfl

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
