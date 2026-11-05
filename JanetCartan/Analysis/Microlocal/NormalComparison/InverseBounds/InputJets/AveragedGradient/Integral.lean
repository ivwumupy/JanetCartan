module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives

/-! # Integration of spatial jets

Differentiation under the segment integral in `app:ch_osc:setup:osc-normal`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.NormalComparison

/-- Partial spatial jets of a jointly smooth integrand are jointly smooth
(`app:ch_osc:setup:osc-normal`). -/
theorem contDiffAt_segmentSpatialJet
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ × P → E} {z : ℝ × P} (hH : ContDiffAt ℝ ∞ H z) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun w : ℝ × P ↦
      iteratedFDeriv ℝ k (fun y ↦ H (w.1, y)) w.2) z := by
  induction k with
  | zero =>
    let L : E →L[ℝ] (P [×0]→L[ℝ] E) :=
      (continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    convert! L.contDiff.contDiffAt.comp z hH using 1
  | succ k ih =>
    let L : (P →L[ℝ] (P [×k]→L[ℝ] E)) →L[ℝ] (P [×(k + 1)]→L[ℝ] E) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P)
        E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have ha : ContDiffAt ℝ ∞
        (fun w : (ℝ × P) × P ↦ iteratedFDeriv ℝ k (fun y ↦ H (w.1.1, y)) w.2)
        (z, z.2) := ih.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun w : ℝ × P ↦
        fderiv ℝ (iteratedFDeriv ℝ k (fun y ↦ H (w.1, y))) w.2) z :=
      ha.fderiv contDiffAt_snd (by simp)
    convert! L.contDiff.contDiffAt.comp z hd using 1

/-- Spatial jets commute with the unit segment integral under explicit
spatial jet bounds (`app:ch_osc:setup:osc-normal`). -/
theorem iteratedFDeriv_unitIntervalIntegral
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ × P → E} {U : Set P} {B : ℕ → ℝ} {k : ℕ}
    (hU : IsOpen U)
    (hH : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ U, ContDiffAt ℝ ∞ H z)
    (hb : ∀ j ≤ k, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ U,
      ‖iteratedFDeriv ℝ j (fun x ↦ H (t, x)) y‖ ≤ B j)
    {x : P} (hx : x ∈ U) :
    iteratedFDeriv ℝ k (fun y ↦ ∫ t in (0 : ℝ)..1, H (t, y)) x =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun y ↦ H (t, y)) x := by
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
    (b := fun j _ ↦ B j) hU _ _ _ _ le_rfl hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact ((hH (t, y) ⟨Ioc_subset_Icc_self ht, hy⟩).comp y
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  · intro j _ y hy
    have hc : ContinuousOn (fun t ↦ iteratedFDeriv ℝ j (fun x ↦ H (t, x)) y)
        (Icc (0 : ℝ) 1) := by
      intro t ht
      exact ((contDiffAt_segmentSpatialJet (hH (t, y) ⟨ht, hy⟩) j).continuousAt.comp
        (f := fun s : ℝ ↦ (s, y)) (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · intro j _
    exact integrable_const _
  · intro j hj
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact hb j hj t (Ioc_subset_Icc_self ht) y hy

/-- The explicit uniform spatial jet bound survives integration over a unit
segment (`app:ch_osc:prop:osc-normal`). -/
theorem norm_iteratedFDeriv_unitIntervalIntegral_le
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ × P → E} {U : Set P} {B : ℕ → ℝ} {k : ℕ}
    (hU : IsOpen U)
    (hH : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ U, ContDiffAt ℝ ∞ H z)
    (hb : ∀ j ≤ k, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ U,
      ‖iteratedFDeriv ℝ j (fun x ↦ H (t, x)) y‖ ≤ B j)
    {x : P} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ k (fun y ↦ ∫ t in (0 : ℝ)..1, H (t, y)) x‖ ≤ B k := by
  rw [iteratedFDeriv_unitIntervalIntegral hU hH hb hx]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (fun t ht ↦ hb k le_rfl t (by simpa using uIoc_subset_uIcc ht) x hx)

end JanetCartan.NormalComparison
