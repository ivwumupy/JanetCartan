module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.CriticalHigher
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InverseJetInduction.Bounds

/-!
# Reserve-graded jets of the actual moving segment average

The integration step in `paper-v2.tex`, `new:eq:carrier-coefficient`.
The critical-graph jet input below is produced by
`exists_criticalGraph_jet_bound_of_phase_profile`, from the actual critical
equation. The final coefficient assembly instantiates it; it is not a new
geometric assumption. The consumer is the original
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every positive segment jet is controlled by the corresponding critical
graph jet and a fixed linear term (`new:eq:carrier-coefficient`). -/
theorem norm_jet_criticalSegment_le
    {w₀ : E → CarrierVariables n} {U : Set E} (hU : IsOpen U)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) {z : E × CarrierVariables n} (hz : z.1 ∈ U)
    {j R : ℕ} (hj : 1 ≤ j) {C L : ℝ} (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hjet : ‖iteratedFDeriv ℝ j (fun q ↦ (q, w₀ q)) z.1‖ ≤ C * L ^ (j - R))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun q : E × CarrierVariables n ↦
      (q.1, w₀ q.1 + t • (q.2 - w₀ q.1))) z‖ ≤ (1 + C) * L ^ (j - R) := by
  let G : E → E × CarrierVariables n := fun q ↦ (q, w₀ q)
  let P := ContinuousLinearMap.fst ℝ E (CarrierVariables n)
  have hG : ContDiffOn ℝ ∞ G U := contDiffOn_id.prodMk hw₀
  have hGP : ContDiffAt ℝ j (G ∘ P) z :=
    ((hG.contDiffAt (hU.mem_nhds hz)).comp z P.contDiff.contDiffAt).of_le (by simp)
  have hid : ContDiffAt ℝ j (id : E × CarrierVariables n → E × CarrierVariables n) z :=
    contDiffAt_id
  have hpull : ‖iteratedFDeriv ℝ j (G ∘ P) z‖ ≤ C * L ^ (j - R) := by
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le P hU hG hz j).trans
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg P) (ContinuousLinearMap.norm_fst_le ℝ E (CarrierVariables n)))).trans hjet
  have hidjet : ‖iteratedFDeriv ℝ j (id : E × CarrierVariables n → E × CarrierVariables n) z‖ ≤ 1 :=
    (NormalComparison.InverseChartJet.norm_iteratedFDeriv_linear_pos_le
      (ContinuousLinearMap.id ℝ (E × CarrierVariables n)) z hj).trans ContinuousLinearMap.norm_id_le
  have heq : (fun q : E × CarrierVariables n ↦ (q.1, w₀ q.1 + t • (q.2 - w₀ q.1))) =
      fun q ↦ (1 - t) • (G ∘ P) q + t • id q := by
    funext q
    apply Prod.ext
    · change q.1 = (1 - t) • q.1 + t • q.1
      module
    · change w₀ q.1 + t • (q.2 - w₀ q.1) = (1 - t) • w₀ q.1 + t • q.2
      module
  rw [heq, fun_iteratedFDeriv_add_apply (hGP.const_smul (1 - t)) (hid.const_smul t),
    iteratedFDeriv_const_smul_apply' hGP, iteratedFDeriv_const_smul_apply' hid]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
  calc
    _ ≤ (1 - t) * (C * L ^ (j - R)) + t * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hpull (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hidjet ht.1)
    _ ≤ C * L ^ (j - R) + L ^ (j - R) :=
      add_le_add (mul_le_of_le_one_left (mul_nonneg hC (pow_nonneg (zero_le_one.trans hL) _))
        (by linarith [ht.1])) (by simpa using ht.2.trans (one_le_pow₀ hL))
    _ = _ := by ring

/-- The moving segment integral preserves a positive reserve. Smoothness
and the finite integrand budgets justify all differentiations under the
integral via the existing segment differentiation API
(`new:eq:carrier-coefficient`). -/
theorem norm_jet_criticalSegmentAverage_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : E × CarrierVariables n → F} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ D)) (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (h₀ : MapsTo w₀ U D) {N k R : ℕ} (hR : 1 ≤ R)
    (A C : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hC : ∀ j, 0 ≤ C j)
    {L : ℝ} (hL : 1 ≤ L)
    (hHjet : ∀ j ≤ N, ∀ z ∈ U ×ˢ D, ‖iteratedFDeriv ℝ j H z‖ ≤ A j * L ^ (j - R))
    (hwjet : ∀ j, 1 ≤ j → j ≤ N → ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun p ↦ (p, w₀ p)) q‖ ≤ C j * L ^ (j - R))
    (hk : k ≤ N) {z : E × CarrierVariables n} (hz : z ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ k (fun q : E × CarrierVariables n ↦
      ∫ t in (0 : ℝ)..1, H (q.1, w₀ q.1 + t • (q.2 - w₀ q.1))) z‖ ≤
      GradedPrimitives.compositionConstant A (fun j ↦ 1 + C j) k * L ^ (k - R) := by
  have hbound (j : ℕ) (hj : j ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j (fun p : E × CarrierVariables n ↦
        H (p.1, w₀ p.1 + t • (p.2 - w₀ p.1))) q‖ ≤
        GradedPrimitives.compositionConstant A (fun i ↦ 1 + C i) j * L ^ (j - R) := by
    let S : E × CarrierVariables n → E × CarrierVariables n :=
      fun p ↦ (p.1, w₀ p.1 + t • (p.2 - w₀ p.1))
    have hmem : S q ∈ U ×ˢ D := ⟨hq.1, hcD.add_smul_sub_mem (h₀ hq.1) hq.2 ht⟩
    have hw := (hw₀.contDiffAt (hU.mem_nhds hq.1)).comp q contDiffAt_fst
    have hS : ContDiffAt ℝ N S q :=
      (contDiffAt_fst.prodMk (hw.add ((contDiffAt_snd.sub hw).const_smul t))).of_le (by simp)
    exact norm_jet_comp_reserve_le hS
      ((hH.contDiffAt ((hU.prod hD).mem_nhds hmem)).of_le (by simp)) hj A
      (fun i ↦ 1 + C i) hA (fun i ↦ by linarith [hC i]) hL hR
      (fun i hi ↦ hHjet i (hi.trans hj) _ hmem)
      (fun i hi hij ↦ norm_jet_criticalSegment_le hU hw₀ hq.1 hi (hC i) hL
        (hwjet i hi (hij.trans hj) q.1 hq.1) ht)
  exact NormalComparison.norm_iteratedFDeriv_unitIntervalIntegral_le
    (H := fun p : ℝ × (E × CarrierVariables n) ↦
      H (p.2.1, w₀ p.2.1 + p.1 • (p.2.2 - w₀ p.2.1)))
    (B := fun j ↦ GradedPrimitives.compositionConstant A (fun i ↦ 1 + C i) j * L ^ (j - R))
    (hU.prod hD) (fun p hp ↦ contDiffAt_criticalSegmentIntegrand hU hD hcD hH hw₀ h₀ hp)
    (fun j hj ↦ hbound j (hj.trans hk)) hz

end JanetCartan.ResponseTransfer.DirectEvolution
