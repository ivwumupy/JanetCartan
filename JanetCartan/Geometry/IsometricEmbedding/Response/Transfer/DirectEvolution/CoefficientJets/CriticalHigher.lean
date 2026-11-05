module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Critical
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Reserve
public import JanetCartan.Analysis.ODE.HigherVariational.Partitions

/-!
# Higher critical-map jets from the critical equation

The implicit-map input of the literal segment estimates in
`paper-v2.tex`, `new:eq:carrier-coefficient`. The single-block term in the
chain rule is solved with the actual Hessian inverse. All other terms
contain strictly lower critical jets. The consumer is the original
`paper.tex`, `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Above order one the identity component of the critical graph has zero
jet (`new:eq:carrier-coefficient`). -/
theorem iteratedFDeriv_criticalGraph_high {k : ℕ} (hk : 2 ≤ k)
    {w₀ : E → CarrierVariables n} {q : E} (hw₀ : ContDiffAt ℝ ∞ w₀ q) :
    iteratedFDeriv ℝ k (fun p ↦ (p, w₀ p)) q =
      (0 : E [×k]→L[ℝ] E).prod (iteratedFDeriv ℝ k w₀ q) := by
  have hid : iteratedFDeriv ℝ k (id : E → E) q = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show 2 + j = (j + 1) + 1 by omega]
    ext v
    rw [iteratedFDeriv_succ_apply_right]
    simp only [fderiv_id, iteratedFDeriv_succ_const, Pi.zero_apply, zero_apply]
  simpa only [id_eq, hid] using iteratedFDeriv_prodMk contDiffAt_id hw₀ (i := k) (by simp)

/-- The highest critical jet is bounded by a partition sum of primitive
gradient jets and strictly lower critical-graph jets. This is a consequence
of the actual critical equation, not an assumed implicit-map budget
(`new:eq:carrier-coefficient`). -/
theorem norm_jet_criticalPoint_le_partition_sum
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {q : E} (hq : q ∈ U) (h₀ : w₀ q ∈ D) (hw₀ : ContDiffAt ℝ ∞ w₀ q)
    (hcritical : ∀ p ∈ U, gradient (f p) (w₀ p) = 0)
    (hinv : IsUnit (averagedPhaseHessian f w₀ q (w₀ q)))
    {B : ℝ} (hB : ‖Ring.inverse (averagedPhaseHessian f w₀ q (w₀ q))‖ ≤ B)
    {k : ℕ} (hk : 2 ≤ k) :
    ‖iteratedFDeriv ℝ k w₀ q‖ ≤ B *
      ∑ p : OrderedFinpartition k with 2 ≤ p.length,
        ‖iteratedFDeriv ℝ p.length
          (fun z : E × CarrierVariables n ↦ gradient (f z.1) z.2) (q, w₀ q)‖ *
          ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) (fun z ↦ (z, w₀ z)) q‖ := by
  classical
  let G : E → E × CarrierVariables n := fun p ↦ (p, w₀ p)
  let V : E × CarrierVariables n → CarrierVariables n := fun p ↦ gradient (f p.1) p.2
  let H := averagedPhaseHessian f w₀ q (w₀ q)
  let T := fun p : OrderedFinpartition k ↦
    p.compAlongOrderedFinpartition (iteratedFDeriv ℝ p.length V (G q))
      (fun i ↦ iteratedFDeriv ℝ (p.partSize i) G q)
  let R := ∑ p : OrderedFinpartition k with 2 ≤ p.length, T p
  have hV : ContDiffAt ℝ ∞ V (G q) :=
    (contDiffOn_jointPhaseGradient hU hD hf).contDiffAt ((hU.prod hD).mem_nhds ⟨hq, h₀⟩)
  have hzero : iteratedFDeriv ℝ k (V ∘ G) q = 0 := by
    have heq : (V ∘ G) =ᶠ[𝓝 q] (fun _ ↦ 0) := by
      filter_upwards [hU.mem_nhds hq] with p hp
      exact hcritical p hp
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (heq.iteratedFDeriv ℝ k).eq_of_nhds
  have hchain := iteratedFDeriv_comp hV (contDiffAt_id.prodMk hw₀) (i := k) (by simp)
  rw [FormalMultilinearSeries.taylorComp] at hchain
  change iteratedFDeriv ℝ k (V ∘ G) q = ∑ p, T p at hchain
  have hkpos : 0 < k := by omega
  have hfilter : Finset.univ.filter (fun p : OrderedFinpartition k ↦ ¬ 2 ≤ p.length) =
      {ODE.singleBlockPartition k hkpos} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      exact ODE.eq_singleBlockPartition_of_length_eq_one hkpos p
        (by have := p.length_pos hkpos; omega)
    · rintro rfl
      simp [ODE.singleBlockPartition]
  have hsum := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (OrderedFinpartition k)) (fun p ↦ 2 ≤ p.length) T
  rw [hfilter, Finset.sum_singleton] at hsum
  have htop : T (ODE.singleBlockPartition k hkpos) =
      H.compContinuousMultilinearMap (iteratedFDeriv ℝ k w₀ q) := by
    ext v
    simp only [T, OrderedFinpartition.compAlongOrderFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply, ODE.singleBlockPartition,
      iteratedFDeriv_one_apply]
    change fderiv ℝ V (G q) (iteratedFDeriv ℝ k (fun p ↦ (p, w₀ p)) q v) = _
    rw [iteratedFDeriv_criticalGraph_high hk hw₀]
    simp only [ContinuousMultilinearMap.prod_apply, zero_apply]
    have he := congrArg (fun A : CarrierVariables n →L[ℝ] CarrierVariables n ↦
        A (iteratedFDeriv ℝ k w₀ q v))
      ((hV.differentiableAt (by simp)).hasFDerivAt.comp (w₀ q)
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) q (w₀ q))).fderiv
    simpa [H, averagedPhaseHessian_at_critical, V, G, Function.comp_def] using he.symm
  rw [htop, ← hchain, hzero] at hsum
  have hsolve : iteratedFDeriv ℝ k w₀ q = -(Ring.inverse H).compContinuousMultilinearMap R := by
    ext v
    have he := congrArg (fun A : E [×k]→L[ℝ] CarrierVariables n ↦ A v) hsum
    change R v + H (iteratedFDeriv ℝ k w₀ q v) = 0 at he
    have he' := congrArg (fun v : CarrierVariables n ↦ (Ring.inverse H) v)
      (eq_neg_of_add_eq_zero_right he)
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hinv] at he'
    simpa using he'
  rw [hsolve, norm_neg]
  apply ((Ring.inverse H).norm_compContinuousMultilinearMap_le R).trans
  apply mul_le_mul hB _ (norm_nonneg _) ((norm_nonneg _).trans hB)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦
    p.norm_compAlongOrderedFinpartition_le _ _)

/-- Uniform reserve-graded critical-graph jets derived from primitive joint
phase jets and the literal inverse gap. The constant precedes the reserve,
scale, box, phase and critical map; no high critical-map jet is assumed.
The phase costs one extra order, before the second derivative used in the
coefficient integrands (`new:eq:carrier-coefficient`). -/
theorem exists_criticalGraph_jet_bound_of_phase_profile
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) {B : ℝ} (hB : 0 ≤ B)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (R : ℕ), 1 ≤ R → ∀ (L : ℝ), 1 ≤ L →
      ∀ (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
        (U : Set E) (D : Set (CarrierVariables n)),
      IsOpen U → IsOpen D → ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D) →
      ∀ q ∈ U, w₀ q ∈ D → ContDiffAt ℝ ∞ w₀ q →
      (∀ p ∈ U, gradient (f p) (w₀ p) = 0) →
      IsUnit (averagedPhaseHessian f w₀ q (w₀ q)) →
      ‖Ring.inverse (averagedPhaseHessian f w₀ q (w₀ q))‖ ≤ B →
      (∀ j, 1 ≤ j → j ≤ k →
        ‖iteratedFDeriv ℝ (j + 1) (Function.uncurry f) (q, w₀ q)‖ ≤ A j * L ^ (j - R)) →
      ‖iteratedFDeriv ℝ k (fun p ↦ (p, w₀ p)) q‖ ≤ C * L ^ (k - R) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      refine ⟨1 + B * A 1, by linarith [mul_nonneg hB (hA 1)], ?_⟩
      intro R hR L hL f w₀ U D hU hD hf q hq h₀ hw₀ hc hu hi hp
      have hb := norm_fderiv_criticalPoint_le_phase hU hD hf hq h₀
        (hw₀.differentiableAt (by simp)) hc hu hi
      have hp1 : ‖iteratedFDeriv ℝ 2 (Function.uncurry f) (q, w₀ q)‖ ≤ A 1 := by
        simpa [Nat.sub_eq_zero_of_le hR] using hp 1 le_rfl le_rfl
      have hb' := hb.trans (mul_le_mul_of_nonneg_left hp1 hB)
      have hprod := iteratedFDeriv_prodMk contDiffAt_id hw₀ (i := 1) (by simp)
      simp only [id_eq] at hprod
      rw [hprod, ContinuousMultilinearMap.opNorm_prod]
      simp only [norm_iteratedFDeriv_one, fderiv_id, Nat.sub_eq_zero_of_le hR, pow_zero, mul_one]
      exact max_le (ContinuousLinearMap.norm_id_le.trans
        (by linarith [mul_nonneg hB (hA 1)])) (by linarith)
    · have hk2 : 2 ≤ k := by omega
      let C : ℕ → ℝ := fun j ↦ if hj : 1 ≤ j ∧ j < k then (ih j hj.2 hj.1).choose else 1
      have hC (j : ℕ) : 1 ≤ C j := by
        dsimp [C]
        split_ifs with hj
        · exact (ih j hj.2 hj.1).choose_spec.1
        · exact le_rfl
      let S := ∑ p : OrderedFinpartition k with 2 ≤ p.length,
        A p.length * ∏ i, C (p.partSize i)
      have hS : 0 ≤ S := Finset.sum_nonneg fun p _ ↦
        mul_nonneg (hA _) (Finset.prod_nonneg fun i _ ↦ zero_le_one.trans (hC _))
      refine ⟨1 + B * S, by linarith [mul_nonneg hB hS], ?_⟩
      intro R hR L hL f w₀ U D hU hD hf q hq h₀ hw₀ hc hu hi hp
      have hlower (j : ℕ) (hj : 1 ≤ j) (hjk : j < k) :
          ‖iteratedFDeriv ℝ j (fun p ↦ (p, w₀ p)) q‖ ≤ C j * L ^ (j - R) := by
        dsimp [C]
        rw [dite_eq_left ⟨hj, hjk⟩]
        exact (ih j hjk hj).choose_spec.2 R hR L hL f w₀ U D hU hD hf q hq h₀ hw₀
          hc hu hi (fun i hi hij ↦ hp i hi (hij.trans hjk.le))
      have hsum : (∑ p : OrderedFinpartition k with 2 ≤ p.length,
          ‖iteratedFDeriv ℝ p.length
            (fun z : E × CarrierVariables n ↦ gradient (f z.1) z.2) (q, w₀ q)‖ *
            ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) (fun z ↦ (z, w₀ z)) q‖) ≤
          S * L ^ (k - R) := by
        dsimp only [S]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro p hp'
        have hp2 := (Finset.mem_filter.mp hp').2
        calc
          _ ≤ (A p.length * L ^ (p.length - R)) *
              ∏ i, (C (p.partSize i) * L ^ (p.partSize i - R)) :=
            mul_le_mul ((norm_jet_jointPhaseGradient_le_phase hU hD hf _ ⟨hq, h₀⟩).trans
              (hp _ (by omega) p.length_le))
              (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
                hlower _ (p.partSize_pos i) (ODE.partSize_lt_of_two_le_length p hp2 i)))
              (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
              (mul_nonneg (hA _) (pow_nonneg (zero_le_one.trans hL) _))
          _ = (A p.length * ∏ i, C (p.partSize i)) *
              L ^ ((p.length - R) + ∑ i, (p.partSize i - R)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hL (partition_comp_reserve_le p hR))
            (mul_nonneg (hA _) (Finset.prod_nonneg fun i _ ↦ zero_le_one.trans (hC _)))
      rw [iteratedFDeriv_criticalGraph_high hk2 hw₀, ContinuousMultilinearMap.opNorm_prod,
        norm_zero, max_eq_right (norm_nonneg _)]
      calc
        _ ≤ _ := norm_jet_criticalPoint_le_partition_sum hU hD hf hq h₀ hw₀ hc hu hi hk2
        _ ≤ B * (S * L ^ (k - R)) := mul_le_mul_of_nonneg_left hsum hB
        _ ≤ (1 + B * S) * L ^ (k - R) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ResponseTransfer.DirectEvolution
