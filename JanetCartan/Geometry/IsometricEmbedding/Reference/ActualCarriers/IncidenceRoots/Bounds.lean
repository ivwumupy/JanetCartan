module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Refinement

/-!
# Fixed interior buffers for the continued incidence roots

The entire finite family of closed scalar intervals has a common positive
buffer inside the original parameter cubes. This buffer is chosen using only
the frozen refinement (`app:ch_seed:prop:seed-actual-menu`, Step 3).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- All scalar lines in the finite refinement stay a common positive distance
from every parameter face. Consequently every root constructed on these
intervals has this same interior buffer, independently of current phases
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem IncidenceRefinement.exists_uniform_interior_margin {n : ℕ} {D : CoverData n}
    {R : IncidenceRefinement D} (hR : R.IsValid) :
    ∃ η : ℝ, 0 < η ∧ ∀ j a, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
      ∀ i : Fin 3,
        |incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) t i| + η <
          (D.patches (R.sourceChart j) a).radius := by
  classical
  have hlocal (j a) (i : Fin 3) : ∃ η : ℝ, 0 < η ∧
      ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
        |incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) t i| + η <
          (D.patches (R.sourceChart j) a).radius := by
    let f : ℝ → ℝ := fun t ↦
      |incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) t i|
    have hf : Continuous f := by
      apply Continuous.abs
      exact (PiLp.continuous_apply 2 _ i).comp
        (continuous_const.add (continuous_id.smul continuous_const))
    obtain ⟨t, ht, hmax⟩ := (isCompact_Icc :
      IsCompact (Icc (-R.halfWidth j a) (R.halfWidth j a))).exists_isMaxOn
      (nonempty_Icc.mpr (by linarith [(hR.2.2.2 j a).1])) hf.continuousOn
    have hlt := (hR.2.2.2 j a).2.2.2.1 t ht i
    let η := ((D.patches (R.sourceChart j) a).radius - f t) / 2
    refine ⟨η, by dsimp [η, f]; linarith, ?_⟩
    intro s hs
    have hm : f s ≤ f t := hmax hs
    change f s + η < _
    dsimp [η]
    change f t < _ at hlt
    linarith
  choose η hη hbound using fun p :
      (j : Fin R.chartCount) × (Fin (D.patchCount (R.sourceChart j)) × Fin 3) ↦
    hlocal p.1 p.2.1 p.2.2
  obtain ⟨η₀, hη₀, hηle⟩ := Pi.exists_forall_pos_add_lt hη
  refine ⟨η₀, hη₀, ?_⟩
  intro j a t ht i
  have h := hbound ⟨j, a, i⟩ t ht
  have he : η₀ ≤ η ⟨j, a, i⟩ := by simpa using (hηle ⟨j, a, i⟩).le
  linarith

/-- The frozen equation differentials, lifted to include the physical variable,
have one finite bound on all buffered cylinders. This supplies the fixed low
constant for the actual root derivative estimate below
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem IncidenceRefinement.exists_uniform_frozen_derivative_bound {n : ℕ}
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {R : IncidenceRefinement D} (hR : R.IsValid) :
    ∃ M : ℝ, 0 < M ∧ ∀ j a,
      ∀ p : Euclidean n × Euclidean n,
      p.2 ∈ Metric.closedBall (R.center j) (2 * R.radius j) →
      ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
        ‖fderiv ℝ (fun w : (Euclidean n × Euclidean n) × ℝ ↦
          frozenDeterminantIncidence (D.patches (R.sourceChart j) a)
            (D.roots (R.sourceChart j) a (R.center j)) (w.1.2, w.2)) (p, t)‖ ≤ M := by
  classical
  let π : (Euclidean n × Euclidean n) × ℝ →L[ℝ] Euclidean n × ℝ :=
    ((ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
      (ContinuousLinearMap.fst ℝ (Euclidean n × Euclidean n) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n) ℝ)
  have hπ (v : (Euclidean n × Euclidean n) × ℝ) : ‖π v‖ ≤ ‖v‖ := by
    change max ‖v.1.2‖ ‖v.2‖ ≤ max (max ‖v.1.1‖ ‖v.1.2‖) ‖v.2‖
    exact max_le_max (le_max_right _ _) le_rfl
  have hlocal (j a) : ∃ M : ℝ, 0 < M ∧
      ∀ q ∈ Metric.closedBall (R.center j) (2 * R.radius j),
      ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
        ‖fderiv ℝ (frozenDeterminantIncidence (D.patches (R.sourceChart j) a)
          (D.roots (R.sourceChart j) a (R.center j))) (q, t)‖ ≤ M := by
    let K := Metric.closedBall (R.center j) (2 * R.radius j) ×ˢ
      Icc (-R.halfWidth j a) (R.halfWidth j a)
    have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
    have hf : ContinuousOn (fun w ↦ ‖fderiv ℝ
        (frozenDeterminantIncidence (D.patches (R.sourceChart j) a)
          (D.roots (R.sourceChart j) a (R.center j))) w‖) K := by
      intro w hw
      have hs := contDiffAt_frozenDeterminantIncidence
        (hD.2.2.2.2.1 (R.sourceChart j) a).1
        (D.roots (R.sourceChart j) a (R.center j)) w
        (fun i ↦ ((hR.2.2.2 j a).2.2.2.1 w.2 hw.2 i).le)
      exact (hs.continuousAt_fderiv (by simp)).norm.continuousWithinAt
    obtain ⟨M, hM⟩ := hK.bddAbove_image hf
    refine ⟨max M 0 + 1, by positivity, ?_⟩
    intro q hq t ht
    exact (hM (mem_image_of_mem _ (show (q, t) ∈ K from ⟨hq, ht⟩))).trans
      (by linarith [le_max_left M 0])
  choose M hM hbound using fun i :
      (j : Fin R.chartCount) × Fin (D.patchCount (R.sourceChart j)) ↦ hlocal i.1 i.2
  let B := 1 + ∑ i, M i
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg (fun i _ ↦ (hM i).le)
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro j a p hp t ht
  let f := frozenDeterminantIncidence (D.patches (R.sourceChart j) a)
    (D.roots (R.sourceChart j) a (R.center j))
  have hf : DifferentiableAt ℝ f (π (p, t)) :=
    (contDiffAt_frozenDeterminantIncidence (hD.2.2.2.2.1 (R.sourceChart j) a).1
      _ (p.2, t) (fun i ↦ ((hR.2.2.2 j a).2.2.2.1 t ht i).le)).differentiableAt (by simp)
  change ‖fderiv ℝ (f ∘ π) (p, t)‖ ≤ B
  rw [(hf.hasFDerivAt.comp (p, t) π.hasFDerivAt).fderiv]
  have hMB : M ⟨j, a⟩ ≤ B := by
    exact (Finset.single_le_sum (fun i _ ↦ (hM i).le) (Finset.mem_univ ⟨j, a⟩)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdiff : ‖fderiv ℝ f (π (p, t))‖ ≤ M ⟨j, a⟩ := hbound ⟨j, a⟩ p.2 hp t ht
  exact (((fderiv ℝ f (π (p, t))).comp π).opNorm_le_bound (hM ⟨j, a⟩).le
    (fun v ↦ ((fderiv ℝ f (π (p, t))).le_opNorm (π v)).trans
      (mul_le_mul hdiff (hπ v) (norm_nonneg _) (hM ⟨j, a⟩).le))).trans hMB

/-- A full `C¹` incidence comparison gives a fixed bound for the physical and
covector derivatives of each constructed root. The root hypotheses here are
outputs of `exists_current_incidence_roots_of_refinement`; the additional
comparison is a cylinder estimate supplied by Hamilton-phase continuity.
The constant is chosen before the current data
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem IncidenceRefinement.exists_uniform_root_derivative_bound {n : ℕ}
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {R : IncidenceRefinement D} (hR : R.IsValid) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ j a,
      ∀ (X : Set (Euclidean n)), IsOpen X →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (Θ : Euclidean n → Euclidean 3 → ℝ) (g : Euclidean n × Euclidean n → ℝ),
      let U := X ×ˢ Metric.ball (R.center j) (2 * R.radius j)
      let z := D.roots (R.sourceChart j) a (R.center j)
      let f := currentIncidence Q Θ z
      let f₀ := fun w : (Euclidean n × Euclidean n) × ℝ ↦
        frozenDeterminantIncidence (D.patches (R.sourceChart j) a) z (w.1.2, w.2)
      ContDiffOn ℝ ∞ g U →
      (∀ p ∈ U, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
        ContDiffAt ℝ ∞ f (p, t) ∧ ‖fderiv ℝ f (p, t) - fderiv ℝ f₀ (p, t)‖ ≤ 1) →
      (∀ p ∈ U, g p ∈ Ioo (-R.halfWidth j a) (R.halfWidth j a) ∧
        f (p, g p) = 0 ∧ c ≤ |scalarDerivative f (p, g p)|) →
      ∀ p ∈ U, ‖fderiv ℝ g p‖ ≤ B := by
  obtain ⟨M, hM, hbound⟩ := IncidenceRefinement.exists_uniform_frozen_derivative_bound hD hR
  refine ⟨(M + 1) / c, div_pos (by linarith) hc, ?_⟩
  intro j a X hX Q Θ g U z f f₀ hg hf hroot p hp
  have ht := Ioo_subset_Icc_self (hroot p hp).1
  have hU : IsOpen U := hX.prod Metric.isOpen_ball
  apply norm_fderiv_root_le hc ((hf p hp _ ht).1.differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    _ (hroot p hp).2.2
  · have h₀ : ‖fderiv ℝ f₀ (p, g p)‖ ≤ M :=
      hbound j a p (Metric.ball_subset_closedBall hp.2) (g p) ht
    calc
      _ ≤ ‖fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g p)‖ +
          ‖fderiv ℝ f₀ (p, g p)‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + M := add_le_add (hf p hp _ ht).2 h₀
      _ = M + 1 := add_comm _ _
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact (hroot q hq).2.1

end JanetCartan.ActualCarriers
