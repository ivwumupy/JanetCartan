module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Selector
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Homogeneity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Jets

/-!
# The averaged mixed inverse near a carrier

The literal average, phase-increment identity, selector inverse, and finite
joint jet bounds from
`app:ch_response:thm:response-literal-transfer`, immediately before
`app:ch_response:eq:direct-envelope-profile`. Inverse bounds use the Euclidean
operator norm; matrices use the Frobenius norm.

The final assembly `averagedMixedMatrix_physical_selector_jet_bounds` supplies
all these conclusions with a single radius chosen before frequency, including
Frobenius bounds for the matrix inverse. These deductions remain conditional
on primitive phase geometry and derivative bounds supplied by
`jc-compatible-phase-geometry` and `jc-finite-fio-calculus`. The consumer
`jc-response-near-carrier` must instantiate them uniformly on its compact
supports. No Hamilton phase or finite FIO calculus is constructed here.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Matrix.Norms.Frobenius ContDiff Topology

namespace JanetCartan.ResponseTransfer

local instance (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- Homogeneity identifies the actual physical average with its normalized
covector form, with no assumption about the average itself
(`app:ch_response:thm:response-literal-transfer`). -/
theorem averagedMixedMatrix_eq_normalized {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {U D : Set (Euclidean n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    {x ζ δ : Euclidean n} (hx : x ∈ U) (hζ : ζ ∈ D)
    {ρ : ℝ} (hρ : ρ ≠ 0) (hend : ζ + ρ⁻¹ • δ ∈ D)
    (hh : ∀ z ∈ U, ∀ ξ ∈ D, S z (ρ • ξ) = ρ * S z ξ)
    (hDx : ∀ ξ ∈ D, DifferentiableAt ℝ (fun z ↦ S z ξ) x)
    (hDξ : ∀ ξ ∈ D, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) ξ)
    (hDρξ : ∀ ξ ∈ D, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) (ρ • ξ)) :
    averagedMixedMatrix S ζ ρ x δ = averagedMixedMatrix S ζ 1 x (ρ⁻¹ • δ) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hξ := hcD.add_smul_mem hζ hend ht'
  have hpath : ρ • (ζ + t • (ρ⁻¹ • δ)) = ρ • ζ + t • δ := by
    simp only [smul_add, smul_smul]
    congr 1
    congr 1
    field_simp
  simpa only [one_smul, hpath] using
    mixedPhaseMatrix_smul_covector hU hD hx hξ hρ hh hDx (hDξ _ hξ) (hDρξ _ hξ)

/-- The normalized segment integral is the operator realization of the matrix
average. Differentiability of the primitive mixed operator on the chart
supplies integrability (`app:ch_response:thm:response-literal-transfer`). -/
theorem averagedMixedOperator_one_eq_integral {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {D : Set (Euclidean n)}
    (hD : Convex ℝ D) {x ζ ε : Euclidean n}
    (hζ : ζ ∈ D) (hend : ζ + ε ∈ D)
    (hA : ∀ η ∈ D, DifferentiableAt ℝ (mixedPhaseOperator S x) η) :
    averagedMixedOperator S ζ 1 x ε =
      ∫ t in (0 : ℝ)..1, mixedPhaseOperator S x (ζ + t • ε) := by
  have hc : ContinuousOn (fun t : ℝ ↦ mixedPhaseOperator S x (ζ + t • ε))
      (Icc 0 1) := by
    intro t ht
    exact ((hA _ (hD.add_smul_mem hζ hend ht)).continuousAt.comp
      (f := fun s : ℝ ↦ ζ + s • ε)
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hm : ContinuousOn
      (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S x (ζ + t • ε)) (Icc 0 1) := by
    simpa only [Function.comp_def, mixedPhaseOperator, ContinuousLinearEquiv.symm_apply_apply] using
      (mixedMatrixOperatorEquiv n).symm.continuous.comp_continuousOn hc
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S x ((1 : ℝ) • ζ + t • ε)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hm
  simpa only [one_smul] using averagedMixedOperator_eq_integral S ζ 1 x ε hi

/-- The actual averaged mixed operator is invertible with norm of inverse at
most `2M` throughout the explicit physical selector `‖δ‖ ≤ cρ`. The radius
`averagedMixedSelectorRadius b M K` is chosen before `ρ`; the only quantitative
inputs are the central inverse bound and the first normalized covector
derivative bound on the primitive mixed operator. No inverse or closeness
estimate for the average is an input
(`app:ch_response:thm:response-literal-transfer`). -/
theorem averagedMixedOperator_inverse_on_selector {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {U D : Set (Euclidean n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    {x ζ : Euclidean n} (hx : x ∈ U)
    {b M K : ℝ} (hb : 0 < b) (hbuffer : Metric.closedBall ζ b ⊆ D)
    (hu : IsUnit (mixedPhaseOperator S x ζ))
    (hM : ‖Ring.inverse (mixedPhaseOperator S x ζ)‖ ≤ M) (hK : 0 ≤ K)
    (hA : ∀ η ∈ D, DifferentiableAt ℝ (mixedPhaseOperator S x) η)
    (hd : ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : Euclidean n}
    (hδ : ‖δ‖ ≤ averagedMixedSelectorRadius b M K * ρ)
    (hh : ∀ z ∈ U, ∀ ξ ∈ D, S z (ρ • ξ) = ρ * S z ξ)
    (hDx : ∀ ξ ∈ D, DifferentiableAt ℝ (fun z ↦ S z ξ) x)
    (hDξ : ∀ ξ ∈ D, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) ξ)
    (hDρξ : ∀ ξ ∈ D, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) (ρ • ξ)) :
    IsUnit (averagedMixedOperator S ζ ρ x δ) ∧
      ‖Ring.inverse (averagedMixedOperator S ζ ρ x δ)‖ ≤ 2 * M := by
  have hε : ‖ρ⁻¹ • δ‖ ≤ averagedMixedSelectorRadius b M K := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), ← div_eq_inv_mul]
    exact (div_le_iff₀ hρ).mpr hδ
  have hζ : ζ ∈ D := hbuffer (Metric.mem_closedBall_self hb.le)
  have hend : ζ + ρ⁻¹ • δ ∈ D := by
    apply hbuffer
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hε.trans (min_le_left _ _)
  have he := averagedMixedMatrix_eq_normalized hU hD hcD hx hζ hρ.ne' hend hh hDx hDξ hDρξ
  have he' : averagedMixedOperator S ζ ρ x δ =
      averagedMixedOperator S ζ 1 x (ρ⁻¹ • δ) := congrArg (mixedMatrixOperatorEquiv n) he
  rw [he', averagedMixedOperator_one_eq_integral hcD hζ hend hA]
  exact segmentAverage_inverse_on_selector hcD hA hb hbuffer hu hM hK hd hε

/-- At normalized frequency the central inverse and primitive derivative
bound already imply invertibility of the actual average. This is the input
to the finite jet assembly for `app:ch_response:eq:direct-envelope-profile`. -/
theorem averagedMixedOperator_one_inverse_on_selector {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {D : Set (Euclidean n)}
    (hcD : Convex ℝ D) {x ζ : Euclidean n} {b M K : ℝ}
    (hb : 0 < b) (hbuffer : Metric.closedBall ζ b ⊆ D)
    (hu : IsUnit (mixedPhaseOperator S x ζ))
    (hM : ‖Ring.inverse (mixedPhaseOperator S x ζ)‖ ≤ M) (hK : 0 ≤ K)
    (hA : ∀ η ∈ D, DifferentiableAt ℝ (mixedPhaseOperator S x) η)
    (hd : ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K)
    {ε : Euclidean n} (hε : ‖ε‖ ≤ averagedMixedSelectorRadius b M K) :
    IsUnit (averagedMixedOperator S ζ 1 x ε) ∧
      ‖Ring.inverse (averagedMixedOperator S ζ 1 x ε)‖ ≤ 2 * M := by
  have hζ : ζ ∈ D := hbuffer (Metric.mem_closedBall_self hb.le)
  have hend : ζ + ε ∈ D := by
    apply hbuffer
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hε.trans (min_le_left _ _)
  rw [averagedMixedOperator_one_eq_integral hcD hζ hend hA]
  exact segmentAverage_inverse_on_selector hcD hA hb hbuffer hu hM hK hd hε

section JetAssembly

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n}
  {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D) (hcD : Convex ℝ D)
  {b M K : ℝ} (hb : 0 < b) (hbuffer : Metric.closedBall ζ b ⊆ D)
  (hu : ∀ x ∈ X, IsUnit (mixedPhaseOperator S x ζ))
  (hM : ∀ x ∈ X, ‖Ring.inverse (mixedPhaseOperator S x ζ)‖ ≤ M) (hK : 0 ≤ K)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))
  (hd : ∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K)
  {C : ℕ → ℝ} {L : ℝ} {r : ℕ} (hL : 1 ≤ L)
  (hjets : ∀ j ≤ r, ∀ q ∈ X ×ˢ D,
    ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤
      C j * L ^ j)

include hX hD hS in
private theorem mixedPhaseOperator_differentiableOn_covectors {x : Euclidean n}
    (hx : x ∈ X) : ∀ η ∈ D, DifferentiableAt ℝ (mixedPhaseOperator S x) η := by
  intro η hη
  have hs := (hS.contDiffAt ((hX.prod hD).mem_nhds ⟨hx, hη⟩)).comp η
    (contDiffAt_const.prodMk contDiffAt_id)
  exact ((mixedMatrixOperatorEquiv n).contDiff.contDiffAt.comp η hs).differentiableAt
    (by simp)

include hX hD hcD hb hbuffer hu hM hK hS hd hL hjets in
/-- Finite joint bounds for the average and both realizations of its inverse,
with every averaged-inverse premise discharged from primitive phase data.
The closed selector has radius `c = averagedMixedSelectorRadius b M K / 2`;
the larger open ball supplies a neighborhood even at its boundary. The
constants depend only on the primitive budgets and the central inverse bound,
not on `L` or frequency (`app:ch_response:eq:direct-envelope-profile`).
The geometry/FIO producers must supply the displayed primitive hypotheses
uniformly on the physical and carrier supports. -/
theorem averagedMixedMatrix_selector_jet_bounds
    {p : Euclidean n × Euclidean n} (hp : p.1 ∈ X)
    (hε : ‖p.2‖ ≤ averagedMixedSelectorRadius b M K / 2)
    {k : ℕ} (hk : k ≤ r) :
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      averagedMixedMatrix S ζ 1 q.1 q.2) p‖ ≤ C k * L ^ k ∧
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      Ring.inverse (averagedMixedOperator S ζ 1 q.1 q.2)) p‖ ≤
        averagedMixedInverseJetConstant n k C M * L ^ k ∧
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      (averagedMixedMatrix S ζ 1 q.1 q.2)⁻¹) p‖ ≤
        (‖(mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap‖ *
          averagedMixedInverseJetConstant n k C M) * L ^ k := by
  let V := Metric.ball (0 : Euclidean n) (averagedMixedSelectorRadius b M K)
  have hV : IsOpen V := Metric.isOpen_ball
  have hpos := averagedMixedSelectorRadius_pos hb ((norm_nonneg _).trans (hM _ hp)) hK
  have hpV : p ∈ X ×ˢ V := ⟨hp, by
    simpa [V, Metric.mem_ball, dist_zero_right] using hε.trans_lt (by linarith)⟩
  have hζ : ζ ∈ D := hbuffer (Metric.mem_closedBall_self hb.le)
  have hbuf : ∀ ε ∈ V, ζ + ε ∈ D := by
    intro ε hε
    apply hbuffer
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (by simpa [V, Metric.mem_ball, dist_zero_right] using hε :
      ‖ε‖ < averagedMixedSelectorRadius b M K).le.trans (min_le_left _ _)
  have hinv : ∀ q ∈ X ×ˢ V,
      IsUnit (averagedMixedOperator S ζ 1 q.1 q.2) ∧
        ‖Ring.inverse (averagedMixedOperator S ζ 1 q.1 q.2)‖ ≤ 2 * M := by
    intro q hq
    exact averagedMixedOperator_one_inverse_on_selector hcD hb hbuffer (hu _ hq.1)
      (hM _ hq.1) hK (mixedPhaseOperator_differentiableOn_covectors hX hD hS hq.1)
      (hd _ hq.1) (by
        exact (by simpa [V, Metric.mem_ball, dist_zero_right] using hq.2 :
          ‖q.2‖ < averagedMixedSelectorRadius b M K).le)
  exact ⟨norm_iteratedFDeriv_averagedMixedMatrix_normalized_le
      hX hD hV hcD hζ hbuf hS hjets hk hpV,
    norm_iteratedFDeriv_averagedMixedOperator_inverse_le
      hX hD hV hcD hζ hbuf hS hL hjets
      (fun q hq ↦ (hinv q hq).1) (fun q hq ↦ (hinv q hq).2) hk hpV,
    norm_iteratedFDeriv_averagedMixedMatrix_inverse_le
      hX hD hV hcD hζ hbuf hS hL hjets
      (fun q hq ↦ (hinv q hq).1) (fun q hq ↦ (hinv q hq).2) hk hpV⟩

include hX hD hcD hb hbuffer hu hM hK hS hd hL hjets in
/-- The literal physical average and its inverse have the same finite joint
`x`/normalized-covector jet bounds, uniformly in every positive frequency.
Here the joint variable is `(x, ε)` with physical displacement `δ = ρ ε`.
The positive selector `c = averagedMixedSelectorRadius b M K / 2` is fixed
before `ρ`; in particular `‖ε‖ ≤ c` is exactly `‖δ‖ ≤ cρ`.
All inverse hypotheses of the jet helper are discharged. Only primitive
smoothness, homogeneity, chart buffering, central inverse bounds, and primitive
derivative budgets remain conditional
(`app:ch_response:thm:response-literal-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedMixedMatrix_physical_selector_jet_bounds
    {ρ : ℝ} (hρ : 0 < ρ)
    (hh : ∀ x ∈ X, ∀ ξ ∈ D, S x (ρ • ξ) = ρ * S x ξ)
    (hDx : ∀ x ∈ X, ∀ ξ ∈ D, DifferentiableAt ℝ (fun z ↦ S z ξ) x)
    (hDξ : ∀ x ∈ X, ∀ ξ ∈ D, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) ξ)
    (hDρξ : ∀ x ∈ X, ∀ ξ ∈ D, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) (ρ • ξ))
    {p : Euclidean n × Euclidean n} (hp : p.1 ∈ X)
    (hε : ‖p.2‖ ≤ averagedMixedSelectorRadius b M K / 2)
    {k : ℕ} (hk : k ≤ r) :
    0 < averagedMixedSelectorRadius b M K / 2 ∧
    IsUnit (averagedMixedOperator S ζ ρ p.1 (ρ • p.2)) ∧
    ‖Ring.inverse (averagedMixedOperator S ζ ρ p.1 (ρ • p.2))‖ ≤ 2 * M ∧
    (∀ i : Fin n,
      partialDeriv (fun x ↦ phaseIncrement S ζ ρ x (ρ • p.2)) p.1 i =
        averagedMixedOperator S ζ ρ p.1 (ρ • p.2) (ρ • p.2) i) ∧
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      averagedMixedMatrix S ζ ρ q.1 (ρ • q.2)) p‖ ≤ C k * L ^ k ∧
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      Ring.inverse (averagedMixedOperator S ζ ρ q.1 (ρ • q.2))) p‖ ≤
        averagedMixedInverseJetConstant n k C M * L ^ k ∧
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × Euclidean n ↦
      (averagedMixedMatrix S ζ ρ q.1 (ρ • q.2))⁻¹) p‖ ≤
        (‖(mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap‖ *
          averagedMixedInverseJetConstant n k C M) * L ^ k := by
  have hpos := averagedMixedSelectorRadius_pos hb ((norm_nonneg _).trans (hM _ hp)) hK
  have hε' : ‖p.2‖ ≤ averagedMixedSelectorRadius b M K := hε.trans (by linarith)
  have hζ : ζ ∈ D := hbuffer (Metric.mem_closedBall_self hb.le)
  let V := (fun ε : Euclidean n ↦ ζ + ε) ⁻¹' D
  have hV : IsOpen V := hD.preimage (continuous_const.add continuous_id)
  have hpV : p ∈ X ×ˢ V := by
    refine ⟨hp, hbuffer ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hε'.trans (min_le_left _ _)
  have he : (fun q : Euclidean n × Euclidean n ↦
      averagedMixedMatrix S ζ ρ q.1 (ρ • q.2)) =ᶠ[𝓝 p]
      (fun q ↦ averagedMixedMatrix S ζ 1 q.1 q.2) := by
    apply eventuallyEq_of_mem ((hX.prod hV).mem_nhds hpV)
    intro q hq
    have hn : ρ⁻¹ • (ρ • q.2) = q.2 := by
      rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    simpa only [hn] using averagedMixedMatrix_eq_normalized (δ := ρ • q.2)
      hX hD hcD hq.1 hζ hρ.ne'
      (by simpa only [hn] using (show ζ + q.2 ∈ D from hq.2))
      hh (hDx _ hq.1) (hDξ _ hq.1) (hDρξ _ hq.1)
  have heop := he.fun_comp (mixedMatrixOperatorEquiv n)
  have hi := averagedMixedOperator_one_inverse_on_selector hcD hb hbuffer (hu _ hp)
    (hM _ hp) hK (mixedPhaseOperator_differentiableOn_covectors hX hD hS hp)
    (hd _ hp) hε'
  have heop' : averagedMixedOperator S ζ ρ p.1 (ρ • p.2) =
      averagedMixedOperator S ζ 1 p.1 p.2 := heop.eq_of_nhds
  have hpath (t : ℝ) : ρ • ζ + t • (ρ • p.2) = ρ • (ζ + t • p.2) := by
    simp only [smul_add, smul_smul, mul_comm]
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + t • p.2 ∈ D :=
    fun _ ht ↦ hcD.add_smul_mem hζ hpV.2 ht
  have hxρ : ∀ η ∈ D, DifferentiableAt ℝ (fun x ↦ S x (ρ • η)) p.1 := by
    intro η hη
    exact ((hDx _ hp η hη).const_mul ρ).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hX.mem_nhds hp) (fun x hx ↦ hh x hx η hη))
  have hξ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun x ↦ S x η) p.1 i)
        (ρ • ζ + t • (ρ • p.2)) := by
    intro t ht i
    rw [hpath]
    exact hDρξ _ hp _ (hseg t ht) i
  have hc : ContinuousOn
      (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S p.1
        (ρ • ζ + t • (ρ • p.2))) (Icc 0 1) := by
    have hc₁ : ContinuousOn
        (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S p.1 (ζ + t • p.2))
        (Icc 0 1) := by
      intro t ht
      have hcprim : ContinuousAt (Function.uncurry (FourierIntegral.mixedPhaseMatrix S))
          (p.1, ζ + t • p.2) :=
        (hS.contDiffAt ((hX.prod hD).mem_nhds
          (show (p.1, ζ + t • p.2) ∈ X ×ˢ D from ⟨hp, hseg t ht⟩))).continuousAt
      have hpcont : ContinuousAt (fun s : ℝ ↦ (p.1, ζ + s • p.2)) t :=
        continuousAt_const.prodMk
          (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
      exact (hcprim.comp (f := fun s : ℝ ↦ (p.1, ζ + s • p.2)) hpcont).continuousWithinAt
    apply hc₁.congr
    intro t ht
    dsimp only
    rw [hpath]
    exact mixedPhaseMatrix_smul_covector hX hD hp (hseg t ht) hρ.ne' hh
      (hDx _ hp) (hDξ _ hp _ (hseg t ht)) (hDρξ _ hp _ (hseg t ht))
  have hid : ∀ i : Fin n,
      partialDeriv (fun x ↦ phaseIncrement S ζ ρ x (ρ • p.2)) p.1 i =
        averagedMixedOperator S ζ ρ p.1 (ρ • p.2) (ρ • p.2) i := by
    apply partialDeriv_phaseIncrement_eq_averagedMixedOperator S ζ ρ p.1 (ρ • p.2)
      (hxρ ζ hζ) _ hξ hc
    simpa only [smul_add] using hxρ (ζ + p.2) hpV.2
  refine ⟨by positivity, heop' ▸ hi.1, heop' ▸ hi.2, hid, ?_⟩
  have hj := averagedMixedMatrix_selector_jet_bounds
    hX hD hcD hb hbuffer hu hM hK hS hd hL hjets hp hε hk
  have he₁ := (he.iteratedFDeriv ℝ k).eq_of_nhds
  have he₂ := ((heop.fun_comp Ring.inverse).iteratedFDeriv ℝ k).eq_of_nhds
  have he₃ := ((he.fun_comp (fun A ↦ A⁻¹)).iteratedFDeriv ℝ k).eq_of_nhds
  exact ⟨he₁ ▸ hj.1, he₂ ▸ hj.2.1, he₃ ▸ hj.2.2⟩

end JetAssembly

end JanetCartan.ResponseTransfer
