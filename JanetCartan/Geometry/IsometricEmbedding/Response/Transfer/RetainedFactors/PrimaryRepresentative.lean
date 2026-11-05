module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointBounds

/-!
# A common smooth representative of the original primary phase

The integrated-envelope endpoints require a globally continuous primary phase,
whereas the actual Hamilton chart supplies smoothness only on its primary
domain. A single cutoff, chosen before the current coefficients, extends that
same phase. It agrees as a joint germ on the full retained carrier and keeps
the original frame shift one. No chart, source or physical operator is changed.
Consumer: `hφ`, `hcφ`, `hφb`, and `hsourceφ` in the two
`IntegratedEnvelope.Assembly` endpoints (`direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open DirectEvolution RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Fixing the primary parameter costs no derivative or norm factor. This
converts the actual joint phase profile to the spatial source profile in
the complementary integral (`app:ch_response:eq:direct-envelope-profile`). -/
theorem primary_phase_spatial_jet_le_joint
    (f : E × Euclidean 3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : E) (c : Euclidean 3) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f (y, c)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (x, c)‖ := by
  let L : E →L[ℝ] E × Euclidean 3 := (ContinuousLinearMap.id ℝ E).prod 0
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [L]
  have hh := Pseudodifferential.norm_iteratedFDeriv_comp_linear_le L
    (fun q ↦ f ((0, c) + q)) (hf.comp (contDiff_const.add contDiff_id)) j x
  have hh' := hh.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg L) hL))
  simpa only [iteratedFDeriv_comp_add_left', Function.comp_def, L,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply, Prod.mk_add_mk, zero_add, add_zero] using hh'

/-- Joint germ agreement of the primary representative preserves the literal
modulated phase in either orientation, including all elapsed and parameter
derivatives (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem jointRetainedCarrierPhase_primary_eventuallyEq
    (adj : Bool) (Ψ : TwoTimePhase d) (f g : E × Euclidean 3 → ℝ)
    {v : RetainedCarrierPoint d}
    (hout : f =ᶠ[𝓝 v.1.2] g)
    (hsource : f =ᶠ[𝓝 (v.2.fst, v.1.2.2)] g) :
    jointRetainedCarrierPhase adj Ψ (fun x c ↦ f (x, c)) =ᶠ[𝓝 v]
      jointRetainedCarrierPhase adj Ψ (fun x c ↦ g (x, c)) := by
  have hs : Continuous (fun w : RetainedCarrierPoint d ↦ (w.2.fst, w.1.2.2)) :=
    (((WithLp.fstL 2 ℝ E E).continuous.comp continuous_snd).prodMk continuous_fst.snd.snd)
  filter_upwards [hout.comp_tendsto continuous_fst.snd.continuousAt,
    hsource.comp_tendsto hs.continuousAt] with w ho hs
  change f w.1.2 = g w.1.2 at ho
  change f (w.2.fst, w.1.2.2) = g (w.2.fst, w.1.2.2) at hs
  cases adj <;> simp only [jointRetainedCarrierPhase, Bool.false_eq_true, ↓reduceIte,
    elapsedCarrierPhase, carrierPhase, CompactTransfer.adjointCarrierPhase, hs, ho]

end JanetCartan.ResponseTransfer.RetainedFactors

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse GeometricProfile
open ResponseTransfer.RetainedFactors
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)

/-- Construct the primary representative with ONE cutoff on the actual
primary domain before varying the coefficient field. The original shift-one
frame estimate bounds its joint jets on the carrier; the spatial source jets
and the parameter-first joint jets have exactly the same bound. These are
primitive phase estimates, not a hypothesis of successful envelope transfer
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_primaryPhaseInCoordinates_representative
    {c C : ℝ} (hP : P.IsValid c C) (i : Fin (d + 1))
    {K : Set (E × Euclidean 3)} (hK : IsCompact K)
    (hKU : ∀ q ∈ K, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
      q.2 ∈ parameterInterior (2 * P.radius)) :
    ∃ χ : E × Euclidean 3 → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧ ∀ Q,
        let f : E × Euclidean 3 → ℝ := fun q ↦ χ q * T.primaryPhaseInCoordinates i Q q.1 q.2
        ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        (∀ q ∈ K, f =ᶠ[𝓝 q] (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2)) ∧
        ∀ j, cNorm K j f ≤ A j *
          (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j + 1) Q.1) ∧
          ∀ q ∈ K,
            ‖iteratedFDeriv ℝ j f q‖ ≤ A j *
              (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j + 1) Q.1) ∧
            ‖iteratedFDeriv ℝ j (fun p : Euclidean 3 × E ↦ f p.swap) q.swap‖ ≤ A j *
              (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j + 1) Q.1) ∧
            ‖iteratedFDeriv ℝ j (fun y ↦ f (y, q.2)) q.1‖ ≤ A j *
              (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j + 1) Q.1) := by
  let Ω := ((primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius) ×ˢ
    parameterInterior (2 * P.radius)
  have hΩ : IsOpen Ω :=
    (isOpen_ball.preimage (primaryCoordinateChange i).symm.continuous).prod
      (isOpen_parameterInterior _)
  obtain ⟨χ, hχ, hcχ, hsχ, _, heχ⟩ := NormalComparison.exists_contDiff_localization
    hΩ hK hKU (contDiff_const (c := (1 : ℝ))).contDiffOn
  obtain ⟨A, hA, hbound⟩ := T.exists_primaryPhaseInCoordinates_frame_bound hP i hK hKU
  refine ⟨χ, hχ, hcχ, A, hA, ?_⟩
  intro Q f
  have hraw : ContDiffOn ℝ ∞ (fun q : E × Euclidean 3 ↦
      T.primaryPhaseInCoordinates i Q q.1 q.2) Ω :=
    (T.carrier_smooth hP Q).comp
      (((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun _ hq ↦ hq)
  have hf : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hraw.contDiffAt (hΩ.mem_nhds (hsχ hq)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with p hp
      change χ p = 0 at hp
      simp only [f, hp, zero_mul]
  have he q (hq : q ∈ K) : f =ᶠ[𝓝 q]
      (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) := by
    filter_upwards [heχ q hq] with p hp
    simp only [f, hp, one_mul]
  refine ⟨hf, hcχ.mul_right, he, ?_⟩
  intro j
  have hb : cNorm K j f ≤ A j *
      (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j + 1) Q.1) := by
    rw [cNorm_eq_of_eventuallyEq he j]
    exact hbound Q j
  refine ⟨hb, ?_⟩
  intro q hq
  have hj := (norm_iteratedFDeriv_le_cNorm hK (hf.of_le (by simp)) hq le_rfl).trans hb
  refine ⟨hj, ?_, (primary_phase_spatial_jet_le_joint f hf q.1 q.2 j).trans hj⟩
  simpa only [Function.comp_def, LinearIsometryEquiv.prodComm_apply, Prod.swap_swap] using
    ((LinearIsometryEquiv.prodComm ℝ (Euclidean 3) E).norm_iteratedFDeriv_comp_right
      f q.swap j).le.trans hj

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
