module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.TimeDifferentiation

/-!
# Parameter words for the full elapsed envelope

The annular endpoint uses ordered directional derivatives, whereas the completed
complementary endpoint uses Fréchet jets. These identities connect those exact
operations, including local equality and addition to the actual annular time
integral. The local domination input is produced by
`Parameter.exists_annularEnvelope_local_word_bounds_of_primitive_jets` and its
adjoint counterpart; no bound on the full output is used.
Consumer: the joint form of `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
open Pseudodifferential Parameter
variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Local equality identifies every actual ordered derivative, without a
regularity premise (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem orderedParameterWord_congr_nhds {f g : P → H} {c : P}
    (h : f =ᶠ[𝓝 c] g) (ps : List P) :
    orderedTransferAction (fun v F a => fderiv ℝ F a v) ps f c =
      orderedTransferAction (fun v F a => fderiv ℝ F a v) ps g c := by
  induction ps generalizing c with
  | nil => exact h.eq_of_nhds
  | cons v ps ih =>
    change fderiv ℝ _ c v = fderiv ℝ _ c v
    have he : orderedTransferAction (fun v F a => fderiv ℝ F a v) ps f =ᶠ[𝓝 c]
        orderedTransferAction (fun v F a => fderiv ℝ F a v) ps g := by
      filter_upwards [eventually_eventually_nhds.mpr h] with a ha
      exact ih ha
    rw [he.fderiv_eq]

/-- Ordered words are exactly the Fréchet jets of the integrated remainder.
The phase and physical operator stay fixed during these parameter derivatives.
Source: the joint assertion following `app:ch_response:eq:direct-envelope-profile`. -/
theorem orderedParameterWord_eq_iteratedFDeriv {U : Set P} (hU : IsOpen U)
    {g : P → H} (hg : ContDiffOn ℝ ∞ g U) (ps : List P) {c : P} (hc : c ∈ U) :
    orderedTransferAction (fun v F a => fderiv ℝ F a v) ps g c =
      iteratedFDeriv ℝ ps.length g c ps.get := by
  have he {k : ℕ} (v : Fin k → P) {a : P} (ha : a ∈ U) :
      orderedTransferAction (fun v F a => fderiv ℝ F a v) (List.ofFn v) g a =
        iteratedFDeriv ℝ k g a v := by
    induction k generalizing a with
    | zero => simp [orderedTransferAction, iteratedFDeriv_zero_apply]
    | succ k ih =>
      rw [List.ofFn_succ]
      change fderiv ℝ _ a (v 0) = _
      have he : orderedTransferAction (fun v F a => fderiv ℝ F a v)
          (List.ofFn (fun i => v i.succ)) g =ᶠ[𝓝 a]
          (fun b => iteratedFDeriv ℝ k g b (fun i => v i.succ)) := by
        filter_upwards [hU.mem_nhds ha] with b hb
        exact ih _ hb
      rw [he.fderiv_eq, DifferentiableAt.iteratedFDeriv_succ_apply_left']
      · rfl
      · exact (hg.contDiffAt (hU.mem_nhds ha)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top k : (k : ℕ∞ω) < ∞)
  simpa only [List.ofFn_get] using he ps.get hc

variable [FiniteDimensional ℝ P]
  {U : Set P} {Δ : ℝ} {f : ℝ → P → H}

/-- Every shorter word of the integrated annular operator is differentiable
using only fixed-time words through order `N`. The primitive local-domination
producer supplies the bound, without an extra jet or any time regularity of
critical points. Consumer: adding the true complementary remainder in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem differentiableAt_ordered_elapsedIntegral
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t => f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (N : ℕ)
    (hb : ∀ qs : List P, qs.length ≤ N → ∀ c ∈ U,
      ∃ V ∈ 𝓝 c, V ⊆ U ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
        ‖orderedTransferAction (fun v F a => fderiv ℝ F a v) qs (f t) a‖ ≤ B)
    (ps : List P) (hps : ps.length < N) {c : P} (hc : c ∈ U) :
    DifferentiableAt ℝ (orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
      (fun a => ∫ t in Icc 0 Δ, f t a)) c := by
  have hp := orderedTransferAction_elapsedIntegral hU hm hf N hb ps hps.le hc
  have he : orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
      (fun a => ∫ t in Icc 0 Δ, f t a) =ᶠ[𝓝 c]
      (fun a => ∫ t in Icc 0 Δ,
        orderedTransferAction (fun v F a => fderiv ℝ F a v) ps (f t) a) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact (orderedTransferAction_elapsedIntegral hU hm hf N hb ps hps.le ha).2
  obtain ⟨V, hV, hVU, B, hB⟩ := local_fderiv_bound_of_local_word_bounds N hb ps hps hc
  exact (hasFDerivAt_elapsedWordIntegral hU hm hf ps hc hp.1 hV hVU B hB).differentiableAt.congr_of_eventuallyEq he

/-- The full envelope's parameter word splits into the actual annular word
and the Fréchet jet of the actual integrated tail. All differentiability and
Bochner interchange needed for this addition follow from the original
fixed-time annular regularity and its primitive local domination. This analytic
identity is subsequently instantiated on the SAME full physical operator;
it does not assume a full-envelope estimate.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem ordered_elapsedIntegral_add
    (hU : IsOpen U)
    (hm : ∀ c ∈ U, AEStronglyMeasurable (fun t => f t c) (volume.restrict (Icc 0 Δ)))
    (hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (f t) U)
    (N : ℕ)
    (hb : ∀ qs : List P, qs.length ≤ N → ∀ c ∈ U,
      ∃ V ∈ 𝓝 c, V ⊆ U ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 Δ, ∀ a ∈ V,
        ‖orderedTransferAction (fun v F a => fderiv ℝ F a v) qs (f t) a‖ ≤ B)
    {g : P → H} (hg : ContDiffOn ℝ ∞ g U)
    (ps : List P) (hps : ps.length ≤ N) {c : P} (hc : c ∈ U) :
    orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
        (fun a => (∫ t in Icc 0 Δ, f t a) + g a) c =
      orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
        (fun a => ∫ t in Icc 0 Δ, f t a) c +
      iteratedFDeriv ℝ ps.length g c ps.get := by
  rw [← orderedParameterWord_eq_iteratedFDeriv hU hg ps hc]
  induction ps generalizing c with
  | nil => rfl
  | cons v ps ih =>
    have hlt : ps.length < N := lt_of_lt_of_le (Nat.lt_succ_self _) hps
    have he : orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
        (fun a => (∫ t in Icc 0 Δ, f t a) + g a) =ᶠ[𝓝 c]
        (fun a => orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
            (fun b => ∫ t in Icc 0 Δ, f t b) a +
          orderedTransferAction (fun v F a => fderiv ℝ F a v) ps g a) := by
      filter_upwards [hU.mem_nhds hc] with a ha
      exact ih hlt.le ha
    change fderiv ℝ _ c v = fderiv ℝ _ c v + fderiv ℝ _ c v
    rw [he.fderiv_eq, fderiv_fun_add
      (differentiableAt_ordered_elapsedIntegral hU hm hf N hb ps hlt hc)
      (((contDiffOn_orderedParameterWord hU hg ps).contDiffAt
        (hU.mem_nhds hc)).differentiableAt (by simp)), add_apply]

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
