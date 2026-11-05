module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Local

/-!
# Fixed open patches for a simple scalar root

The fixed-patch implicit-function step of `app:ch_seed:prop:seed-actual-menu`.
Smoothness is proved on one open neighborhood, and the scalar derivative has a
positive uniform lower bound there. No solution function is an input.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- Continuity of the transverse derivative from smoothness of the symbol
(`app:ch_response:thm:response-compatible-choice`). -/
theorem continuousAt_scalarDerivative {f : P × ℝ → ℝ} {z : P × ℝ}
    (hf : ContDiffAt ℝ ∞ f z) : ContinuousAt (scalarDerivative f) z :=
  (hf.continuousAt_fderiv (by simp)).clm_apply continuousAt_const

/-- The constructed local root is smooth on a fixed open patch, is the unique
root in an open scalar neighborhood, and has a uniform positive derivative gap.
This is the local implicit-function step in `app:ch_seed:prop:seed-actual-menu`;
it also retains any coefficient parameters included in `P`. -/
theorem exists_localRoot_patch {f : P × ℝ → ℝ} {S : Set (P × ℝ)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {z : P × ℝ} (hzS : z ∈ S)
    (hz : f z = 0) (hd : scalarDerivative f z ≠ 0) :
    let H := localRoot (hf.contDiffAt (hS.mem_nhds hzS)) hd
    ∃ (U : Set P) (V : Set ℝ) (c : ℝ),
      IsOpen U ∧ z.1 ∈ U ∧ IsOpen V ∧ z.2 ∈ V ∧ 0 < c ∧
      ContDiffOn ℝ ∞ H U ∧
      (∀ q ∈ U, H q ∈ V ∧ (q, H q) ∈ S ∧ f (q, H q) = 0 ∧
        c ≤ |scalarDerivative f (q, H q)|) ∧
      (∀ q ∈ U, ∀ r ∈ V, f (q, r) = 0 ↔ H q = r) := by
  dsimp only
  let hf₀ := hf.contDiffAt (hS.mem_nhds hzS)
  let H := localRoot hf₀ hd
  have hH : ContDiffAt ℝ ∞ H z.1 := contDiffAt_localRoot hf₀ hd
  have hH₀ : H z.1 = z.2 := localRoot_base hf₀ hd
  obtain ⟨U₀, V, hU₀, hzU₀, hV, hzV, huniq⟩ :=
    mem_nhds_prod_iff'.mp (localRoot_eventually_unique hf₀ hd hz)
  let c := |scalarDerivative f z| / 2
  have hc : 0 < c := half_pos (abs_pos.mpr hd)
  have hclt : c < |scalarDerivative f z| := half_lt_self (abs_pos.mpr hd)
  have ht : Tendsto (fun q ↦ (q, H q)) (𝓝 z.1) (𝓝 z) := by
    simpa only [hH₀, id_eq, Prod.eta] using (continuousAt_id.prodMk hH.continuousAt).tendsto
  have hgap : ∀ᶠ q in 𝓝 z.1, c < |scalarDerivative f (q, H q)| :=
    ht.eventually ((continuousAt_scalarDerivative hf₀).abs.tendsto.eventually
      (eventually_gt_nhds hclt))
  have hVevent : ∀ᶠ q in 𝓝 z.1, H q ∈ V := by
    apply hH.continuousAt.preimage_mem_nhds
    simpa only [hH₀] using hV.mem_nhds hzV
  have hevent : ∀ᶠ q in 𝓝 z.1,
      q ∈ U₀ ∧ ContDiffAt ℝ 1 H q ∧ H q ∈ V ∧ (q, H q) ∈ S ∧
        f (q, H q) = 0 ∧ c < |scalarDerivative f (q, H q)| := by
    filter_upwards [hU₀.mem_nhds hzU₀,
      (hH.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp), hVevent,
      ht.eventually (hS.mem_nhds hzS), localRoot_eventually_zero hf₀ hd hz, hgap]
      with q hq hdiff hv hs he hg
    exact ⟨hq, hdiff, hv, hs, he, hg⟩
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hevent
  refine ⟨U, V, c, hU, hzU, hV, hzV, hc, ?_, ?_, ?_⟩
  · intro q hq
    have hprops := hUsub hq
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_of_continuous_root
      (hf.contDiffAt (hS.mem_nhds hprops.2.2.2.1))
      (abs_pos.mp (hc.trans hprops.2.2.2.2.2))
    · exact hprops.2.1.continuousAt
    · filter_upwards [hU.mem_nhds hq] with p hp
      exact (hUsub hp).2.2.2.2.1
  · intro q hq
    have hp := hUsub hq
    exact ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.le⟩
  · intro q hq r hr
    exact huniq ⟨(hUsub hq).1, hr⟩

end JanetCartan.CharacteristicRoot
