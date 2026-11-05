module

public import JanetCartan.Analysis.Calculus.HomogeneousTransversality
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Compact-family buffers for compatible response choices

The compactness steps in `app:ch_response:thm:response-compatible-choice`.
These results select gaps and a common response ball from geometric inputs;
they do not construct the energy roots or canonical projection charts.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.CompatibleResponse

/-- A continuous positive quantity on a compact family has one positive lower
bound (`app:ch_response:thm:response-compatible-choice`). Empty families are allowed. -/
theorem exists_uniform_positive_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ c > 0, ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, zero_lt_one, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x, hpos x hx, hmin⟩

/-- Compact protected carriers and a disjoint closed inactive source have a
strict positive gap, including the entire closed source support
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_uniform_source_gap {X : Type*} [PseudoMetricSpace X]
    {K S : Set X} (hK : IsCompact K) (hS : IsClosed S) (hdis : Disjoint K S) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ S, δ < dist x y := by
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist hK hS hdis
  refine ⟨(δ : ℝ), by exact_mod_cast hδ, ?_⟩
  intro x hx y hy
  have hg : δ < nndist x y := by
    exact_mod_cast (show (δ : ENNReal) < (nndist x y : ENNReal) from by simpa only [edist_nndist] using hgap x hx y hy)
  exact_mod_cast hg

/-- Finitely many pointed open patch cores contain one common buffered closed
response ball, chosen without frequencies or samples
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_common_response_ball {X ι : Type*} [PseudoMetricSpace X] [Finite ι]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) {p : X} (hp : ∀ i, p ∈ U i) :
    ∃ r > 0, ∀ i, closedBall p (2 * r) ⊆ U i := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (isOpen_iInter_of_finite hU)
    p (mem_iInter.mpr hp)
  refine ⟨ε / 4, by linarith, ?_⟩
  intro i x hx
  exact mem_iInter.mp (hsub (lt_of_le_of_lt hx (show 2 * (ε / 4) < ε by linarith))) i

/-- Euler's identity rules out a zero transverse covector on a nonzero
characteristic covector with a simple temporal root
(`app:ch_response:thm:response-compatible-choice`). -/
theorem transverse_covector_ne_zero {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {h : ℝ × U → ℝ} (hhom : PosHomogeneousOne h) {ξ : ℝ × U}
    (hξ : ξ ≠ 0) (hd : DifferentiableAt ℝ h ξ) (hzero : h ξ = 0)
    (hroot : fderiv ℝ h ξ (1, 0) ≠ 0) : ξ.2 ≠ 0 := by
  intro ht
  have hξt : ξ.1 ≠ 0 := by
    intro hz
    apply hξ
    exact Prod.ext hz ht
  have hsplit : ξ = ξ.1 • ((1 : ℝ), (0 : U)) := by
    apply Prod.ext <;> simp [ht]
  have he := hhom.euler hξ hd
  rw [hzero] at he
  have he' := congrArg (fderiv ℝ h ξ) hsplit
  rw [map_smul, smul_eq_mul] at he'
  exact (mul_ne_zero hξt hroot) (he'.symm.trans he)

/-- The root gap and transverse-covector gap share a positive constant on a
compact characteristic family (`app:ch_response:thm:response-compatible-choice`).
The symbol's regularity and simple-root hypotheses remain explicit. -/
theorem exists_root_and_transverse_gap {U : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    {h : ℝ × U → ℝ} (hhom : PosHomogeneousOne h) {K : Set (ℝ × U)}
    (hK : IsCompact K)
    (hξ : ∀ ξ ∈ K, ξ ≠ 0) (hd : ∀ ξ ∈ K, DifferentiableAt ℝ h ξ)
    (hzero : ∀ ξ ∈ K, h ξ = 0) (hroot : ∀ ξ ∈ K, fderiv ℝ h ξ (1, 0) ≠ 0)
    (hcont : ContinuousOn (fun ξ ↦ fderiv ℝ h ξ (1, 0)) K) :
    ∃ c > 0, ∀ ξ ∈ K, c ≤ |fderiv ℝ h ξ (1, 0)| ∧ c ≤ ‖ξ.2‖ := by
  obtain ⟨c, hc, hcroot⟩ := exists_uniform_positive_bound hK hcont.abs
    (fun ξ hξK ↦ abs_pos.mpr (hroot ξ hξK))
  obtain ⟨d, hdpos, hdtrans⟩ := exists_uniform_positive_bound hK
    (continuous_snd.norm.continuousOn : ContinuousOn (fun ξ : ℝ × U ↦ ‖ξ.2‖) K)
    (fun ξ hξK ↦ norm_pos_iff.mpr
      (transverse_covector_ne_zero hhom (hξ ξ hξK) (hd ξ hξK)
        (hzero ξ hξK) (hroot ξ hξK)))
  exact ⟨min c d, lt_min hc hdpos, fun ξ hξK ↦
    ⟨(min_le_left c d).trans (hcroot ξ hξK),
      (min_le_right c d).trans (hdtrans ξ hξK)⟩⟩

end JanetCartan.CompatibleResponse
