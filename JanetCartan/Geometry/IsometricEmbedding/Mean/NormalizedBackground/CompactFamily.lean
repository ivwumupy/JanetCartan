module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Smooth normalized pullbacks and a compact nonvanishing bound

Analytic ingredients of `app:ch_background:prop:bg-normalized`. These results
apply to a given coefficient field; identifying the actual geometric fields
with these pullbacks remains a separate geometric obligation.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace JanetCartan.NormalizedBackground

variable {E Z F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The regular pullback in `app:ch_background:eq:bg-Nsigma`, retaining the
carrier variable and defined also at scale zero. -/
def normalizedPullback (f : E × Z → F) (p : ℝ × (E × Z)) : F :=
  f (p.1 • p.2.1, p.2.2)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The scale-zero pullback freezes only the spatial variable
(`app:ch_background:prop:bg-normalized`). -/
@[simp] theorem normalizedPullback_zero (f : E × Z → F) (x : E) (z : Z) :
    normalizedPullback f (0, (x, z)) = f (0, z) := by
  simp [normalizedPullback]

/-- Joint smoothness, hence all mixed space/carrier derivatives, of regular
normalized factors (`app:ch_background:eq:bg-Nsigma`). -/
theorem contDiff_normalizedPullback {f : E × Z → F} {r : ℕ∞}
    (hf : ContDiff ℝ r f) : ContDiff ℝ r (normalizedPullback f) :=
  hf.comp ((contDiff_fst.smul contDiff_snd.fst).prodMk contDiff_snd.snd)

/-- Local version on the full inverse image of the coefficient domain; it
does not require a globally defined smooth phase or reference
(`app:ch_background:prop:bg-normalized`). -/
theorem contDiffOn_normalizedPullback {f : E × Z → F} {U : Set (E × Z)} {r : ℕ∞}
    (hf : ContDiffOn ℝ r f U) :
    ContDiffOn ℝ r (normalizedPullback f)
      {p : ℝ × (E × Z) | (p.1 • p.2.1, p.2.2) ∈ U} :=
  hf.comp ((contDiff_fst.smul contDiff_snd.fst).prodMk contDiff_snd.snd).contDiffOn
    (fun _ h ↦ h)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Cancellation of the positive scale in the normalized second-form and
transport factors of `app:ch_background:eq:bg-Nsigma`. -/
theorem inv_smul_scaled_pullback (f : E × Z → F) {σ : ℝ} (hσ : σ ≠ 0)
    (x : E) (z : Z) :
    σ⁻¹ • (σ • f (σ • x, z)) = normalizedPullback f (σ, (x, z)) := by
  simp [normalizedPullback, smul_smul, hσ]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Cancellation for the normalized inverse normal map in
`app:ch_background:eq:bg-Nsigma`. This is an algebraic identity only and
makes no assertion about the rank of the zero-scale immersion. -/
theorem smul_inv_scaled_pullback (f : E × Z → F) {σ : ℝ} (hσ : σ ≠ 0)
    (x : E) (z : Z) :
    σ • (σ⁻¹ • f (σ • x, z)) = normalizedPullback f (σ, (x, z)) := by
  simp [normalizedPullback, smul_smul, hσ]

omit [NormedSpace ℝ F] in
/-- Compactness turns nonvanishing at scale zero into a common positive lower
bound at all sufficiently small scales (`app:ch_background:prop:bg-normalized`).
Only continuity at the zero slice is required. -/
theorem exists_uniform_norm_lower_bound {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K) {f : ℝ × P → F}
    (hf : ∀ p ∈ K, ContinuousAt f (0, p)) (hne : ∀ p ∈ K, f (0, p) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ σ : ℝ, |σ| < ε → ∀ p ∈ K, c ≤ ‖f (σ, p)‖ := by
  have hcont : ContinuousOn (fun p ↦ ‖f (0, p)‖) K := by
    intro p hp
    exact ((hf p hp).comp (continuous_const.prodMk continuous_id).continuousAt).norm.continuousWithinAt
  obtain ⟨c, hc, hbound⟩ := hK.exists_forall_le' hcont
    (fun p hp ↦ norm_pos_iff.mpr (hne p hp))
  have hevent : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ p ∈ K, c / 2 < ‖f (σ, p)‖ := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    exact (hf p hp).norm.eventually (lt_mem_nhds ((half_lt_self hc).trans_le (hbound p hp)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨c / 2, half_pos hc, ε, hε, ?_⟩
  intro σ hσ p hp
  exact (hball (by simpa [Metric.mem_ball, Real.dist_eq] using hσ) p hp).le

/-- A fixed compact spatial domain dilates into any neighborhood of the seed
point for all sufficiently small scales (`app:ch_background:prop:bg-normalized`). -/
theorem exists_scale_mapsTo {K U : Set E} (hK : IsCompact K) (hU : U ∈ 𝓝 (0 : E)) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, |σ| ≤ σ₀ → MapsTo (fun x ↦ σ • x) K U := by
  have hevent : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ x ∈ K, σ • x ∈ U := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have hc : ContinuousAt (fun p : ℝ × E ↦ p.1 • p.2) (0, x) :=
      (continuous_fst.smul continuous_snd).continuousAt
    exact hc.eventually (by simpa using hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro σ hσ
  exact hball (by simpa [Metric.mem_ball, Real.dist_eq] using hσ.trans_lt (half_lt_self hε))

omit [NormedSpace ℝ Z] [NormedSpace ℝ F] in
/-- Nonvanishing of the frozen coefficient on a compact carrier set gives a
uniform positive norm bound for its normalized pullbacks on a fixed compact
spatial set (`app:ch_background:prop:bg-normalized`). -/
theorem exists_normalizedPullback_norm_lower_bound
    {K : Set E} (hK : IsCompact K) {L : Set Z} (hL : IsCompact L)
    {f : E × Z → F} (hf : ∀ z ∈ L, ContinuousAt f (0, z))
    (hne : ∀ z ∈ L, f (0, z) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, |σ| ≤ σ₀ →
      ∀ x ∈ K, ∀ z ∈ L, c ≤ ‖normalizedPullback f (σ, (x, z))‖ := by
  have hc : ∀ p ∈ K ×ˢ L, ContinuousAt (normalizedPullback f) (0, p) := by
    intro p hp
    have hm : ContinuousAt (fun q : ℝ × (E × Z) ↦ (q.1 • q.2.1, q.2.2)) (0, p) :=
      ((continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd).continuousAt
    have hf' : ContinuousAt f ((fun q : ℝ × (E × Z) ↦ (q.1 • q.2.1, q.2.2)) (0, p)) :=
      by simpa using hf p.2 hp.2
    exact hf'.comp (f := fun q : ℝ × (E × Z) ↦ (q.1 • q.2.1, q.2.2)) hm
  obtain ⟨c, hcpos, ε, hε, hbound⟩ := exists_uniform_norm_lower_bound (hK.prod hL) hc
    (fun p hp ↦ by simpa [normalizedPullback] using hne p.2 hp.2)
  exact ⟨c, hcpos, ε / 2, half_pos hε, fun σ hσ x hx z hz ↦
    hbound σ (hσ.trans_lt (half_lt_self hε)) (x, z) ⟨hx, hz⟩⟩

/-- All fixed joint derivative orders of a smooth normalized pullback have
uniform bounds on compact scale, space, and carrier sets
(`app:ch_background:prop:bg-normalized`). -/
theorem exists_normalizedPullback_mixed_derivative_bound
    {K : Set E} (hK : IsCompact K) {L : Set Z} (hL : IsCompact L)
    {f : E × Z → F} (hf : ContDiff ℝ ∞ f) (σ₀ : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (0 : ℝ) σ₀, ∀ x ∈ K, ∀ z ∈ L,
      ‖iteratedFDeriv ℝ s (normalizedPullback f) (σ, (x, z))‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ s (normalizedPullback f)) :=
    (contDiff_normalizedPullback hf).continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_Icc.prod (hK.prod hL)).image hc).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun σ hσ x hx z hz ↦ hbound _ ⟨(σ, (x, z)), ⟨hσ, hx, hz⟩, rfl⟩⟩

end JanetCartan.NormalizedBackground
