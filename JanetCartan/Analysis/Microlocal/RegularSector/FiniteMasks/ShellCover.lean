module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.SymbolBounds

/-!
# A finite normalized carrier cover for the actual conic mask

Normalize by `R = 1 + ‖ξ‖`, as required by the weighted-jet conversion in
`EvolutionIntegral.SymbolBudgets.hasFullSourceSymbolBound_elapsedAmplitude`.
The fixed unit collar puts the normalized frequency in the compact annulus
with radii one half and one. Compactness then constructs finitely many
buffered balls inside any specified open chart containing this carrier.
The same cover supplies all normalized multiplier budgets at every order.
Source: `app:ch_regular_base:lem:retarded-kernel` and `finite-calculus`.
-/

@[expose] public noncomputable section
open Set Metric Function
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteMasks
open CompatibleResponse FourierIntegral.PrimitiveProfiles
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "P" => (Euclidean n × Euclidean n) × Euclidean n

/-- The literal compact normalized carrier of the fixed angular mask,
including its shoulders and both physical positions (`retarded-kernel`). -/
def normalizedMaskCarrier (X : Set (E × E)) (a : E → ℝ) : Set P :=
  X ×ˢ ((fun p : ℝ × E ↦ p.1 • p.2) ''
    (Icc (1 / 2 : ℝ) 1 ×ˢ (tsupport a ∩ sphere (0 : E) 1)))

/-- The normalized carrier is compact, even without compact support of the
angular function: its intersection with the unit sphere is compact. -/
theorem isCompact_normalizedMaskCarrier {X : Set (E × E)} (hX : IsCompact X)
    (a : E → ℝ) : IsCompact (normalizedMaskCarrier X a) :=
  hX.prod ((isCompact_Icc.prod ((isCompact_sphere (0 : E) 1).inter_left
    (isClosed_tsupport a))).image (continuous_fst.smul continuous_snd))

/-- The closed unit collar produces the required normalized weight inequality
with equality. No normalized-cover hypothesis is used (`retarded-kernel`). -/
theorem mem_normalizedMaskCarrier_of_conicMask {X : Set (E × E)} (a : E → ℝ)
    {p : P} (hp : p ∈ X ×ˢ tsupport (conicMask a)) :
    (p.1, (1 + ‖p.2‖)⁻¹ • p.2) ∈ normalizedMaskCarrier X a := by
  have hs := conicMask_tsupport_subset a hp.2
  have hn : p.2 ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hs.1)
  have hr : 0 < 1 + ‖p.2‖ := by positivity
  refine ⟨hp.1, ⟨(‖p.2‖ / (1 + ‖p.2‖), NormedSpace.normalize p.2), ?_, ?_⟩⟩
  · refine ⟨⟨?_, ?_⟩, hs.2, ?_⟩
    · apply (le_div_iff₀ hr).mpr
      linarith [hs.1]
    · exact (div_le_one hr).mpr (by linarith)
    · simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hn
  · dsimp
    rw [div_eq_inv_mul, mul_smul, NormedSpace.norm_smul_normalize]

/-- The compact carrier excludes zero before any choice of derivative order
or shell radius (`app:ch_regular_base:setup:finite-calculus`). -/
theorem normalizedMaskCarrier_frequency_ne_zero (X : Set (E × E)) (a : E → ℝ)
    {p : P} (hp : p ∈ normalizedMaskCarrier X a) : p.2 ≠ 0 := by
  obtain ⟨⟨t, η⟩, ⟨ht, _, hη⟩, he⟩ := hp.2
  have hηn : ‖η‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hη
  rw [← he]
  exact smul_ne_zero (by linarith [ht.1] : t ≠ 0)
    (by intro hz; rw [hz, norm_zero] at hηn; norm_num at hηn : η ≠ 0)

/-- Construct the finite closed-ball cover used by the actual elapsed symbol
budgets. Its balls lie in the prescribed open normalized chart and avoid
zero, so every order of the fixed multiplier has a proved finite normalized
seminorm on every ball. The chart containment is geometric; no cover,
multiplier budget or operator estimate is assumed (`retarded-kernel`). -/
theorem exists_finite_conicMask_shell_cover
    {X : Set (E × E)} (hX : IsCompact X) {a : E → ℝ} (ha : ContDiff ℝ ∞ a)
    {U : Set P} (hU : IsOpen U) (hKU : normalizedMaskCarrier X a ⊆ U) :
    ∃ (s : Finset (normalizedMaskCarrier X a))
      (ρ : normalizedMaskCarrier X a → ℝ),
      (∀ p, 0 < ρ p) ∧
      (∀ p ∈ s, closedBall (p : P) (ρ p) ⊆ U) ∧
      (∀ p ∈ s, ∀ m, BoundedNormalizedSeminorm (closedBall (p : P) (ρ p)) m
        (fun z : P ↦ (conicMask a z.2 : ℂ))) ∧
      ∀ p ∈ X ×ˢ tsupport (fun ξ ↦ (conicMask a ξ : ℂ)),
        ∃ q ∈ s, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ closedBall (q : P) (ρ q),
          p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R := by
  classical
  let K := normalizedMaskCarrier X a
  let V : Set P := U ∩ {p | p.2 ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne.preimage continuous_snd)
  have hKV : K ⊆ V := fun p hp ↦
    ⟨hKU hp, normalizedMaskCarrier_frequency_ne_zero X a hp⟩
  have hball (p : K) : ∃ r > (0 : ℝ), closedBall (p : P) r ⊆ V := by
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hV p (hKV p.property)
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (by linarith : r / 2 < r)).trans hb⟩
  choose ρ hρ hρV using hball
  obtain ⟨s, hs⟩ := (isCompact_normalizedMaskCarrier hX a).elim_finite_subcover
    (fun p : K ↦ ball (p : P) (ρ p)) (fun _ ↦ isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (hρ ⟨p, hp⟩)⟩)
  refine ⟨s, ρ, hρ, fun p _ z hz ↦ (hρV p hz).1, ?_, ?_⟩
  · intro p _ m
    exact boundedNormalizedSeminorm_conicMask ha (isCompact_closedBall _ _)
      (fun z hz ↦ (hρV p hz).2) m
  · intro p hp
    have hv := mem_normalizedMaskCarrier_of_conicMask a
      ⟨hp.1, tsupport_comp_subset Complex.ofReal_zero (conicMask a) hp.2⟩
    obtain ⟨q, hq, hvq⟩ := mem_iUnion₂.mp (hs hv)
    refine ⟨q, hq, 1 + ‖p.2‖, by linarith [norm_nonneg p.2],
      (p.1, (1 + ‖p.2‖)⁻¹ • p.2), ball_subset_closedBall hvq, ?_, le_rfl⟩
    simp only [smul_inv_smul₀ (by positivity : (1 + ‖p.2‖) ≠ 0)]

end JanetCartan.RegularSector.FiniteMasks
