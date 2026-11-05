module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.NestedMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude

/-!
# Finite normalized graph cover on the retained section

Both physical supports and the angular carrier are fixed geometric inputs.
Compactness supplies a positive section band, then the literal dilated-mask
cover supplies every multiplier budget and both normalization inequalities.
The same balls have all their elapsed images in the explicit joint jet set.
Consumer: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase EvolutionIntegral FiniteMasks FourierIntegral PrimitiveProfiles
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "P" => (E × E) × E

/-- The actual radially invariant open graph chart, with the source physical
position left unrestricted. The latter still belongs to the original compact
source mask in the normalized carrier (`retarded-kernel`). -/
def retainedGraphDomain (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε : ℝ) : Set P :=
  {p | p.1.1 ∈ elapsedPhysicalBox z (ε / 2) ∧
    spatialPart p.2 ∈ angularCone ℓ z.2.2 (ε / 2)}

/-- Openness of the SAME chart used for every ball (`retarded-kernel`). -/
theorem isOpen_retainedGraphDomain (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε : ℝ) :
    IsOpen (retainedGraphDomain ℓ z ε) :=
  ((isOpen_elapsedPhysicalBox z (ε / 2)).preimage continuous_fst.fst).inter
    ((isOpen_angularCone ℓ z.2.2 (ε / 2)).preimage
      (spatialPartCLM.continuous.comp continuous_snd))

/-- The whole graph chart stays on the SAME cone after every positive
frequency dilation (`fixed-time-representation`). -/
theorem smul_mem_retainedGraphDomain (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε : ℝ)
    {p : P} (hp : p ∈ retainedGraphDomain ℓ z ε) {t : ℝ} (ht : 0 < t) :
    (p.1, t • p.2) ∈ retainedGraphDomain ℓ z ε := by
  exact ⟨hp.1, by simpa only [SymbolBudgets.spatialPart_smul] using
    smul_mem_angularCone hp.2 ht⟩

/-- The fixed normalized carrier lies in the actual graph chart. This is a
deduction from the physical supports and angular carrier, not a presumed graph
realization (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem normalizedMaskCarrier_subset_retainedGraphDomain
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε : ℝ)
    {X : Set (E × E)} (hX : ∀ x ∈ X, x.1 ∈ elapsedPhysicalBox z (ε / 2))
    (b : E → ℝ)
    (hb : ∀ ξ ∈ tsupport b ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2)) :
    normalizedMaskCarrier X b ⊆ retainedGraphDomain ℓ z ε := by
  rintro p ⟨hx, ⟨⟨t, ξ⟩, ⟨ht, hξ⟩, he⟩⟩
  refine ⟨hX p.1 hx, ?_⟩
  rw [← he, SymbolBudgets.spatialPart_smul]
  exact smul_mem_angularCone (hb ξ hξ) (by linarith [ht.1])

/-- Every elapsed image of the actual chart's bounded section band lies in
the literal buffered joint set. The source physical coordinate plays no role
in the elapsed map; it is retained in the finite cover (`retarded-kernel`). -/
theorem retainedGraphDomain_elapsed_mem_bufferedJetSet
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε a b r : ℝ} (hε : 0 < ε)
    (hr : r ∈ Icc 0 ε) {p : P} (hp : p ∈ retainedGraphDomain ℓ z ε)
    (hband : ℓ (spatialPart p.2) ∈ Icc a b) :
    SymbolBudgets.elapsedPoint r p ∈ bufferedJetSet ℓ z ε a b := by
  have hx : p.1.1 ∈ elapsedPhysicalBox z ε :=
    ⟨ball_subset_ball (by linarith) hp.1.1, ball_subset_ball (by linarith) hp.1.2⟩
  have hη : (ℓ (spatialPart p.2))⁻¹ • spatialPart p.2 ∈ ball z.2.2 ε :=
    ball_subset_ball (by linarith) hp.2.2
  have ht := elapsedPoint_mem_twoTime_buffer hε hr hx hη
  have ht' : dist (p.1.1 0) z.1 ≤ 2 * ε ∧
      dist (p.1.1 0 - r) z.1 ≤ 2 * ε ∧ dist (spatialPart p.1.1) z.2.1 ≤ 2 * ε := by
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
  rw [SymbolBudgets.elapsedPoint_eq]
  refine ⟨ht', (ℓ (spatialPart p.2), (ℓ (spatialPart p.2))⁻¹ • spatialPart p.2),
    ⟨hband, ball_subset_closedBall hη, ?_⟩, smul_inv_smul₀ hp.2.1.ne' _⟩
  change ℓ ((ℓ (spatialPart p.2))⁻¹ • spatialPart p.2) = 1
  simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.2.1.ne']

/-- Construct the finite normalized cover, its radial section band, and all
elapsed-image inclusions on the SAME right multiplier, uniformly in every
larger radial threshold. `X` is the product of the original physical supports;
the parent supplies its compactness and placement in the retained box.
No finite graph estimate is an input (`fixed-time-representation`). -/
theorem exists_retained_finite_shell_cover
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε : ℝ} (hε : 0 < ε)
    {X : Set (E × E)} (hXc : IsCompact X)
    (hX : ∀ x ∈ X, x.1 ∈ elapsedPhysicalBox z (ε / 2))
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b)
    (hcarrier : ∀ ξ ∈ tsupport b ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2)) :
    ∃ ra > (0 : ℝ), ∃ rb > ra,
    ∃ (s : Finset (normalizedMaskCarrier X b)) (δ : normalizedMaskCarrier X b → ℝ),
      (∀ p, 0 < δ p) ∧
      (∀ p ∈ s, closedBall (p : P) (δ p) ⊆ retainedGraphDomain ℓ z ε) ∧
      (∀ r ∈ Icc 0 ε, ∀ p ∈ s,
        MapsTo (SymbolBudgets.elapsedPoint r) (closedBall (p : P) (δ p))
          (bufferedJetSet ℓ z ε ra rb)) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p ∈ s, ∀ m,
        BoundedNormalizedSeminorm (closedBall (p : P) (δ p)) m
          (SymbolBudgets.jointMultiplier (fun ξ ↦ (dilatedConicMask b L ξ : ℂ)))) ∧
      ∀ L : ℝ, 1 ≤ L →
        ∀ p ∈ X ×ˢ tsupport (fun ξ ↦ (dilatedConicMask b L ξ : ℂ)),
          ∃ q ∈ s, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ closedBall (q : P) (δ q),
            p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t ∧ t ≤ 1 * (1 + ‖p.2‖) := by
  have hK := isCompact_normalizedMaskCarrier hXc b
  have hKG := normalizedMaskCarrier_subset_retainedGraphDomain ℓ z ε hX b hcarrier
  let f : P → ℝ := fun p ↦ ℓ (spatialPart p.2)
  have hf : Continuous f := ℓ.continuous.comp (spatialPartCLM.continuous.comp continuous_snd)
  obtain ⟨a, ha, hamin⟩ := hK.exists_forall_le' hf.continuousOn
    (fun p hp ↦ (hKG hp).2.1)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  let rb := |B| + a + 1
  have hrb : a / 2 < rb := by dsimp [rb]; linarith [abs_nonneg B]
  let U := retainedGraphDomain ℓ z ε ∩ f ⁻¹' Ioo (a / 2) rb
  have hU : IsOpen U := (isOpen_retainedGraphDomain ℓ z ε).inter (isOpen_Ioo.preimage hf)
  have hKU : normalizedMaskCarrier X b ⊆ U := by
    intro p hp
    refine ⟨hKG hp, ?_, ?_⟩
    · have := hamin p hp; linarith
    · have h := hB p hp
      rw [Real.norm_eq_abs] at h
      dsimp [rb]
      linarith [le_abs_self (f p), le_abs_self B]
  obtain ⟨s, δ, hδ, hball, hbound, hcover⟩ :=
    exists_finite_dilatedConicMask_shell_cover hXc hb hU hKU
  refine ⟨a / 2, half_pos ha, rb, hrb, s, δ, hδ,
    fun p hp v hv ↦ (hball p hp hv).1, ?_, hbound, hcover⟩
  intro r hr p hp v hv
  have h := hball p hp hv
  exact retainedGraphDomain_elapsed_mem_bufferedJetSet ℓ z hε hr h.1
    ⟨h.2.1.le, h.2.2.le⟩

end JanetCartan.RegularSector.Characteristic.UniformEvolution
