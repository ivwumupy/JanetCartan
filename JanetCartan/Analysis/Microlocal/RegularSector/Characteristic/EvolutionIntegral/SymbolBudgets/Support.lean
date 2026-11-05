module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude

/-!
# Closed carriers and smoothness of the actual elapsed amplitude

The lower-frequency cutoff of the original spatial symbol and both physical
masks remain in the actual full amplitude of the fixed-time representation.
The multiplier cone controls every nonzero differentiated amplitude, not just
its values. Source: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles
variable {d q : ℕ}

/-- A fixed closed carrier retaining both masks, the conic multiplier and the
original spatial frequency cutoff (`fixed-time-representation`). -/
def amplitudeCarrier (χout χsource β : Euclidean (d + 1) → ℂ)
    (F : Set (Euclidean d)) : Set (Point (d + 1)) :=
  (tsupport χout ×ˢ tsupport χsource) ×ˢ (tsupport β ∩ spatialPart ⁻¹' F)

/-- The fixed carrier is closed, so it controls all joint derivatives. -/
theorem isClosed_amplitudeCarrier (χout χsource β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F) :
    IsClosed (amplitudeCarrier χout χsource β F) :=
  ((isClosed_tsupport _).prod (isClosed_tsupport _)).prod
    ((isClosed_tsupport _).inter (hF.preimage (spatialProjection (d := d)).continuous))

/-- Primitive spatial support and the fixed masks prove the closed support
of the actual elapsed amplitude, uniformly in elapsed time. -/
theorem tsupport_elapsedAmplitude_subset
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0) (r : ℝ) :
    tsupport (uncurry (elapsedAmplitude b χout χsource β r)) ⊆
      amplitudeCarrier χout χsource β F := by
  apply closure_minimal _ (isClosed_amplitudeCarrier χout χsource β hF)
  intro p hp
  have hm : χout p.1.1 ≠ 0 ∧ χsource p.1.2 ≠ 0 ∧ β p.2 ≠ 0 := by
    constructor
    · intro hz
      exact hp (elapsedAmplitude_eq_zero_of_mask b χout χsource β r _ _ _ (Or.inl hz))
    constructor
    · intro hz
      exact hp (elapsedAmplitude_eq_zero_of_mask b χout χsource β r _ _ _ (Or.inr (Or.inl hz)))
    · intro hz
      exact hp (elapsedAmplitude_eq_zero_of_mask b χout χsource β r _ _ _ (Or.inr (Or.inr hz)))
  refine ⟨⟨subset_tsupport χout hm.1, subset_tsupport χsource hm.2.1⟩,
    subset_tsupport β hm.2.2, ?_⟩
  by_contra hη
  exact hp (by simp [uncurry, elapsedAmplitude, hb _ _ _ _ hη])

/-- Ordinary smoothness of the cutoff original symbol produces ordinary
smoothness of the actual full amplitude. This supplies the low source-series
constructor; no smoothness of an operator is assumed. -/
theorem contDiff_uncurry_elapsedAmplitude
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (r : ℝ) :
    ContDiff ℝ ∞ (uncurry (elapsedAmplitude b χout χsource β r)) := by
  have hM : ContDiff ℝ ∞ (physicalMasks χout χsource) :=
    (hχout.comp (contDiff_fst.comp contDiff_fst)).mul
      (hχsource.comp (contDiff_snd.comp contDiff_fst))
  have hB : ContDiff ℝ ∞ (jointMultiplier β) := hβ.comp contDiff_snd
  have hE : ContDiff ℝ ∞ (elapsedPoint (d := d) r) :=
    elapsedLinear.contDiff.add contDiff_const
  have he : uncurry (elapsedAmplitude b χout χsource β r) =
      fun p ↦ physicalMasks χout χsource p • (jointMultiplier β p •
        jointAmplitude b (elapsedPoint r p)) := by
    funext p
    simp [uncurry, elapsedAmplitude, physicalMasks, jointMultiplier, jointAmplitude, mul_smul]
  rw [he]
  exact hM.smul (hB.smul (hb.comp hE))

/-- The lower-end buffer is retained by every differentiated elapsed
amplitude in its open vanishing region. Source: the retarded lemma's
zero extension below the initial time. -/
theorem elapsedAmplitude_jet_eq_zero_below_buffer
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (a r : ℝ) (hb : ∀ t s y η, s ≤ a → b t s y η = 0)
    (w : List (Coordinate (d + 1))) (p : Point (d + 1)) (hp : p.1.1 0 - r < a) :
    uncurry (jet w (elapsedAmplitude b χout χsource β r)) p = 0 := by
  have hopen : IsOpen {p : Point (d + 1) | p.1.1 0 - r < a} :=
    isOpen_lt (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).continuous.comp
      (continuous_fst.comp continuous_fst)).sub continuous_const) continuous_const
  have he : uncurry (elapsedAmplitude b χout χsource β r) =ᶠ[nhds p] 0 := by
    filter_upwards [hopen.mem_nhds hp] with v hv
    exact elapsedAmplitude_eq_zero_of_lower_buffer b χout χsource β a r hb _ _ _ hv.le
  have hn : p ∉ tsupport (uncurry (elapsedAmplitude b χout χsource β r)) :=
    notMem_tsupport_iff_eventuallyEq.mpr he
  exact image_eq_zero_of_notMem_tsupport (fun h ↦ hn (tsupport_jet_subset w _ h))

/-- Every nonzero joint jet lies in the multiplier cone. Thus the spatial
order-minus-one comparison applies to differentiated amplitudes as required
by the retarded lemma, not only to undifferentiated values. -/
theorem elapsedAmplitude_jet_bracket_comparison
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ C * ‖spatialPart ξ‖)
    (r : ℝ) (w : List (Coordinate (d + 1))) (p : Point (d + 1))
    (hp : uncurry (jet w (elapsedAmplitude b χout χsource β r)) p ≠ 0) :
    (1 + ‖spatialPart p.2‖)⁻¹ ≤ (C + 1) / (1 + ‖p.2‖) := by
  have hc := tsupport_elapsedAmplitude_subset b χout χsource β hF hb r
    (tsupport_jet_subset w _ (subset_tsupport _ hp))
  exact inv_spatial_bracket_le_of_cone hC (hcone p.2 hc.2.1)

/-- The multiplier cone turns a normalized spacetime annulus into a spatial
annulus with fixed positive inner radius. This is the geometric reason the
original spatial order-minus-one normalization suffices in the preceding
amplitude profile theorem. The assertion applies at every physical dilation. -/
theorem spatial_annulus_of_normalized_multiplier_cone
    (β : Euclidean (d + 1) → ℂ) {C a b R : ℝ} (hC : 0 ≤ C)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ C * ‖spatialPart ξ‖)
    (hR : 0 < R) (u : Euclidean (d + 1)) (hu : R • u ∈ tsupport β)
    (ha : a ≤ ‖u‖) (hb : ‖u‖ ≤ b) :
    a / (C + 1) ≤ ‖spatialPart u‖ ∧ ‖spatialPart u‖ ≤ b := by
  have hc := hcone (R • u) hu
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, spatialPart_smul,
    norm_smul, Real.norm_eq_abs, abs_of_pos hR] at hc
  have hc' : |u 0| ≤ C * ‖spatialPart u‖ := by nlinarith
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
    nlinarith [norm_le_spatial_of_cone hc']
  · exact (norm_spatialPart_le u).trans hb

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
