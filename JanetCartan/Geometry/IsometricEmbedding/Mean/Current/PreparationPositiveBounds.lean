module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationDiscrepancyBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.PositiveAmplitude

/-!
# Positive-density bounds for the actual colored discrepancy

The square-root estimate and the concrete carrier-integral estimate close the
nonlinear part of `app:ch_mean_pairs:eq:mean-density-lipschitz`. Only the
original linear atom bounds and joint extensions remain primitive inputs.
Unlike a realization interface, the conclusion concerns the literal integral;
its Sobolev realization and integrability estimates have already been proved.
Constants precede the coloring and the small current/transport error.
-/

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow SmoothPeriodicFamily

variable {n N : ℕ} {A κ : Type*} [AddCommGroup A] [Module ℝ A] [Fintype κ]

/-- For the literal measured carrier integral, derive both the initial
`O(δ)` error and the positive-density Lipschitz bound, where `δ = λ⁻¹` in
preparation. The fixed compact initial domain and input order `j` are those
of the original current-atom estimate. Every output is the same integral
identified by `preparationAtomDiscrepancy_eq_colored`; no desired discrepancy
bound or Sobolev realization identity is assumed
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem exists_preparationAtom_positiveDensity_bounds
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (χ : CarrierParameter → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (I : A →ₗ[ℝ] (CarrierVariable n → ℝ))
    {initial : Set (CarrierVariable n)} (hi : IsCompact initial) (j s : ℕ)
    (r : CarrierVariable n → ℝ) (hr : ContDiff ℝ j r)
    {M L R ρ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hχM : ∀ z, |χ z| ≤ M) (hrR : cNorm initial j r ≤ R) :
    ∃ D : ℝ, 0 < D ∧ ∀ (mask : κ → CarrierParameter → ℝ),
      (∀ c, Measurable (mask c)) → (∀ c z, 0 ≤ mask c z) → (∀ z, ∑ c, mask c z = 1) →
      ∀ (δ : ℝ), 0 ≤ δ →
      ∀ U T : κ → CarrierParameter → A →ₗ[ℝ]
        SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ),
      (∀ a c, Continuous (fun p : Torus n × CarrierParameter ↦ (U c p.2 a).val p.1 ())) →
      (∀ a c, Continuous (fun p : Torus n × CarrierParameter ↦ (T c p.2 a).val p.1 ())) →
      (∀ a c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
        (U c p.2 a).val (torusQuotient p.1) ())) →
      (∀ a c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
        (T c p.2 a).val (torusQuotient p.1) ())) →
      (∀ c z a, componentCSeminorm s () (U c z a) ≤ L * cNorm initial j (I a)) →
      (∀ c z a, componentCSeminorm s () (T c z a) ≤ L * cNorm initial j (I a)) →
      (∀ c z a, componentCSeminorm s () ((U c z - T c z) a) ≤
        δ * L * cNorm initial j (I a)) →
      (∀ a₀, I a₀ = r → periodicSobolevNorm s (preparationAtomDiscrepancy C χ U T mask a₀) ≤ D * δ) ∧
      ∀ (v w : CarrierVariable n → ℝ) (a b : A),
        ContDiff ℝ j v → ContDiff ℝ j w →
        cNorm initial j v ≤ ρ → cNorm initial j w ≤ ρ →
        (∀ x, 0 < 1 + v x) → (∀ x, 0 < 1 + w x) →
        (∀ x ∈ initial, 1 + v x ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        (∀ x ∈ initial, 1 + w x ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        I a = (fun x ↦ positiveDensityAmplitude (r x) (v x)) →
        I b = (fun x ↦ positiveDensityAmplitude (r x) (w x)) →
        periodicSobolevNorm s
          (preparationAtomDiscrepancy C χ U T mask a - preparationAtomDiscrepancy C χ U T mask b) ≤
          D * δ * cNorm initial j (v - w) := by
  obtain ⟨B, hB, hb⟩ := DensityDiscrepancy.exists_positiveAmplitude_cNorm_bounds hi j hρ hR
  let H := (2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)
  have hH : 0 ≤ H := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  let W := sobolevPeriodicJetConstant n s * (s + 1 : ℕ) *
    (M ^ 2 * (2 * H * L ^ 2)) * (volume.prod volume : Measure CarrierParameter).real (tsupport χ)
  have hW : 0 ≤ W := by
    have := (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s))
    have : 0 ≤ (volume.prod volume : Measure CarrierParameter).real (tsupport χ) := ENNReal.toReal_nonneg
    dsimp [W]
    positivity
  let D₀ := W * R ^ 2
  let D₁ := W * (2 * (R + B * ρ)) * B
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  refine ⟨1 + D₀ + D₁, by positivity, ?_⟩
  intro mask hm hm0 hmask δ hδ U T hUc hTc hU hT hUb hTb hDb
  let p := fun a : A ↦ cNorm initial j (I a)
  have hp (a : A) : 0 ≤ p a := cNorm_nonneg _ _ _
  have habs (a : A) : periodicSobolevNorm s (preparationAtomDiscrepancy C χ U T mask a) ≤
      W * δ * p a ^ 2 := by
    convert periodicSobolevNorm_preparationAtomDiscrepancy_le C hC χ hχ hχc U T
      hUc hTc hU hT mask hm hm0 hmask s p hp hM hL hδ hχM hUb hTb hDb a using 1
    dsimp [W, H]
    ring
  have hdiff (a b : A) : periodicSobolevNorm s
      (preparationAtomDiscrepancy C χ U T mask a - preparationAtomDiscrepancy C χ U T mask b) ≤
      W * δ * (p a + p b) * p (a - b) := by
    convert periodicSobolevNorm_preparationAtomDiscrepancy_sub_le C hC χ hχ hχc U T
      hUc hTc hU hT mask hm hm0 hmask s p hp hM hL hδ hχM hUb hTb hDb a b using 1
    dsimp [W, H]
    ring
  constructor
  · intro a₀ ha₀
    have hpa : p a₀ ≤ R := by simpa only [p, ha₀] using hrR
    calc
      _ ≤ W * δ * p a₀ ^ 2 := habs a₀
      _ ≤ W * δ * R ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hp a₀) hpa 2) (mul_nonneg hW hδ)
      _ = D₀ * δ := by dsimp [D₀]; ring
      _ ≤ (1 + D₀ + D₁) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
  · intro v w a b hv hw hvρ hwρ hvpos hwpos hvi hwi ha hb'
    obtain ⟨hva, hwb, hvw⟩ := hb r v w hr hv hw hrR hvρ hwρ hvpos hwpos hvi hwi
    have hpa : p a ≤ R + B * ρ := by simpa only [p, ha] using hva
    have hpb : p b ≤ R + B * ρ := by simpa only [p, hb'] using hwb
    have hpab : p (a - b) ≤ B * cNorm initial j (v - w) := by
      simpa only [p, map_sub, ha, hb', Pi.sub_def] using hvw
    calc
      _ ≤ W * δ * (p a + p b) * p (a-b) := hdiff a b
      _ ≤ W * δ * ((R + B * ρ) + (R + B * ρ)) * (B * cNorm initial j (v - w)) := by
        apply mul_le_mul _ hpab (hp _) (by positivity)
        exact mul_le_mul_of_nonneg_left (add_le_add hpa hpb) (mul_nonneg hW hδ)
      _ = D₁ * δ * cNorm initial j (v - w) := by dsimp [D₁]; ring
      _ ≤ (1 + D₀ + D₁) * δ * cNorm initial j (v - w) := by
        apply mul_le_mul_of_nonneg_right _ (cNorm_nonneg _ _ _)
        exact mul_le_mul_of_nonneg_right (by linarith) hδ

end JanetCartan.CurrentMean
