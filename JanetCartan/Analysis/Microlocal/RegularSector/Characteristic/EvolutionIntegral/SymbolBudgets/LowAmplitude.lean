module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Support
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.WeightedJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientJets

/-!
# The actual elapsed amplitude supplies the low source-symbol reserve

The finite normalized carrier cover is a geometric input. All weighted jets
are deduced from the original joint spatial symbol and fixed masks. The result
is exactly `HasFullSourceSymbolBound` at `fullLowReserve`, as consumed by
`PrimitiveRealization.Family`, and has no primitive operator bound.
Source: `app:ch_regular_base:lem:retarded-kernel` and actual-calculus Step 1.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles FirstOutputJets SourceExpansion FullLowBounds
variable {d q : ℕ} {ι : Type*} [Fintype ι]

/-- Spatial order `-o` controls spatial order zero at every radius `R≥1`.
This supplies the common low reserve for both branches of the retarded lemma. -/
theorem normalizedSeminorm_jointAmplitude_le_order
    (o j : ℕ) (J : Set (TwoTimePoint d)) (b : TwoTimeAmplitude d q)
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hbbound : BoundedTwoTimeOrderSeminorm o J j b) :
    BoundedNormalizedSeminorm J j (jointAmplitude b) ∧
      normalizedSeminorm J j (jointAmplitude b) ≤ twoTimeOrderSeminorm o J j b := by
  have hbound (R : {R : ℝ // 1 ≤ R}) :
      cNorm J j (PrimitiveProfiles.normalizedField R (jointAmplitude b)) ≤
        twoTimeOrderSeminorm o J j b := by
    have hf : ContDiff ℝ j (PrimitiveProfiles.normalizedField R (jointAmplitude b)) :=
      (hb.comp (contDiff_fst.prodMk (contDiff_snd.const_smul (R : ℝ)))).of_le (by simp)
    have he : cNorm J j (twoTimeOrderField o R b) =
        (R : ℝ) ^ o * cNorm J j (PrimitiveProfiles.normalizedField R (jointAmplitude b)) := by
      rw [twoTimeOrderField, cNorm_smul _ hf, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (zero_le_one.trans R.2) _)]
    have hpow : 1 ≤ (R : ℝ) ^ o := one_le_pow₀ R.2
    calc
      _ ≤ (R : ℝ) ^ o * cNorm J j (PrimitiveProfiles.normalizedField R (jointAmplitude b)) := by
        nlinarith [cNorm_nonneg J j (PrimitiveProfiles.normalizedField R (jointAmplitude b))]
      _ = cNorm J j (twoTimeOrderField o R b) := he.symm
      _ ≤ _ := cNorm_twoTimeOrderField_le hbbound R.2
  constructor
  · exact ⟨_, by rintro _ ⟨R, rfl⟩; exact hbound R⟩
  · apply Real.sSup_le _ (twoTimeOrderSeminorm_nonneg _ _ _ _)
    rintro _ ⟨R, rfl⟩
    exact hbound R

/-- Fixed carrier coverage turns the constructed normalized budgets into
the global source-symbol bound. The bound is linear in the original symbol
at the same derivative order, uniformly in elapsed time under the fixed
chart inclusion. No weighted elapsed jet estimate is assumed. -/
theorem hasFullSourceSymbolBound_elapsedAmplitude
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) {F : Set (Euclidean d)} (hF : IsClosed F)
    (hcover : ∀ p ∈ amplitudeCarrier χout χsource β F,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (o N : ℕ)
    (hβbound : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) N (jointMultiplier β))
    (b : TwoTimeAmplitude d q) (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hbsupport : ∀ t s y η, η ∉ F → b t s y η = 0)
    (hbbound : BoundedTwoTimeOrderSeminorm o J N b)
    (r : ℝ) (hmap : ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J) :
    HasFullSourceSymbolBound (elapsedAmplitude b χout χsource β r) N
      ((∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i)) N χout χsource β) *
        twoTimeOrderSeminorm o J N b) := by
  classical
  let A := elapsedAmplitude b χout χsource β r
  let B := (∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i)) N χout χsource β) *
    twoTimeOrderSeminorm o J N b
  have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg fun i _ ↦
    amplitudeMaskConstant_nonneg _ _ _ _ _) (twoTimeOrderSeminorm_nonneg _ _ _ _)
  have hA : ContDiff ℝ ∞ (uncurry A) :=
    contDiff_uncurry_elapsedAmplitude b χout χsource β hb hχout hχsource hβ r
  have hA' : ContDiff ℝ ∞ (fun p : Euclidean (d + 1) × Euclidean (d + 1) × Euclidean (d + 1) ↦
      A p.1 p.2.1 p.2.2) :=
    hA.comp ((contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
      (contDiff_snd.comp contDiff_snd))
  have hb0 := normalizedSeminorm_jointAmplitude_le_order o N J b hb hbbound
  have hlocal (i : ι) := elapsedAmplitude_normalizedSeminorm_le
    (isCompact_closedBall (z i) (δ i)) hJ hU hJU
    (V := univ) (fun _ _ _ _ ↦ mem_univ _) N r b χout χsource β
    hχout hχsource hβ (hβbound i) hb.contDiffOn hb0.1 (hmap i)
  have hbudget (i : ι) : normalizedSeminorm (Metric.closedBall (z i) (δ i)) N (uncurry A) ≤ B := by
    apply (hlocal i).2.trans
    exact mul_le_mul
      (Finset.single_le_sum (fun k _ ↦ amplitudeMaskConstant_nonneg
        (Metric.closedBall (z k) (δ k)) N χout χsource β) (Finset.mem_univ i))
      hb0.2 (normalizedSeminorm_nonneg _ _ _)
      (Finset.sum_nonneg fun k _ ↦ amplitudeMaskConstant_nonneg _ _ _ _ _)
  have hweighted : ∀ w : List (Coordinate (d + 1)), w.length ≤ N → ∀ x y η,
      (1 + ‖η‖) ^ frequencyOrder w * ‖jet w A x y η‖ ≤ B := by
    intro w hw x y η
    by_cases hz : jet w A x y η = 0
    · simpa only [hz, norm_zero, mul_zero] using hB
    have hp := tsupport_elapsedAmplitude_subset b χout χsource β hF hbsupport r
      (tsupport_jet_subset w A (subset_tsupport (uncurry (jet w A))
        (show ((x, y), η) ∈ Function.support (uncurry (jet w A)) from hz)))
    obtain ⟨i, R, hR, v, hv, he, hweight⟩ := hcover ((x, y), η) hp
    have hj := weighted_jet_le_normalizedSeminorm (z i) isOpen_univ isOpen_univ
      (subset_univ _) hA.contDiffOn
      (fun R _ ↦ (hA.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).contDiffOn)
      w ((hlocal i).1.mono hw) hR v hv (mem_univ _)
    have hj' : R ^ frequencyOrder w * ‖jet w A x y η‖ ≤
        normalizedSeminorm (Metric.closedBall (z i) (δ i)) w.length (uncurry A) := by
      change R ^ frequencyOrder w * ‖uncurry (jet w A) (v.1, R • v.2)‖ ≤ _ at hj
      rw [← he] at hj
      exact hj
    calc
      _ ≤ R ^ frequencyOrder w * ‖jet w A x y η‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hweight _) (norm_nonneg _)
      _ ≤ _ := hj'
      _ ≤ normalizedSeminorm (Metric.closedBall (z i) (δ i)) N (uncurry A) :=
        normalizedSeminorm_mono (hlocal i).1 hw
      _ ≤ _ := hbudget i
  simpa only [one_pow, one_mul] using hasFullSourceSymbolBound_of_weighted_jets
    hA' N (fun η ↦ 1 + ‖η‖) (c := 1) le_rfl hB (fun _ ↦ by simp) hweighted

/-- A primitive low-bounded family supplies the exact fixed reserve of
`PrimitiveRealization.Family`, uniformly for elapsed time in the whole slab.
The constant is chosen before the amplitude, its order, and its low budget.
The original amplitude includes its low-frequency cutoff and lower-end buffer;
all masks remain inside the source-symbol derivatives. -/
theorem exists_elapsed_fullLowReserve_constant
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) {F : Set (Euclidean d)} (hF : IsClosed F)
    (hcover : ∀ p ∈ amplitudeCarrier χout χsource β F,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (hβbound : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1)) (jointMultiplier β))
    (Δ : ℝ)
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (o : ℕ) (M : ℝ) (b : TwoTimeAmplitude d q),
      ContDiff ℝ ∞ (jointAmplitude b) →
      (∀ t s y η, η ∉ F → b t s y η = 0) →
      BoundedTwoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b →
      twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b ≤ M →
      ∀ r ∈ Icc 0 Δ, HasFullSourceSymbolBound (elapsedAmplitude b χout χsource β r)
        (fullLowReserve (d + 1)) (C * M) := by
  classical
  let ca := ∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i))
    (fullLowReserve (d + 1)) χout χsource β
  have hca : 0 ≤ ca := Finset.sum_nonneg fun _ _ ↦ amplitudeMaskConstant_nonneg _ _ _ _ _
  refine ⟨1 + ca, by linarith, ?_⟩
  intro o M b hb hbsupport hbbound hM r hr
  have h := hasFullSourceSymbolBound_elapsedAmplitude z δ hJ hU hJU χout χsource β
    hχout hχsource hβ hF hcover o (fullLowReserve (d + 1)) hβbound b hb hbsupport
    hbbound r (hmap r hr)
  have hM0 := (twoTimeOrderSeminorm_nonneg o J (fullLowReserve (d + 1)) b).trans hM
  intro is js hij x y η
  apply (h is js hij x y η).trans
  change ca * twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b ≤ (1 + ca) * M
  have := mul_le_mul_of_nonneg_left hM hca
  nlinarith

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
