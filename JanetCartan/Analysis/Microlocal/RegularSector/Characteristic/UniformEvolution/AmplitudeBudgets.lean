module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhaseBudgets

/-!
# Low budgets for the literal solver sum and residual

The same-witness producer is
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`: its
`j = 0, 1, 2` conclusions give the three smooth amplitudes and their finite
normalized budgets. Here the correction's order-minus-one budget is converted
to order zero before adding it to the leading amplitude. The fixed original
coefficient order from `PhaseBudgets` supplies both low inputs.

Consumers: `E_(W₀+W₁)Bβ` and `E_(PW₁)Bβ` in
`app:ch_regular_base:lem:retarded-kernel` and `energy-complete-residual`.
These are deductions from the published amplitude outputs, not an operator
existence assumption or a completion of the retarded construction.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open FourierIntegral EvolutionIntegral SymbolBudgets PrimitiveProfiles FullLowBounds
variable {d q : ℕ}

private theorem contDiff_twoTimeOrderField {W : TwoTimeAmplitude d q}
    (hW : ContDiff ℝ ∞ (jointAmplitude W)) (o : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (twoTimeOrderField o R W) := by
  change ContDiff ℝ ∞ (fun p : SymbolBudgets.TwoTimePoint d ↦
    R ^ o • jointAmplitude W (p.1, R • p.2))
  exact (hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).const_smul (R ^ o)

/-- The correction's order-minus-one budget controls its order-zero budget.
The radial normalization is unchanged, including every radius `R ≥ 1`
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem correction_order_zero_bound {J : Set (SymbolBudgets.TwoTimePoint d)} {m : ℕ}
    {W₁ : TwoTimeAmplitude d q} (hW₁ : ContDiff ℝ ∞ (jointAmplitude W₁))
    (hfinite : BoundedTwoTimeOrderSeminorm 1 J m W₁) :
    BoundedTwoTimeOrderSeminorm 0 J m W₁ ∧
      twoTimeOrderSeminorm 0 J m W₁ ≤ twoTimeOrderSeminorm 1 J m W₁ := by
  have hbound (R : ℝ) (hR : 1 ≤ R) :
      cNorm J m (twoTimeOrderField 0 R W₁) ≤ twoTimeOrderSeminorm 1 J m W₁ := by
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have he : twoTimeOrderField 0 R W₁ = R⁻¹ • twoTimeOrderField 1 R W₁ := by
      simp only [twoTimeOrderField, pow_zero, pow_one, one_smul, smul_smul,
        inv_mul_cancel₀ hRpos.ne']
    rw [he, cNorm_smul R⁻¹ ((contDiff_twoTimeOrderField hW₁ 1 R).of_le (by simp))]
    calc
      _ ≤ 1 * cNorm J m (twoTimeOrderField 1 R W₁) :=
        mul_le_mul_of_nonneg_right (by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
          exact (inv_le_one₀ hRpos).mpr hR) (cNorm_nonneg _ _ _)
      _ ≤ _ := by simpa only [one_mul] using cNorm_twoTimeOrderField_le hfinite hR
  refine ⟨⟨twoTimeOrderSeminorm 1 J m W₁, ?_⟩, ?_⟩
  · rintro _ ⟨R, rfl⟩
    exact hbound R R.2
  · exact Real.sSup_le (by rintro _ ⟨R, rfl⟩; exact hbound R R.2)
      (twoTimeOrderSeminorm_nonneg _ _ _ _)

/-- The literal solver sum has a finite order-zero budget bounded by the sum
of the producer's leading and correction budgets. No new amplitude is chosen
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem solver_order_zero_bound {J : Set (SymbolBudgets.TwoTimePoint d)}
    (hJ : IsCompact J) {m : ℕ} {W₀ W₁ : TwoTimeAmplitude d q}
    (hW₀ : ContDiff ℝ ∞ (jointAmplitude W₀))
    (hW₁ : ContDiff ℝ ∞ (jointAmplitude W₁))
    (hf₀ : BoundedTwoTimeOrderSeminorm 0 J m W₀)
    (hf₁ : BoundedTwoTimeOrderSeminorm 1 J m W₁) :
    BoundedTwoTimeOrderSeminorm 0 J m (W₀ + W₁) ∧
      twoTimeOrderSeminorm 0 J m (W₀ + W₁) ≤
        twoTimeOrderSeminorm 0 J m W₀ + twoTimeOrderSeminorm 1 J m W₁ := by
  obtain ⟨hf₁', h₁⟩ := correction_order_zero_bound hW₁ hf₁
  have hbound (R : ℝ) (hR : 1 ≤ R) :
      cNorm J m (twoTimeOrderField 0 R (W₀ + W₁)) ≤
        twoTimeOrderSeminorm 0 J m W₀ + twoTimeOrderSeminorm 1 J m W₁ := by
    have he : twoTimeOrderField 0 R (W₀ + W₁) =
        twoTimeOrderField 0 R W₀ + twoTimeOrderField 0 R W₁ := by
      ext p i j
      simp [twoTimeOrderField, normalizedField, jointAmplitude]
    rw [he]
    exact (cNorm_add_le hJ ((contDiff_twoTimeOrderField hW₀ 0 R).of_le (by simp))
      ((contDiff_twoTimeOrderField hW₁ 0 R).of_le (by simp))).trans
        (add_le_add (cNorm_twoTimeOrderField_le hf₀ hR)
          ((cNorm_twoTimeOrderField_le hf₁' hR).trans h₁))
  refine ⟨⟨twoTimeOrderSeminorm 0 J m W₀ + twoTimeOrderSeminorm 1 J m W₁, ?_⟩, ?_⟩
  · rintro _ ⟨R, rfl⟩
    exact hbound R R.2
  · exact Real.sSup_le (by rintro _ ⟨R, rfl⟩; exact hbound R R.2)
      (add_nonneg (twoTimeOrderSeminorm_nonneg _ _ _ _) (twoTimeOrderSeminorm_nonneg _ _ _ _))

/-- Fixed original `Q,B` norms supply each primitive low amplitude budget.
`hbudget` is precisely the order-zero/order-minus-one estimate retained by
`ConicConstruction`, with its original shifts ten and nine. -/
theorem retained_amplitude_low_bound
    (KQ : Set (Euclidean (d + 1)))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    {J : Set (SymbolBudgets.TwoTimePoint d)} {W : TwoTimeAmplitude d q}
    {o : ℕ} (ho : o = 0 ∨ o = 1) (D : ℕ → ℝ) (hD : ∀ m, 0 < D m)
    (hbudget : ∀ m, twoTimeOrderSeminorm o J m W ≤
      D m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B))
    {M : ℝ} (hQ : cNorm KQ (retardedCoefficientOrder d) Q ≤ M)
    (hB : cNorm KQ (retardedCoefficientOrder d) B ≤ M) :
    twoTimeOrderSeminorm o J (fullLowReserve (d + 1) + o) W ≤
      D (fullLowReserve (d + 1) + o) * (1 + 2 * M) := by
  apply (hbudget _).trans
  apply mul_le_mul_of_nonneg_left _ (hD _).le
  have hQ' := (cNorm_mono_order (retardedCoefficientOrder_bounds ho).2.2.1).trans hQ
  have hB' : cNorm KQ (fullLowReserve (d + 1) + o + 9) B ≤ M :=
    (cNorm_mono_order (show fullLowReserve (d + 1) + o + 9 ≤ retardedCoefficientOrder d
      by have := (retardedCoefficientOrder_bounds (d := d) ho).2.2.1; omega)).trans hB
  linarith

/-- The actual sum inherits one additive original coefficient budget at every
order. The coefficient shift stays ten in `Q` and nine in `B`; the factor two
comes only from adding the two retained amplitudes (`retarded-kernel`). -/
theorem solver_coefficient_bound
    (KQ : Set (Euclidean (d + 1)))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    {J : Set (SymbolBudgets.TwoTimePoint d)} (hJ : IsCompact J)
    {W₀ W₁ : TwoTimeAmplitude d q}
    (hW₀ : ContDiff ℝ ∞ (jointAmplitude W₀))
    (hW₁ : ContDiff ℝ ∞ (jointAmplitude W₁))
    (D : ℕ → ℝ)
    (h₀ : ∀ m, BoundedTwoTimeOrderSeminorm 0 J m W₀ ∧
      twoTimeOrderSeminorm 0 J m W₀ ≤ D m *
        (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B))
    (h₁ : ∀ m, BoundedTwoTimeOrderSeminorm 1 J m W₁ ∧
      twoTimeOrderSeminorm 1 J m W₁ ≤ D m *
        (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B)) (m : ℕ) :
    BoundedTwoTimeOrderSeminorm 0 J m (W₀ + W₁) ∧
      twoTimeOrderSeminorm 0 J m (W₀ + W₁) ≤ (2 * D m) *
        (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B) := by
  obtain ⟨hf, hb⟩ := solver_order_zero_bound hJ hW₀ hW₁ (h₀ m).1 (h₁ m).1
  refine ⟨hf, (hb.trans (add_le_add (h₀ m).2 (h₁ m).2)).trans_eq ?_⟩
  ring

/-- Restrict the producer's actual normalized amplitude budgets to the smaller
retained phase buffer. The radial band and amplitude remain unchanged; global
smoothness is exactly the supported-amplitude conclusion of `ConicConstruction`
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem retained_amplitude_restriction
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ρ ra rb : ℝ} (hερ : ε ≤ ρ / 2) {o m : ℕ} {W : TwoTimeAmplitude d q}
    (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (hf : BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m W) :
    BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z ε ra rb) m W ∧
      twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z ε ra rb) m W ≤
        twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m W := by
  have hsub : ConicPhase.bufferedJetSet ℓ z ε ra rb ⊆
      ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb := by
    intro p hp
    have hrad : 2 * ε ≤ 2 * (ρ / 2) := by linarith
    refine ⟨⟨closedBall_subset_closedBall hrad hp.1.1,
      closedBall_subset_closedBall hrad hp.1.2.1,
      closedBall_subset_closedBall hrad hp.1.2.2⟩, ?_⟩
    obtain ⟨v, ⟨hv, hθ, hℓ⟩, he⟩ := hp.2
    exact ⟨v, ⟨hv, closedBall_subset_closedBall hερ hθ, hℓ⟩, he⟩
  have hbound (R : ℝ) (hR : 1 ≤ R) :
      cNorm (ConicPhase.bufferedJetSet ℓ z ε ra rb) m (twoTimeOrderField o R W) ≤
        twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m W :=
    (cNorm_mono_set hsub (ConicPhase.isCompact_bufferedJetSet _ _ _ _ _)
      ((contDiff_twoTimeOrderField hW o R).of_le (by simp))).trans
        (cNorm_twoTimeOrderField_le hf hR)
  refine ⟨⟨twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m W, ?_⟩, ?_⟩
  · rintro _ ⟨R, rfl⟩
    exact hbound R R.2
  · exact Real.sSup_le (by rintro _ ⟨R, rfl⟩; exact hbound R R.2)
      (twoTimeOrderSeminorm_nonneg _ _ _ _)

end JanetCartan.RegularSector.Characteristic.UniformEvolution
