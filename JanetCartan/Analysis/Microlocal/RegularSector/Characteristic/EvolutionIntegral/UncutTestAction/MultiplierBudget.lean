module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude

/-!
# Schwartz multiplier regularity from the original symbol budgets

The smooth order-zero symbol class in `app:ch_regular_base:lem:retarded-kernel`
has a finite normalized seminorm at every order. On the same finite carrier
cover used by `PrimitiveRetarded`, these budgets bound every derivative of
the original multiplier. This is the producer of `HasTemperateGrowth` used
by the uncut multiplier-slice proof. It does not follow from just the one
finite reserve needed for the parent's low operator estimate.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles SymbolBudgets
variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)

private theorem norm_iteratedFDeriv_le_jointMultiplier (β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β) (k : ℕ) (p : Point (d + 1)) :
    ‖iteratedFDeriv ℝ k β p.2‖ ≤ ‖iteratedFDeriv ℝ k (jointMultiplier β) p‖ := by
  have he := (ContinuousLinearMap.snd ℝ (E × E) E).iteratedFDeriv_comp_right
    hβ p (i := k) (by simp)
  change iteratedFDeriv ℝ k (jointMultiplier β) p = _ at he
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro m
  have hm := (iteratedFDeriv ℝ k (jointMultiplier β) p).le_opNorm
    (fun i ↦ ((0 : E × E), m i))
  conv_lhs at hm => rw [he]
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.coe_snd', Prod.norm_mk, norm_zero,
    max_eq_right (norm_nonneg _)] using hm

/-- The finite normalized carrier cover bounds each derivative of the
original multiplier at the same derivative order. This is the primitive
producer for the Schwartz multiplier argument in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_iteratedFDeriv_multiplier_le_normalized_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β)
    (hcover : ∀ ξ ∈ tsupport β, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ p ∈ Metric.closedBall (z i) (δ i), ξ = R • p.2)
    (k : ℕ) (hb : ∀ i, BoundedNormalizedSeminorm
      (Metric.closedBall (z i) (δ i)) k (jointMultiplier β)) (ξ : E) :
    ‖iteratedFDeriv ℝ k β ξ‖ ≤
      ∑ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) k (jointMultiplier β) := by
  classical
  by_cases hξ : ξ ∈ tsupport β
  · obtain ⟨i, R, hR, p, hp, rfl⟩ := hcover ξ hξ
    have hs : ContDiff ℝ ∞ (fun η : E ↦ β (R • η)) :=
      hβ.comp (contDiff_id.const_smul R)
    have hj := norm_iteratedFDeriv_le_jointMultiplier (fun η ↦ β (R • η)) hs k p
    change ‖iteratedFDeriv ℝ k (fun η ↦ β (R • η)) p.2‖ ≤
      ‖iteratedFDeriv ℝ k (normalizedField R (jointMultiplier β)) p‖ at hj
    have hcn := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall (z i) (δ i))
      ((hs.comp contDiff_snd).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) hp (le_refl k)
    change ‖iteratedFDeriv ℝ k (normalizedField R (jointMultiplier β)) p‖ ≤
      cNorm (Metric.closedBall (z i) (δ i)) k (normalizedField R (jointMultiplier β)) at hcn
    have hscale := congrFun (iteratedFDeriv_comp_const_smul R
      (hβ.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))) p.2
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hj
    have hpow : 1 ≤ R ^ k := one_le_pow₀ hR
    calc
      _ ≤ R ^ k * ‖iteratedFDeriv ℝ k β (R • p.2)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hpow
      _ ≤ _ := hj
      _ ≤ _ := hcn
      _ ≤ normalizedSeminorm (Metric.closedBall (z i) (δ i)) k (jointMultiplier β) :=
        cNorm_normalizedField_le (hb i) hR
      _ ≤ _ := Finset.single_le_sum
        (fun j _ ↦ normalizedSeminorm_nonneg (Metric.closedBall (z j) (δ j)) k
          (jointMultiplier β)) (Finset.mem_univ i)
  · have hz : iteratedFDeriv ℝ k β ξ = 0 := by
      by_contra hn
      exact hξ (support_iteratedFDeriv_subset k hn)
    rw [hz, norm_zero]
    exact Finset.sum_nonneg fun i _ ↦ normalizedSeminorm_nonneg _ _ _

/-- Any finite normalized reserve bounds the original multiplier itself.
This is the finite-budget producer of the frequency bound used in
`exists_bound_reverseRetardedFrequency`, for
`app:ch_regular_base:lem:retarded-kernel`. Unlike Schwartz preservation,
it does not require all derivative orders. -/
theorem norm_multiplier_le_finite_normalized_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β)
    (hcover : ∀ ξ ∈ tsupport β, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ p ∈ Metric.closedBall (z i) (δ i), ξ = R • p.2)
    (k : ℕ) (hb : ∀ i, BoundedNormalizedSeminorm
      (Metric.closedBall (z i) (δ i)) k (jointMultiplier β)) (ξ : E) :
    ‖β ξ‖ ≤ ∑ i, normalizedSeminorm
      (Metric.closedBall (z i) (δ i)) 0 (jointMultiplier β) := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_multiplier_le_normalized_budgets z δ β hβ hcover 0
      (fun i ↦ (hb i).mono (Nat.zero_le k)) ξ

/-- The parent's actual joint carrier cover supplies the frequency cover
needed for the finite multiplier bound whenever both physical masks have
nonempty support. Empty masks give zero test pairings separately. Consumer:
the primitive instantiation of
`retardedOperator_adjoint_pairing_reverseTriangle_of_strongLimit`, for
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_multiplier_le_primitive_joint_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (χout χsource β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β)
    (ho : (tsupport χout).Nonempty) (hs : (tsupport χsource).Nonempty)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R)
    (k : ℕ) (hb : ∀ i, BoundedNormalizedSeminorm
      (Metric.closedBall (z i) (δ i)) k (jointMultiplier β)) (ξ : E) :
    ‖β ξ‖ ≤ ∑ i, normalizedSeminorm
      (Metric.closedBall (z i) (δ i)) 0 (jointMultiplier β) := by
  apply norm_multiplier_le_finite_normalized_budgets z δ β hβ _ k hb ξ
  intro η hη
  obtain ⟨x, hx⟩ := ho
  obtain ⟨y, hy⟩ := hs
  obtain ⟨i, R, hR, v, hv, he, _⟩ := hcover ((x, y), η) ⟨⟨hx, hy⟩, hη⟩
  exact ⟨i, R, hR, v, hv, congrArg Prod.snd he⟩

/-- A smooth order-zero multiplier with the original finite carrier cover
and finite normalized seminorms at every order has temperate growth.
Consumer: `sourceInputFourierTransform_physicalMultiplierSlice`, in
`app:ch_regular_base:eq:fixed-time-representation`. This theorem explicitly
retains the all-orders symbol-class assumption, separately from the finite
reserve used for a quantitative low estimate. -/
theorem hasTemperateGrowth_multiplier_of_normalized_budgets
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (β : E → ℂ)
    (hβ : ContDiff ℝ ∞ β)
    (hcover : ∀ ξ ∈ tsupport β, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
      ∃ p ∈ Metric.closedBall (z i) (δ i), ξ = R • p.2)
    (hb : ∀ k i, BoundedNormalizedSeminorm
      (Metric.closedBall (z i) (δ i)) k (jointMultiplier β)) :
    β.HasTemperateGrowth := by
  refine ⟨hβ, fun k ↦ ⟨0, ∑ i,
    normalizedSeminorm (Metric.closedBall (z i) (δ i)) k (jointMultiplier β), ?_⟩⟩
  intro ξ
  simpa only [pow_zero, mul_one] using
    norm_iteratedFDeriv_multiplier_le_normalized_budgets z δ β hβ hcover k (hb k) ξ

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
