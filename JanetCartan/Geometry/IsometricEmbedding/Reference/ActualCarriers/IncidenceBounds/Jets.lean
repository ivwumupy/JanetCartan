module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.LocalInterpolation
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.JetBounds

/-!
# Joint tame bounds for actual incidence

Coefficient estimates for `app:ch_seed:eq:seed-phase-tame` and Step 3 of
`app:ch_seed:prop:seed-actual-menu`. The frame and carrier gradient are primitive
inputs; no incidence or root bound is assumed. The domain includes all physical,
angular, and patch variables. The testing covectors remain in a fixed compact
patch (in the application, a patch of the unit sphere).

The parent `jc-actual-carriers` must instantiate the primitive frame and phase
bounds from `jc-projected-stress-frame` and `jc-hamilton-phase`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open Set Metric

namespace JanetCartan.ActualCarriers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem cNorm_incidenceInputs_le {s U : Set E} (hs : IsCompact s)
    (hU : IsOpen U) (hsU : s ⊆ U) (r : ℕ)
    {Q : E → Fin n → MetricTensor n} {ξ k : E → Euclidean n}
    (hQ : ContDiffOn ℝ ∞ Q U) (hξ : ContDiffOn ℝ ∞ ξ U)
    (hk : ContDiffOn ℝ ∞ k U) :
    cNorm s r (fun x ↦ ((Q x, ξ x), k x)) ≤
      (r + 1 : ℝ) * (cNorm s r Q + cNorm s r ξ + cNorm s r k) := by
  have hQr (x : E) (hx : x ∈ s) : ContDiffAt ℝ r Q x :=
    (hQ.contDiffAt (hU.mem_nhds (hsU hx))).of_le (by simp)
  have hξr (x : E) (hx : x ∈ s) : ContDiffAt ℝ r ξ x :=
    (hξ.contDiffAt (hU.mem_nhds (hsU hx))).of_le (by simp)
  have hkr (x : E) (hx : x ∈ s) : ContDiffAt ℝ r k x :=
    (hk.contDiffAt (hU.mem_nhds (hsU hx))).of_le (by simp)
  have hQ0 := cNorm_nonneg s r Q
  have hξ0 := cNorm_nonneg s r ξ
  have hk0 := cNorm_nonneg s r k
  have hb := cNorm_le_sum_of_bounds (s := s) (r := r)
    (f := fun x ↦ ((Q x, ξ x), k x))
    (C := fun _ ↦ cNorm s r Q + cNorm s r ξ + cNorm s r k)
    (fun _ _ ↦ by linarith) (by
      intro j hj x hx
      rw [iteratedFDeriv_prodMk ((hQr x hx).prodMk (hξr x hx)) (hkr x hx)
          (by exact_mod_cast hj),
        iteratedFDeriv_prodMk (hQr x hx) (hξr x hx) (by exact_mod_cast hj),
        ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
      have h1 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hQr hx hj
      have h2 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hξr hx hj
      have h3 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hs hkr hx hj
      exact max_le (max_le (by linarith) (by linarith)) (by linarith))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] using hb

/-- `app:ch_seed:eq:seed-phase-tame`, Step 3: a uniform joint incidence bound
from the separate primitive frame, phase-gradient, and testing-covector norms.
The constant is chosen before those fields and their open domain. There is no
derivative loss; in particular this composition does not enlarge an input
`r + 6` reserve. Compact ranges are fixed low data, not high-norm smallness. -/
theorem exists_cNorm_incidence_le_primitive
    (a : E) {ρ : ℝ} (hρ : 0 < ρ)
    {TQ : Set (Fin n → MetricTensor n)} {Tξ K : Set (Euclidean n)}
    (hTQ : IsCompact TQ) (hTξ : IsCompact Tξ) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E), IsOpen U → closedBall a ρ ⊆ U →
      ∀ (Q : E → Fin n → MetricTensor n) (ξ k : E → Euclidean n),
      ContDiffOn ℝ ∞ Q U → ContDiffOn ℝ ∞ ξ U → ContDiffOn ℝ ∞ k U →
      MapsTo Q (closedBall a ρ) TQ → MapsTo ξ (closedBall a ρ) Tξ →
      MapsTo k (closedBall a ρ) K →
      cNorm (closedBall a ρ) r (fun x ↦ fderiv ℝ (determinant (Q x)) (ξ x) (k x)) ≤
        C * (1 + cNorm (closedBall a ρ) r Q + cNorm (closedBall a ρ) r ξ +
          cNorm (closedBall a ρ) r k) := by
  obtain ⟨C, hC, hb⟩ :=
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ ((hTQ.prod hTξ).prod hK) (r := r) (k := r) le_rfl
      (fun _ _ ↦ (contDiff_incidenceCoefficient (n := n)).contDiffAt.of_le (by simp))
  refine ⟨C * (r + 1), by positivity, ?_⟩
  intro U hU hsU Q ξ k hQ hξ hk hQT hξT hkK
  have h := hb U hU hsU (fun x ↦ ((Q x, ξ x), k x))
    ((hQ.prodMk hξ).prodMk hk) (fun x hx ↦ ⟨⟨hQT hx, hξT hx⟩, hkK hx⟩)
  have hi := cNorm_incidenceInputs_le (isCompact_closedBall a ρ) hU hsU r hQ hξ hk
  change cNorm _ r (fun x ↦ fderiv ℝ (determinant (Q x)) (ξ x) (k x)) ≤ _ at h
  apply h.trans
  have hr : (1 : ℝ) ≤ r + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  nlinarith

/-- `app:ch_seed:eq:seed-phase-tame`, Step 3: the baseline-one equation profile
needed by `CharacteristicRoot.exists_rootGraph_jet_bound_of_equation_profile`.
Both the low equation bound and its high bound are derived from primitive norms.
The constant is uniform in the fields, point, and intermediate derivative order.
All derivatives are joint derivatives on the fixed buffered ball. -/
theorem exists_incidence_jet_profile
    (a : E) {ρ : ℝ} (hρ : 0 < ρ)
    {TQ : Set (Fin n → MetricTensor n)} {Tξ K : Set (Euclidean n)}
    (hTQ : IsCompact TQ) (hTξ : IsCompact Tξ) (hK : IsCompact K)
    {r : ℕ} (hr : 2 ≤ r) {L : ℝ} (hL : 0 ≤ L)
    {U : Set E} (hU : IsOpen U) (hsU : closedBall a ρ ⊆ U) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (Q : E → Fin n → MetricTensor n) (ξ k : E → Euclidean n),
      ContDiffOn ℝ ∞ Q U → ContDiffOn ℝ ∞ ξ U → ContDiffOn ℝ ∞ k U →
      MapsTo Q (closedBall a ρ) TQ → MapsTo ξ (closedBall a ρ) Tξ →
      MapsTo k (closedBall a ρ) K →
      cNorm (closedBall a ρ) 1 Q + cNorm (closedBall a ρ) 1 ξ +
        cNorm (closedBall a ρ) 1 k ≤ L →
      ∀ j, 1 ≤ j → j ≤ r → ∀ x ∈ closedBall a ρ,
        ‖iteratedFDeriv ℝ j
          (fun y ↦ fderiv ℝ (determinant (Q y)) (ξ y) (k y)) x‖ ≤
        M * (1 + cNorm (closedBall a ρ) r Q + cNorm (closedBall a ρ) r ξ +
          cNorm (closedBall a ρ) r k) ^ (((j : ℝ) - 1) / ((r : ℝ) - 1)) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_cNorm_incidence_le_primitive a hρ hTQ hTξ hK 1
  obtain ⟨C, hC, hb⟩ := exists_cNorm_incidence_le_primitive a hρ hTQ hTξ hK r
  obtain ⟨B, hB, hprofile⟩ :=
    FlowForcing.exists_uniform_cNorm_baseline_one_profile_closedBall_on
      (F := ℝ) a hρ hU hsU hr (mul_nonneg hC₁.le (by linarith : 0 ≤ 1 + L))
  refine ⟨B * (1 + C), ?_, ?_⟩
  · nlinarith
  intro Q ξ k hQ hξ hk hQT hξT hkK hlow j hj hjr x hx
  let f : E → ℝ := fun y ↦ fderiv ℝ (determinant (Q y)) (ξ y) (k y)
  have hf : ContDiffOn ℝ ∞ f U :=
    contDiff_incidenceCoefficient.comp_contDiffOn ((hQ.prodMk hξ).prodMk hk)
  have hf₁ : cNorm (closedBall a ρ) 1 f ≤ C₁ * (1 + L) := by
    apply (hb₁ U hU hsU Q ξ k hQ hξ hk hQT hξT hkK).trans
    nlinarith
  have hfr := hb U hU hsU Q ξ k hQ hξ hk hQT hξT hkK
  let H := 1 + cNorm (closedBall a ρ) r Q + cNorm (closedBall a ρ) r ξ +
    cNorm (closedBall a ρ) r k
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (closedBall a ρ) r Q, cNorm_nonneg (closedBall a ρ) r ξ,
      cNorm_nonneg (closedBall a ρ) r k]
  have hr' : 0 < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  let θ : ℝ := ((j : ℝ) - 1) / ((r : ℝ) - 1)
  have hθ₀ : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hj)) hr'.le
  have hθ₁ : θ ≤ 1 := (div_le_one hr').mpr
    (sub_le_sub_right (by exact_mod_cast hjr) 1)
  have hhigh : 1 + cNorm (closedBall a ρ) r f ≤ (1 + C) * H := by
    change cNorm (closedBall a ρ) r f ≤ C * H at hfr
    nlinarith
  have hpow : (1 + cNorm (closedBall a ρ) r f) ^ θ ≤ (1 + C) * H ^ θ := by
    calc
      _ ≤ ((1 + C) * H) ^ θ := Real.rpow_le_rpow
        (by linarith [cNorm_nonneg (closedBall a ρ) r f]) hhigh hθ₀
      _ = (1 + C) ^ θ * H ^ θ := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ (1 + C) * H ^ θ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        exact (Real.rpow_le_rpow_of_exponent_le (by linarith) hθ₁).trans_eq
          (Real.rpow_one _)
  have hpoint : ‖iteratedFDeriv ℝ j f x‖ ≤ cNorm (closedBall a ρ) j f :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hsU hy))).of_le (by simp)) hx le_rfl
  exact (hpoint.trans (hprofile f hf hf₁ j hj hjr)).trans
    ((mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hB)).trans_eq (by ring))

end JanetCartan.ActualCarriers
