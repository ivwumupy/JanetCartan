module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability.JetInduction

/-!
# Finite-order continuity of actual transverse roots

For `app:lem:common-hamilton-phase`, iterate the differentiated root-equation
comparison on a fixed compact parameter set. Every lower perturbed root jet
bound is derived from the preceding comparison. The perturbation uses exactly
order `m`, in addition to a separate fixed `C¹` gap neighborhood; only the fixed
reference equation uses order `m+1`.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem exists_root_stability_of_compact
    {f₀ : P × ℝ → ℝ} {g₀ : P → ℝ} {K D : Set (P × ℝ)} {S U : Set P}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hS : IsCompact S)
    (hD : IsOpen D) (hKD : K ⊆ D) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    {l u c : ℝ} (hc : 0 < c)
    (hseg : ∀ p ∈ U, ∀ t ∈ Icc l u, (p, t) ∈ K)
    (hgap₀ : ∀ z ∈ K, 2 * c ≤ |scalarDerivative f₀ z|)
    (hroot₀ : ∀ p ∈ U, g₀ p ∈ Icc l u ∧ f₀ (p, g₀ p) = 0) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f : P × ℝ → ℝ) (g : P → ℝ),
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ g U →
      (∀ p ∈ U, g p ∈ Icc l u ∧ f (p, g p) = 0) →
      cNorm K 1 (f - f₀) ≤ c → cNorm K m (f - f₀) ≤ 1 →
      cNorm S m (g - g₀) ≤ C * cNorm K m (f - f₀) := by
  induction m with
  | zero =>
    refine ⟨1 / c, by positivity, ?_⟩
    intro f g hf _hg hroot hsmall _hbound
    simpa only [one_div_mul_eq_div] using
      cNorm_root_sub_zero_le hK hD hKD hf hf₀ hc
        (fun p hp ↦ hseg p (hSU hp))
        (scalar_gap_of_cNorm_one_sub_le hK hD hKD hf hf₀ hgap₀ hsmall)
        (fun p hp ↦ hroot p (hSU hp)) (fun p hp ↦ hroot₀ p (hSU hp))
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      refine ⟨1 / c + (1 + cNorm K 2 f₀ / c) ^ 2 / c, by positivity, ?_⟩
      intro f g hf hg hroot hsmall _hbound
      exact cNorm_root_sub_one_le hK hconv hD hKD hU hSU hf hf₀ hg hg₀ hc hseg
        (scalar_gap_of_cNorm_one_sub_le hK hD hKD hf hf₀ hgap₀ hsmall)
        (fun z hz ↦ by linarith [hgap₀ z hz]) hroot hroot₀
    obtain ⟨B, hB, hprev⟩ := ih
    let M := 1 + cNorm K (m + 1) f₀ + cNorm S (m + 1) g₀ + B
    have hM : 1 ≤ M := by
      dsimp [M]
      linarith [cNorm_nonneg K (m + 1) f₀, cNorm_nonneg S (m + 1) g₀]
    let A := 1 + cNorm K (m + 1 + 1) f₀ / c
    have hA : 0 < A := by
      dsimp [A]
      linarith [div_nonneg (cNorm_nonneg K (m + 1 + 1) f₀) hc.le]
    obtain ⟨T, hT, hstep⟩ := exists_root_jet_difference_step (P := P) (m + 1)
      (by omega) M c hM hc
    refine ⟨B + T * (A + B), by positivity, ?_⟩
    intro f g hf hg hroot hsmall hbound
    let ε := cNorm K (m + 1) (f - f₀)
    have hε : 0 ≤ ε := cNorm_nonneg _ _ _
    have hgap := scalar_gap_of_cNorm_one_sub_le hK hD hKD hf hf₀ hgap₀ hsmall
    have hlower : cNorm S m (g - g₀) ≤ B * ε :=
      (hprev f g hf hg hroot hsmall
        ((cNorm_mono_order (Nat.le_succ m)).trans hbound)).trans
        (mul_le_mul_of_nonneg_left (cNorm_mono_order (Nat.le_succ m)) hB.le)
    have htop : ∀ p ∈ S, ‖iteratedFDeriv ℝ (m + 1) (g - g₀) p‖ ≤
        T * (A + B) * ε := by
      intro p hp
      have hpU := hSU hp
      have hz := hseg p hpU _ (hroot p hpU).1
      have hz₀ := hseg p hpU _ (hroot₀ p hpU).1
      have hgp : ContDiffAt ℝ ∞ g p := hg.contDiffAt (hU.mem_nhds hpU)
      have hg₀p : ContDiffAt ℝ ∞ g₀ p := hg₀.contDiffAt (hU.mem_nhds hpU)
      have hfjet₀ (j : ℕ) (hj : j ≤ m + 1) :
          ‖iteratedFDeriv ℝ j f₀ (p, g₀ p)‖ ≤ cNorm K (m + 1) f₀ :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
          (fun z hz ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp)) hz₀ hj
      have hgjet₀ (j : ℕ) (hj : j ≤ m + 1) :
          ‖iteratedFDeriv ℝ j g₀ p‖ ≤ cNorm S (m + 1) g₀ :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
          (fun q hq ↦ (hg₀.contDiffAt (hU.mem_nhds (hSU hq))).of_le (by simp)) hp hj
      have hdiff (j : ℕ) (hj : j < m + 1) :
          ‖iteratedFDeriv ℝ j g p - iteratedFDeriv ℝ j g₀ p‖ ≤ B * ε := by
        rw [← iteratedFDeriv_sub_apply (hgp.of_le (by simp)) (hg₀p.of_le (by simp))]
        exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
          (fun q hq ↦ ((hg.sub hg₀).contDiffAt (hU.mem_nhds (hSU hq))).of_le
            (by simp)) hp (by omega : j ≤ m)).trans hlower
      have heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0 := by
        filter_upwards [hU.mem_nhds hpU] with q hq using (hroot q hq).2
      have heq₀ : ∀ᶠ q in 𝓝 p, f₀ (q, g₀ q) = 0 := by
        filter_upwards [hU.mem_nhds hpU] with q hq using (hroot₀ q hq).2
      rw [iteratedFDeriv_sub_apply (hgp.of_le (by simp)) (hg₀p.of_le (by simp))]
      rw [mul_assoc]
      apply hstep f f₀ g g₀ p ((A + B) * ε) (by positivity)
        ((hf.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
        ((hf₀.contDiffAt (hD.mem_nhds (hKD hz₀))).of_le (by simp))
        (hgp.of_le (by simp)) (hg₀p.of_le (by simp)) heq heq₀ (hgap _ hz)
      · intro j _hj hjn
        have hsame := equation_jet_sub_le_cNorm hK hD hKD hf hf₀ hjn hz
        have href : ‖iteratedFDeriv ℝ j f₀ (p, g p)‖ ≤ cNorm K (m + 1) f₀ :=
          norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun z hz ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp)) hz hjn
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (iteratedFDeriv ℝ j f (p, g p)) (iteratedFDeriv ℝ j f₀ (p, g p)) 0
        simp only [sub_zero] at htri
        dsimp [M]
        linarith [cNorm_nonneg S (m + 1) g₀]
      · intro j _hj hjn
        exact (hfjet₀ j hjn).trans (by dsimp [M]; linarith [cNorm_nonneg S (m + 1) g₀])
      · intro j _hj hjn
        exact (rootGraph_jet_sub_le_cNorm hK hconv hD hKD hf hf₀ hjn hc
          (hseg p hpU) (fun t ht ↦ hgap _ (hseg p hpU t ht))
          (hroot p hpU).1 (hroot₀ p hpU).1 (hroot p hpU).2 (hroot₀ p hpU).2).trans
          (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith : A ≤ A + B) hε)
      · intro j _hj hjn
        exact (hgjet₀ j hjn).trans (by dsimp [M]; linarith [cNorm_nonneg K (m + 1) f₀])
      · intro j _hj hjn
        have hd := hdiff j hjn
        have hb := hgjet₀ j hjn.le
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (iteratedFDeriv ℝ j g p) (iteratedFDeriv ℝ j g₀ p) 0
        simp only [sub_zero] at htri
        have hBε : B * ε ≤ B := by simpa using mul_le_mul_of_nonneg_left hbound hB.le
        dsimp [M]
        linarith [cNorm_nonneg K (m + 1) f₀]
      · intro j _hj hjn
        exact (hdiff j hjn).trans
          (mul_le_mul_of_nonneg_right (by linarith : B ≤ A + B) hε)
    rw [cNorm_succ]
    calc
      _ ≤ B * ε + T * (A + B) * ε := by
        apply add_le_add hlower
        apply Real.sSup_le _ (by positivity)
        rintro _ ⟨p, hp, rfl⟩
        exact htop p hp
      _ = _ := by ring

/-- `app:lem:common-hamilton-phase`: actual smooth roots on a common transverse
cylinder depend locally Lipschitz continuously in `C^m` on the equation in
`C^m`. The constant is fixed before the perturbed equation and root. The
separate `C¹` neighborhood preserves the scalar gap, and the order-`m` unit
neighborhood supplies all higher jet bounds by induction. No derivative bound
or derivative closeness of the perturbed root is assumed.

The root producer is `exists_uniform_C1_stable_sectionRoot`; the parent phase
construction supplies this cylinder and applies
`exists_sectionEnergy_finiteOrder_bound` on its normalized state domain. -/
theorem exists_finiteOrder_root_stability_on_closedBall [ProperSpace P]
    {f₀ : P × ℝ → ℝ} {g₀ : P → ℝ} {D : Set (P × ℝ)}
    {p₀ : P} {r l u c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hD : IsOpen D) (hKD : closedBall p₀ (2 * r) ×ˢ Icc l u ⊆ D)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) (hg₀ : ContDiffOn ℝ ∞ g₀ (ball p₀ (2 * r)))
    (hgap₀ : ∀ z ∈ closedBall p₀ (2 * r) ×ˢ Icc l u,
      2 * c ≤ |scalarDerivative f₀ z|)
    (hroot₀ : ∀ p ∈ ball p₀ (2 * r), g₀ p ∈ Icc l u ∧ f₀ (p, g₀ p) = 0)
    (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f : P × ℝ → ℝ) (g : P → ℝ),
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ g (ball p₀ (2 * r)) →
      (∀ p ∈ ball p₀ (2 * r), g p ∈ Icc l u ∧ f (p, g p) = 0) →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) 1 (f - f₀) ≤ c →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) m (f - f₀) ≤ 1 →
      cNorm (closedBall p₀ r) m (g - g₀) ≤
        C * cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) m (f - f₀) :=
  exists_root_stability_of_compact ((isCompact_closedBall p₀ (2 * r)).prod isCompact_Icc)
    ((convex_closedBall p₀ (2 * r)).prod (convex_Icc l u)) (isCompact_closedBall p₀ r)
    hD hKD isOpen_ball (closedBall_subset_ball (by linarith)) hf₀ hg₀ hc
    (fun _ hp _ ht ↦ ⟨ball_subset_closedBall hp, ht⟩) hgap₀ hroot₀ m

/-- `app:lem:common-hamilton-phase`: epsilon–delta continuity of the actual
roots in each finite-order seminorm on the fixed inner ball. The independent
`C¹` equation neighborhood is the low-order gap condition supplied by the
common symbol neighborhood. The higher perturbation order is exactly `m`. -/
theorem exists_finiteOrder_root_continuity_on_closedBall [ProperSpace P]
    {f₀ : P × ℝ → ℝ} {g₀ : P → ℝ} {D : Set (P × ℝ)}
    {p₀ : P} {r l u c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hD : IsOpen D) (hKD : closedBall p₀ (2 * r) ×ˢ Icc l u ⊆ D)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) (hg₀ : ContDiffOn ℝ ∞ g₀ (ball p₀ (2 * r)))
    (hgap₀ : ∀ z ∈ closedBall p₀ (2 * r) ×ˢ Icc l u,
      2 * c ≤ |scalarDerivative f₀ z|)
    (hroot₀ : ∀ p ∈ ball p₀ (2 * r), g₀ p ∈ Icc l u ∧ f₀ (p, g₀ p) = 0)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (f : P × ℝ → ℝ) (g : P → ℝ),
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ g (ball p₀ (2 * r)) →
      (∀ p ∈ ball p₀ (2 * r), g p ∈ Icc l u ∧ f (p, g p) = 0) →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) 1 (f - f₀) ≤ c →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) m (f - f₀) < δ →
      cNorm (closedBall p₀ r) m (g - g₀) < ε := by
  obtain ⟨C, hC, hbound⟩ := exists_finiteOrder_root_stability_on_closedBall
    hr hc hD hKD hf₀ hg₀ hgap₀ hroot₀ m
  refine ⟨min 1 (ε / C), lt_min zero_lt_one (div_pos hε hC), ?_⟩
  intro f g hf hg hroot hsmall hδ
  have hunit := hδ.le.trans (min_le_left _ _)
  apply (hbound f g hf hg hroot hsmall hunit).trans_lt
  have hε' := hδ.trans_le (min_le_right _ _)
  calc
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hε' hC
    _ = ε := mul_div_cancel₀ _ hC.ne'

end JanetCartan.CharacteristicRoot
