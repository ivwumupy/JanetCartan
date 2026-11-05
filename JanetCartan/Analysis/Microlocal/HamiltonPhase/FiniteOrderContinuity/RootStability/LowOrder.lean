module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability.EquationJets

/-!
# Initial steps of the root stability induction

The `C⁰` and `C¹` comparisons of actual roots in
`app:lem:common-hamilton-phase`, with no loss of perturbation derivatives.
The gap is supplied by a separate fixed `C¹` equation neighborhood, itself
available from the common `C³` symbol neighborhood. No derivative comparison
of the roots is an assumption.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem norm_jet_one_sub {f f₀ : P × ℝ → ℝ} {x y : P × ℝ} :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f₀ y‖ =
      ‖fderiv ℝ f x - fderiv ℝ f₀ y‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map,
    iteratedFDeriv_zero_eq_comp]

/-- The fixed transverse gap only requires a `C¹` equation neighborhood.
This separates domain construction from the higher perturbation order in
`app:lem:common-hamilton-phase`. -/
theorem scalar_gap_of_cNorm_one_sub_le {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {c : ℝ} (hgap : ∀ z ∈ K, 2 * c ≤ |scalarDerivative f₀ z|)
    (hsmall : cNorm K 1 (f - f₀) ≤ c) :
    ∀ z ∈ K, c ≤ |scalarDerivative f z| := by
  intro z hz
  have h := equation_jet_sub_le_cNorm hK hD hKD hf hf₀ (le_refl 1) hz
  rw [norm_jet_one_sub] at h
  have hd := (fderiv ℝ f z - fderiv ℝ f₀ z).le_opNorm ((0, 1) : P × ℝ)
  have hd' : |scalarDerivative f z - scalarDerivative f₀ z| ≤ c := by
    have hd'' : |scalarDerivative f z - scalarDerivative f₀ z| ≤
        ‖fderiv ℝ f z - fderiv ℝ f₀ z‖ := by simpa [scalarDerivative] using hd
    exact hd''.trans (h.trans hsmall)
  have htri := abs_sub_abs_le_abs_sub (scalarDerivative f₀ z) (scalarDerivative f z)
  rw [abs_sub_comm (scalarDerivative f₀ z)] at htri
  linarith [hgap z hz]

/-- The zeroth root seminorm is controlled by the zeroth equation seminorm,
with the gap supplied independently (`app:lem:common-hamilton-phase`). -/
theorem cNorm_root_sub_zero_le {f f₀ : P × ℝ → ℝ} {g g₀ : P → ℝ}
    {K D : Set (P × ℝ)} {S : Set P}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {l u c : ℝ} (hc : 0 < c)
    (hseg : ∀ p ∈ S, ∀ t ∈ Icc l u, (p, t) ∈ K)
    (hgap : ∀ z ∈ K, c ≤ |scalarDerivative f z|)
    (hroot : ∀ p ∈ S, g p ∈ Icc l u ∧ f (p, g p) = 0)
    (hroot₀ : ∀ p ∈ S, g₀ p ∈ Icc l u ∧ f₀ (p, g₀ p) = 0) :
    cNorm S 0 (g - g₀) ≤ cNorm K 0 (f - f₀) / c := by
  rw [cNorm_order_zero]
  apply Real.sSup_le _ (div_nonneg (cNorm_nonneg _ _ _) hc.le)
  rintro _ ⟨p, hp, rfl⟩
  exact root_sub_le_cNorm_zero hK hD hKD hf hf₀ hc (hseg p hp)
    (fun t ht ↦ hgap _ (hseg p hp t ht))
    (hroot p hp).1 (hroot₀ p hp).1 (hroot p hp).2 (hroot₀ p hp).2

/-- Subtract the actual first differentiated root equations and take suprema.
Only the order-one equation perturbation occurs; the order-two reference norm
is fixed before perturbation (`app:lem:common-hamilton-phase`). -/
theorem cNorm_root_sub_one_le {f f₀ : P × ℝ → ℝ} {g g₀ : P → ℝ}
    {K D : Set (P × ℝ)} {S U : Set P}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hU : IsOpen U) (hSU : S ⊆ U)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    (hg : ContDiffOn ℝ ∞ g U) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    {l u c : ℝ} (hc : 0 < c)
    (hseg : ∀ p ∈ U, ∀ t ∈ Icc l u, (p, t) ∈ K)
    (hgap : ∀ z ∈ K, c ≤ |scalarDerivative f z|)
    (hgap₀ : ∀ z ∈ K, c ≤ |scalarDerivative f₀ z|)
    (hroot : ∀ p ∈ U, g p ∈ Icc l u ∧ f (p, g p) = 0)
    (hroot₀ : ∀ p ∈ U, g₀ p ∈ Icc l u ∧ f₀ (p, g₀ p) = 0) :
    cNorm S 1 (g - g₀) ≤
      (1 / c + (1 + cNorm K 2 f₀ / c) ^ 2 / c) * cNorm K 1 (f - f₀) := by
  let M := cNorm K 2 f₀
  let ε := cNorm K 1 (f - f₀)
  have hε : 0 ≤ ε := cNorm_nonneg _ _ _
  have hval : cNorm S 0 (g - g₀) ≤ ε / c :=
    (cNorm_root_sub_zero_le hK hD hKD hf hf₀ hc
      (fun p hp ↦ hseg p (hSU hp)) hgap
      (fun p hp ↦ hroot p (hSU hp)) (fun p hp ↦ hroot₀ p (hSU hp))).trans
        (div_le_div_of_nonneg_right (cNorm_mono_order (by omega : 0 ≤ 1)) hc.le)
  have hder : ∀ p ∈ S, ‖fderiv ℝ (g - g₀) p‖ ≤ (1 + M / c) ^ 2 * ε / c := by
    intro p hp
    have hpU := hSU hp
    have hz := hseg p hpU _ (hroot p hpU).1
    have hz₀ := hseg p hpU _ (hroot₀ p hpU).1
    have hfp := (hf.contDiffAt (hD.mem_nhds (hKD hz))).differentiableAt (by simp)
    have hf₀p := (hf₀.contDiffAt (hD.mem_nhds (hKD hz₀))).differentiableAt (by simp)
    have hgp := (hg.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
    have hg₀p := (hg₀.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
    have heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0 := by
      filter_upwards [hU.mem_nhds hpU] with q hq using (hroot q hq).2
    have heq₀ : ∀ᶠ q in 𝓝 p, f₀ (q, g₀ q) = 0 := by
      filter_upwards [hU.mem_nhds hpU] with q hq using (hroot₀ q hq).2
    have hM : ‖fderiv ℝ f₀ (p, g₀ p)‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_one] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
          (fun z hz ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
          hz₀ (by omega : 1 ≤ 2)
    have hG₀ := norm_fderiv_root_le hc hf₀p hg₀p heq₀ (hgap₀ _ hz₀) hM
    have hdiff := rootGraph_jet_sub_le_cNorm hK hconv hD hKD hf hf₀ (le_refl 1)
      hc (hseg p hpU) (fun t ht ↦ hgap _ (hseg p hpU t ht))
      (hroot p hpU).1 (hroot₀ p hpU).1 (hroot p hpU).2 (hroot₀ p hpU).2
    rw [norm_jet_one_sub] at hdiff
    have hb := fderiv_root_sub_le_of_fderiv_sub_le hc hfp hf₀p hgp hg₀p
      heq heq₀ (hgap _ hz) hG₀ hdiff
    rw [fderiv_sub hgp hg₀p]
    convert hb using 1
    dsimp [M, ε]
    ring
  rw [show (1 : ℕ) = 0 + 1 from rfl, cNorm_succ]
  calc
    _ ≤ ε / c + (1 + M / c) ^ 2 * ε / c := by
      apply add_le_add hval
      apply Real.sSup_le _ (by positivity)
      rintro _ ⟨p, hp, rfl⟩
      change ‖iteratedFDeriv ℝ 1 (g - g₀) p‖ ≤ _
      rw [norm_iteratedFDeriv_one]
      exact hder p hp
    _ = _ := by dsimp [M, ε]; ring

/-- The first-order stability constant is chosen before the perturbed equation
and its actual smooth root. The fixed cylinder and the separate `C¹` gap
neighborhood match the data supplied by `exists_uniform_C1_stable_sectionRoot`
in `app:lem:common-hamilton-phase`. -/
theorem exists_C1_root_stability_on_closedBall [ProperSpace P]
    {f₀ : P × ℝ → ℝ} {g₀ : P → ℝ} {D : Set (P × ℝ)}
    {p₀ : P} {r l u c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hD : IsOpen D) (hKD : closedBall p₀ (2 * r) ×ˢ Icc l u ⊆ D)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) (hg₀ : ContDiffOn ℝ ∞ g₀ (ball p₀ (2 * r)))
    (hgap₀ : ∀ z ∈ closedBall p₀ (2 * r) ×ˢ Icc l u,
      2 * c ≤ |scalarDerivative f₀ z|)
    (hroot₀ : ∀ p ∈ ball p₀ (2 * r), g₀ p ∈ Icc l u ∧ f₀ (p, g₀ p) = 0) :
    ∃ C > (0 : ℝ), ∀ (f : P × ℝ → ℝ) (g : P → ℝ),
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ g (ball p₀ (2 * r)) →
      (∀ p ∈ ball p₀ (2 * r), g p ∈ Icc l u ∧ f (p, g p) = 0) →
      cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) 1 (f - f₀) ≤ c →
      cNorm (closedBall p₀ r) 1 (g - g₀) ≤
        C * cNorm (closedBall p₀ (2 * r) ×ˢ Icc l u) 1 (f - f₀) := by
  let K := closedBall p₀ (2 * r) ×ˢ Icc l u
  have hK : IsCompact K := (isCompact_closedBall p₀ (2 * r)).prod isCompact_Icc
  refine ⟨1 / c + (1 + cNorm K 2 f₀ / c) ^ 2 / c, by positivity, ?_⟩
  intro f g hf hg hroot hsmall
  exact cNorm_root_sub_one_le hK ((convex_closedBall p₀ (2 * r)).prod (convex_Icc l u))
    hD hKD isOpen_ball (closedBall_subset_ball (by linarith)) hf hf₀ hg hg₀ hc
    (fun _ hp _ ht ↦ ⟨ball_subset_closedBall hp, ht⟩)
    (scalar_gap_of_cNorm_one_sub_le hK hD hKD hf hf₀ hgap₀ hsmall)
    (fun z hz ↦ by linarith [hgap₀ z hz]) hroot hroot₀

end JanetCartan.CharacteristicRoot
