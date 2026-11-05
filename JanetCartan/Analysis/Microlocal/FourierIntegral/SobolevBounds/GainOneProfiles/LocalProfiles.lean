module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneProfiles.Normalization

/-!
# Individual gain-one profiles on one buffered normalized chart

Interpolation at the fixed baseline `μ₀+1` supplies the exact excess exponent
in `GainOneBranches.profile`. The phase baseline is `μ₀+3`, independently of
the remaining output order `t`. Actual inverse jets are bounded by the proved
tame inverse theorem in `PrimitiveProfiles`, not by an additional high premise.
Source: Step 3 before `app:ch_regular_base:eq:fio-input` and its gain-one paragraph.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneBranches
variable {n r : ℕ}

/-- Buffered interpolation gives precisely the individual gain-one excess
profile, including `t=0`. The constant precedes the field and both endpoints.
Consumer: `exists_localGainOne_profiles`; source: Step 3 interpolation. -/
theorem exists_cNorm_gainOne_profile_constant
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (z : Point n) {δ : ℝ} (hδ : 0 < δ) {U : Set (Point n)}
    (hU : IsOpen U) (hball : Metric.closedBall z δ ⊆ U)
    (b t : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ f : Point n → F, ContDiffOn ℝ ∞ f U →
      ∀ H : ℝ, 1 ≤ H → cNorm (Metric.closedBall z δ) b f ≤ L →
      cNorm (Metric.closedBall z δ) (b + t) f ≤ H →
      ∀ j : ℕ, j ≤ b + t → cNorm (Metric.closedBall z δ) j f ≤
        (K * L) * profile b t H j := by
  obtain ⟨K, hK, hb⟩ := TransportInterpolation.exists_transportPrimitiveProfile_finite_on
    (F := F) z hδ hU hball b t hL
  refine ⟨K, hK, ?_⟩
  intro f hf H hH hlow hhigh j hj
  have he : (j - b) + min j b = j := by omega
  simpa only [he, Nat.add_zero, profile] using
    hb f (hf.of_le (by simp)) H hH hlow hhigh (j - b) (min j b) 0
      (by omega) (by omega)

/-- All three original primitive profiles on one normalized ball, with the
actual order-minus-one amplitude seminorm. The high order is `t+1+(μ₀+2)`;
only the fixed phase baseline `μ₀+3`, amplitude baseline `μ₀+1`, and zeroth-order
inverse gap enter the constants. The high majorant premise is a numerical
endpoint comparison, discharged by the finite-cover theorem in this module.
No individual interpolation or inverse-jet bound is assumed.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem exists_localGainOne_profiles
    (z : Point n) {δ : ℝ} (hδ : 0 < δ) {U V : Set (Point n)}
    (hU : IsOpen U) (hball : Metric.closedBall z δ ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ t : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ P C : ℝ, 1 ≤ P ∧ 1 ≤ C ∧
      ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r),
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ p ∈ Metric.closedBall z δ, ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ j, BoundedOrderMinusOneSeminorm (Metric.closedBall z δ) j A) →
      cNorm (Metric.closedBall z δ) (μ₀ + 3) (fun p : Point n ↦ S p.1.1 p.2) ≤ M →
      orderMinusOneSeminorm (Metric.closedBall z δ) (μ₀ + 1) A ≤ M →
      ∀ H : ℝ, 1 ≤ H →
      C * (1 + orderMinusOneSeminorm (Metric.closedBall z δ) (t + 1 + (μ₀ + 2)) A +
        cNorm (Metric.closedBall z δ) (t + 1 + (μ₀ + 2))
          (fun p : Point n ↦ S p.1.1 p.2)) ≤ H →
      (∀ R : ℝ, 1 ≤ R → ∀ j : ℕ, j ≤ (μ₀ + 1) + t →
        cNorm (Metric.closedBall z δ) j (orderMinusOneField R A) ≤
          P * profile (μ₀ + 1) t H j) ∧
      (∀ j : ℕ, j ≤ (μ₀ + 1) + t →
        cNorm (Metric.closedBall z δ) j (fun p : Point n ↦ S p.1.1 p.2) ≤
          P * profile (μ₀ + 1) t H j) ∧
      (∀ a (j : ℕ), j ≤ (μ₀ + 1) + t →
        normalizedSeminorm (Metric.closedBall z δ) j (uncurry (scalarPrimitive S a)) ≤
          P * profile (μ₀ + 1) t H j) := by
  have hUV : U ⊆ V := by intro p hp; simpa using hrad 1 le_rfl p hp
  have hchartU (p) (hp : p ∈ U) := hchart p (hUV hp)
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_normalizedSeminorm_scalarPrimitive_le_phase
    z hδ hU hball hX hD hchartU hcone (μ₀ + 1) hM B
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_normalizedSeminorm_scalarPrimitive_le_phase
    z hδ hU hball hX hD hchartU hcone ((μ₀ + 1) + t) hM B
  let L := 1 + C₀ * (1 + M)
  have hL : 1 ≤ L := by dsimp [L]; nlinarith
  have hM1 : 1 ≤ 1 + M := by linarith
  obtain ⟨KA, hKA, hiA⟩ := exists_cNorm_gainOne_profile_constant
    (F := Matrix (Fin r) (Fin r) ℂ) z hδ hU hball (μ₀ + 1) t hM1
  obtain ⟨KP, hKP, hiP⟩ := exists_cNorm_gainOne_profile_constant
    (F := ℝ) z hδ hU hball (μ₀ + 1) t hM1
  obtain ⟨KS, hKS, hiS⟩ := exists_normalizedSeminorm_interpolation_constant
    (F := ℂ) z hδ hU hball (μ₀ + 1) t
  let P := max (KA * (1 + M)) (max (KP * (1 + M)) (KS * L))
  have hPA : KA * (1 + M) ≤ P := le_max_left _ _
  have hPP : KP * (1 + M) ≤ P := (le_max_left _ _).trans (le_max_right _ _)
  have hPS : KS * L ≤ P := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨P, 1 + C₁, (one_le_mul_of_one_le_of_one_le hKA hM1).trans hPA,
    by linarith, ?_⟩
  intro S A hS hhom hinv hgap hA hbA hlowS hlowA H hH hhigh
  let k := t + 1 + (μ₀ + 2)
  let f := fun p : Point n ↦ S p.1.1 p.2
  have hfn : 0 ≤ cNorm (Metric.closedBall z δ) k f := cNorm_nonneg _ _ _
  have han : 0 ≤ orderMinusOneSeminorm (Metric.closedBall z δ) k A :=
    orderMinusOneSeminorm_nonneg _ _ _
  have hAH : orderMinusOneSeminorm (Metric.closedBall z δ) k A ≤ H := by
    change (1 + C₁) * (1 + orderMinusOneSeminorm (Metric.closedBall z δ) k A +
      cNorm (Metric.closedBall z δ) k f) ≤ H at hhigh
    nlinarith
  have hPH : cNorm (Metric.closedBall z δ) k f ≤ H := by
    change (1 + C₁) * (1 + orderMinusOneSeminorm (Metric.closedBall z δ) k A +
      cNorm (Metric.closedBall z δ) k f) ≤ H at hhigh
    nlinarith
  have hf : ContDiffOn ℝ ∞ f U := by
    intro p hp
    exact ((hS.contDiffAt ((hX.prod hD).mem_nhds (hchartU p hp))).comp p
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).contDiffWithinAt
  have hlow₂ : cNorm (Metric.closedBall z δ) 2 f ≤ M :=
    (CNormInterpolation.cNorm_mono _ _ (by omega : 2 ≤ μ₀ + 3)).trans hlowS
  have hreg (a : ScalarIndex n) (j : ℕ) := normalized_scalarPrimitive_regular
    hX hD hcone hS hhom hU hball hchartU (fun p hp ↦ hinv p (hUV hp)) a j
  refine ⟨?_, ?_, ?_⟩
  · intro R hR j hj
    apply (hiA (orderMinusOneField R A) (contDiffOn_orderMinusOneField hA hrad hR)
      H hH ((cNorm_orderMinusOneField_le (hbA _) hR).trans (hlowA.trans (by linarith)))
      ((CNormInterpolation.cNorm_mono _ _ (by dsimp [k]; omega : (μ₀ + 1) + t ≤ k)).trans
        ((cNorm_orderMinusOneField_le (hbA _) hR).trans hAH)) j hj).trans
    exact mul_le_mul_of_nonneg_right hPA (profile_nonneg _ _ _ hH)
  · intro j hj
    apply (hiP f hf H hH
      ((CNormInterpolation.cNorm_mono _ _ (by omega : μ₀ + 1 ≤ μ₀ + 3)).trans
        (hlowS.trans (by linarith)))
      ((CNormInterpolation.cNorm_mono _ _ (by dsimp [k]; omega : (μ₀ + 1) + t ≤ k)).trans hPH)
      j hj).trans
    exact mul_le_mul_of_nonneg_right hPP (profile_nonneg _ _ _ hH)
  · intro a j hj
    let q := fun j ↦ normalizedSeminorm (Metric.closedBall z δ) j (uncurry (scalarPrimitive S a))
    have hqlow : q (μ₀ + 1) ≤ L := by
      have he := (hb₀ S hS hhom hlow₂ (fun p hp ↦ hinv p (hUV hp)) hgap a).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl 1) (by simpa only [Nat.add_assoc] using hlowS)) hC₀.le)
      change q (μ₀ + 1) ≤ C₀ * (1 + M) at he
      exact he.trans (by dsimp [L]; linarith)
    have hqhigh : q ((μ₀ + 1) + t) ≤ H := by
      have he := hb₁ S hS hhom hlow₂ (fun p hp ↦ hinv p (hUV hp)) hgap a
      have heq : (μ₀ + 1 + t) + 2 = k := by dsimp [k]; omega
      rw [heq] at he
      change q ((μ₀ + 1) + t) ≤ C₁ * (1 + cNorm (Metric.closedBall z δ) k f) at he
      change (1 + C₁) * (1 + orderMinusOneSeminorm (Metric.closedBall z δ) k A +
        cNorm (Metric.closedBall z δ) k f) ≤ H at hhigh
      nlinarith
    apply (profile_of_interpolation q (μ₀ + 1) t j L KS H
      (fun j ↦ normalizedSeminorm_nonneg _ j _) (fun j k hjk ↦
        normalizedSeminorm_mono (hreg a k).2.1 hjk)
      hL hKS hH hqlow hqhigh hj ?_).trans
    · exact mul_le_mul_of_nonneg_right hPS (profile_nonneg _ _ _ hH)
    · intro hj₁ hj₂
      exact hiS (uncurry (scalarPrimitive S a))
        (fun R hR ↦ ((hreg a 0).1 R hR).of_le (by simp)) (hreg a _).2.1 j hj₁ hj₂

end JanetCartan.FourierIntegral.GainOneProfiles
