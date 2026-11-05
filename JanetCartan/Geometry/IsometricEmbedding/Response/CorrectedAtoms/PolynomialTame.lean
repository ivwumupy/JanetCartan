module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Products

/-!
# An additive high bound for the exact raw derivative polynomial

Apply the existing compact-range product estimate to the literal normal
tensor, then use the exact three-power WKB formula. The original physical
derivative costs one joint jet. Only coefficient values enter the constants;
higher norms remain additive, and the entire error retains `τ`.

Consumers: all-order raw amplitudes, preparation discrepancy and the fixed
atomic offset in `app:ch_response:cor:current-atoms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.CorrectedAtoms
open RawPrimary.AmplitudeGrades.Polynomial

/-- The exact WKB polynomial has an additive high coefficient bound and its
error retains the factor `τ`. Only values of the five original coefficients
are bounded in advance; no uniform high coefficient bound is assumed.
Consumer: all-order raw and offset estimates of
`app:ch_response:cor:current-atoms`, `app:ch_waves:eq:WKB-amplitude-difference`. -/
theorem exists_derivativePolynomial_tameBounds {n N : ℕ} {Z : Type}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ) (M : ℝ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (Ω : Set (Euclidean n × Z)), IsOpen Ω → closedBall a ρ ⊆ Ω →
      ∀ (ξ : Euclidean n × Z → Euclidean n)
        (ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)),
      ContDiffOn ℝ ∞ ξ Ω → ContDiffOn ℝ ∞ ν₀ Ω → ContDiffOn ℝ ∞ ν₁ Ω →
      ContDiffOn ℝ ∞ V₀ Ω → ContDiffOn ℝ ∞ V₁ Ω →
      cNorm (closedBall a ρ) 0 ξ ≤ M → cNorm (closedBall a ρ) 0 ν₀ ≤ M →
      cNorm (closedBall a ρ) 0 ν₁ ≤ M → cNorm (closedBall a ρ) 0 V₀ ≤ M →
      cNorm (closedBall a ρ) 0 V₁ ≤ M →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∀ s,
      let H := 1 + cNorm (closedBall a ρ) (s+1) ξ +
        cNorm (closedBall a ρ) (s+1) ν₀ + cNorm (closedBall a ρ) (s+1) ν₁ +
        cNorm (closedBall a ρ) (s+1) V₀ + cNorm (closedBall a ρ) (s+1) V₁
      cNorm (closedBall a ρ) s (fun w ↦ -(normalTensor n N (ξ w) (ν₀ w))) ≤ C s * H ∧
      cNorm (closedBall a ρ) s (derivativePolynomial τ ξ ν₀ ν₁ V₀ V₁) ≤ C s * H ∧
      cNorm (closedBall a ρ) s (derivativeError τ ξ ν₀ ν₁ V₀ V₁) ≤ τ * C s * H := by
  obtain ⟨D, hD, htensor⟩ :=
    RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.exists_smoothPair_cNorm_bounds
      a hρ M M (fun p ↦ normalTensor n N p.1 p.2) (normalTensor n N).isBoundedBilinearMap.contDiff
  let E := ‖RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N‖
  let C := fun s : ℕ ↦ (s+1 : ℝ) * (1 + 4 * D s + 4 * E)
  have hC (s : ℕ) : 0 < C s := by
    have := hD s
    have : 0 ≤ E := norm_nonneg (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N)
    dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ hKΩ ξ ν₀ ν₁ V₀ V₁ hξ hν₀ hν₁ hV₀ hV₁ hξM hν₀M hν₁M hV₀M hV₁M τ hτ hτ1 s
  dsimp only
  let K := closedBall a ρ
  let H := 1 + cNorm K (s+1) ξ + cNorm K (s+1) ν₀ + cNorm K (s+1) ν₁ +
    cNorm K (s+1) V₀ + cNorm K (s+1) V₁
  have hns (f : Euclidean n × Z → EuclideanSpace ℂ (Fin N)) : 0 ≤ cNorm K (s+1) f :=
    cNorm_nonneg _ _ _
  have hξs : 0 ≤ cNorm K (s+1) ξ := cNorm_nonneg _ _ _
  have hH : 0 ≤ H := by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₀, hns V₁]
  have hE : 0 ≤ E := norm_nonneg (RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N)
  have h0 : cNorm K (s+1) ν₀ ≤ H := by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₀, hns V₁]
  have h1 : cNorm K (s+1) ν₁ ≤ H := by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₀, hns V₁]
  have hv0 : cNorm K (s+1) V₀ ≤ H := by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₀, hns V₁]
  have hv1 : cNorm K (s+1) V₁ ≤ H := by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₀, hns V₁]
  have ht (v : Euclidean n × Z → EuclideanSpace ℂ (Fin N)) (hv : ContDiffOn ℝ ∞ v Ω)
      (hvM : cNorm K 0 v ≤ M) (hvH : 1 + cNorm K (s+1) ξ + cNorm K (s+1) v ≤ H)
      (j : ℕ) (hj : j ≤ s) (w) (hw : w ∈ K) :
      ‖iteratedFDeriv ℝ j (fun y ↦ normalTensor n N (ξ y) (v y)) w‖ ≤ D s * H := by
    have hh := htensor Ω hΩ hKΩ ξ v hξ hv hξM hvM s
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ ((contDiffOn_normalTensor hξ hv).contDiffAt
        (hΩ.mem_nhds (hKΩ hy))).of_le (by simp)) hw hj).trans
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (hD s).le
    linarith only [hvH, cNorm_mono_order (s := K) (f := ξ) (Nat.le_succ s),
      cNorm_mono_order (s := K) (f := v) (Nat.le_succ s)]
  have ht0 := ht ν₀ hν₀ hν₀M (by dsimp [H]; linarith [hns ν₁, hns V₀, hns V₁])
  have ht1 := ht ν₁ hν₁ hν₁M (by dsimp [H]; linarith [hns ν₀, hns V₀, hns V₁])
  have htv0 := ht V₀ hV₀ hV₀M (by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₁])
  have htv1 := ht V₁ hV₁ hV₁M (by dsimp [H]; linarith [hns ν₀, hns ν₁, hns V₀])
  have hj (v : Euclidean n × Z → EuclideanSpace ℂ (Fin N)) (hv : ContDiffOn ℝ ∞ v Ω)
      (hvH : cNorm K (s+1) v ≤ H) (j : ℕ) (hj : j ≤ s) (w) (hw : w ∈ K) :
      ‖iteratedFDeriv ℝ (j+1) v w‖ ≤ H :=
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hv.contDiffAt (hΩ.mem_nhds (hKΩ hy))).of_le (by simp))
      hw (Nat.add_le_add_right hj 1)).trans hvH
  have herr (j : ℕ) (hjs : j ≤ s) (w) (hw : w ∈ K) :
      ‖iteratedFDeriv ℝ j (derivativeError τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤
        τ * (3 * D s + 4 * E) * H := by
    have hc1 := jet_correctionOne_le hΩ hξ hν₀ hν₁ hV₀ (hKΩ hw) j
    have hc2 := jet_correctionTwo_le hΩ hξ hν₁ hV₀ hV₁ (hKΩ hw) j
    have hc1' : ‖iteratedFDeriv ℝ j (correctionOne ξ ν₀ ν₁ V₀) w‖ ≤ (2 * D s + E) * H := by
      apply hc1.trans
      have hh := mul_le_mul_of_nonneg_left (hj ν₀ hν₀ h0 j hjs w hw) hE
      nlinarith only [hh, ht1 j hjs w hw, htv0 j hjs w hw]
    have hc2' : ‖iteratedFDeriv ℝ j (correctionTwo ξ ν₁ V₀ V₁) w‖ ≤ (D s + 2 * E) * H := by
      apply hc2.trans
      have hh1 := mul_le_mul_of_nonneg_left (hj ν₁ hν₁ h1 j hjs w hw) hE
      have hh2 := mul_le_mul_of_nonneg_left (hj V₀ hV₀ hv0 j hjs w hw) hE
      nlinarith only [hh1, hh2, htv1 j hjs w hw]
    have hτ2 : τ^2 ≤ τ := by nlinarith
    have hτ3 : τ^3 ≤ τ := by nlinarith [mul_nonneg hτ (sub_nonneg.mpr hτ2)]
    apply (jet_derivativeError_le hΩ hξ hν₀ hν₁ hV₀ hV₁ (hKΩ hw) hτ j).trans
    calc
      _ ≤ τ * ((2 * D s + E) * H) + τ * ((D s + 2 * E) * H) + τ * (E * H) := by
        gcongr
        exact hj V₁ hV₁ hv1 j hjs w hw
      _ = _ := by ring
  have hlead (j : ℕ) (hjs : j ≤ s) (w) (hw : w ∈ K) :
      ‖iteratedFDeriv ℝ j (fun y ↦ -(normalTensor n N (ξ y) (ν₀ y))) w‖ ≤ D s * H := by
    change ‖iteratedFDeriv ℝ j (-(fun y ↦ normalTensor n N (ξ y) (ν₀ y))) w‖ ≤ _
    rw [iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
    exact ht0 j hjs w hw
  have hraw (j : ℕ) (hjs : j ≤ s) (w) (hw : w ∈ K) :
      ‖iteratedFDeriv ℝ j (derivativePolynomial τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤ (4 * D s + 4 * E) * H := by
    have hx := hΩ.mem_nhds (hKΩ hw)
    have he := (((contDiffOn_correctionOne hΩ hξ hν₀ hν₁ hV₀).const_smul (τ : ℂ)).add
      ((contDiffOn_correctionTwo hΩ hξ hν₁ hV₀ hV₁).const_smul ((τ : ℂ)^2))).add
        ((contDiffOn_physicalJacobian hΩ hV₁).const_smul ((τ : ℂ)^3))
    have hh := jet_add_le ((contDiffOn_normalTensor hξ hν₀).neg.contDiffAt hx) (he.contDiffAt hx) j
    apply hh.trans
    have hp : 0 ≤ (3 * D s + 4 * E) * H := by have := hD s; positivity
    have hsmall := mul_le_mul_of_nonneg_right hτ1 hp
    change ‖iteratedFDeriv ℝ j (fun y ↦ -(normalTensor n N (ξ y) (ν₀ y))) w‖ +
      ‖iteratedFDeriv ℝ j (derivativeError τ ξ ν₀ ν₁ V₀ V₁) w‖ ≤ _
    nlinarith only [hlead j hjs w hw, herr j hjs w hw, hsmall]
  have hsum (f : Euclidean n × Z → Matrix (Fin N) (Fin n) ℂ) (A : ℝ) (hA : 0 ≤ A)
      (hf : ∀ j ≤ s, ∀ w ∈ K, ‖iteratedFDeriv ℝ j f w‖ ≤ A) :
      cNorm K s f ≤ (s+1 : ℝ) * A := by
    simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ hA) hf
  refine ⟨?_, ?_, ?_⟩
  · apply (hsum _ _ (mul_nonneg (hD s).le hH) hlead).trans
    change (s+1 : ℝ) * (D s * H) ≤ C s * H
    dsimp [C]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith only [hD s, hE]) hH
  · apply (hsum _ _ (by have := hD s; positivity) hraw).trans
    change (s+1 : ℝ) * ((4 * D s + 4 * E) * H) ≤ C s * H
    dsimp [C]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hH
  · apply (hsum _ _ (by have := hD s; positivity) herr).trans
    change (s+1 : ℝ) * (τ * (3 * D s + 4 * E) * H) ≤ τ * C s * H
    calc
      _ = τ * ((s+1 : ℝ) * (3 * D s + 4 * E)) * H := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hH
        apply mul_le_mul_of_nonneg_left _ hτ
        exact mul_le_mul_of_nonneg_left (by linarith only [hD s]) (by positivity)

end JanetCartan.CorrectedAtoms
