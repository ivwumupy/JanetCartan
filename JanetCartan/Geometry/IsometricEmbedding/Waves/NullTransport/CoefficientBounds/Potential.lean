module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.PotentialFormula

/-!
# Joint one-high bound for the potential formula

For `app:ch_waves:eq:joint-tame`, compact ranges are chosen from the fixed low
input budget and the primitive metric/normal and adapted-denominator gaps.
The first derivative of the nullvector costs one input derivative. The
immersion second jet and the carrier input will be instantiated by the actual
producer, with one fixed total reserve five.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.CoefficientBounds
open ProjectedStressFrame GeometricProfile

variable {n N : ℕ}

/-- The potential formula has one high input norm. All low ranges and gaps
are fixed before the varying fields; the actual construction supplies them
from primitive hypotheses (`app:ch_waves:eq:joint-tame`). -/
theorem exists_potential_formula_bounds
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (ν : Euclidean n) (r c : Fin n) {L ε κmet : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hκmet : 0 < κmet) (M R : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n × Euclidean 3)), IsOpen Ω → closedBall a ρ ⊆ Ω →
      ∀ (f : Euclidean n × Euclidean 3 → Input n)
        (J : Euclidean n × Euclidean 3 → StressJet n N),
      ContDiffOn ℝ ∞ f Ω → ContDiffOn ℝ ∞ J Ω →
      cNorm (closedBall a ρ) 1 f ≤ L →
      (∀ w ∈ closedBall a ρ, ε ≤ |denominator ν r c (f w)|) →
      MapsTo J (closedBall a ρ) (admissibleStressJets n N M κmet R) →
      ∀ m, cNorm (closedBall a ρ) m
        (fun w ↦ potentialFormula ν r c (f w, fderiv ℝ (right c ∘ f) w, J w)) ≤
          C m * (1 + cNorm (closedBall a ρ) (m + 1) f + cNorm (closedBall a ρ) m J) := by
  obtain ⟨B, A, _, hA, hprincipal⟩ := exists_principal_formula_bounds a hρ ν r c hL hε
  let Lk := A 1 * (1 + L)
  let t : Set (PotentialJet n N) := admissibleInputs ν r c L ε ×ˢ
    (closedBall 0 Lk ×ˢ admissibleStressJets n N M κmet R)
  have ht : IsCompact t := (compact_admissibleInputs ν r c L ε).prod
    ((isCompact_closedBall 0 Lk).prod (isCompact_admissibleStressJets M hκmet R))
  choose C hC hb using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a hρ ht
      (r := m) (k := m) le_rfl (g := potentialFormula ν r c)
      (fun p hp ↦ (smoothAt_potentialFormula ν r c
        (firstJetMetric_isUnit_of_gap hκmet hp.2.2.2.1)
        (abs_pos.mp (hε.trans_le hp.1.2))).of_le (by simp))
  refine ⟨fun m ↦ C m * (1 + (m + 1) + (m + 1) ^ 2 * (A (m + 1) + 1)),
    fun m ↦ mul_pos (hC m) (by have := hA (m + 1); positivity), ?_⟩
  intro Ω hΩ hball f J hf hJ hlow hgap hmap m
  let k := right c ∘ f
  have hk : ContDiffOn ℝ ∞ k Ω := (smooth_right c).comp_contDiffOn hf
  have hdk := hk.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hright (j : ℕ) : cNorm (closedBall a ρ) j k ≤
      A j * (1 + cNorm (closedBall a ρ) j f) := by
    have hh := (hprincipal Ω hΩ hball f hf hlow hgap).2 j
    have := cNorm_nonneg (closedBall a ρ) j (left r ∘ f)
    have := cNorm_nonneg (closedBall a ρ) j (denominator ν r c ∘ f)
    have := cNorm_nonneg (closedBall a ρ) j (fun w ↦ (denominator ν r c (f w))⁻¹)
    have := cNorm_nonneg (closedBall a ρ) j (direction ν r c ∘ f)
    dsimp only [k]
    linarith
  have hklow : cNorm (closedBall a ρ) 1 k ≤ Lk := (hright 1).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hlow) (hA 1).le)
  let v : Euclidean n × Euclidean 3 → PotentialJet n N :=
    fun w ↦ (f w, fderiv ℝ k w, J w)
  have hv : ContDiffOn ℝ ∞ v Ω := hf.prodMk (hdk.prodMk hJ)
  have hvt : MapsTo v (closedBall a ρ) t := by
    intro w hw
    have hfv : ‖f w‖ ≤ cNorm (closedBall a ρ) 1 f := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
            (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 1)
    have hkv : ‖fderiv ℝ k w‖ ≤ cNorm (closedBall a ρ) 0 (fderiv ℝ k) := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ (hdk.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
            (by simp : (0 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 0)
    exact ⟨⟨mem_closedBall_zero_iff.mpr (hfv.trans hlow), hgap w hw⟩,
      mem_closedBall_zero_iff.mpr
        (hkv.trans ((cNorm_fderiv_le (closedBall a ρ) 0 k).trans hklow)), hmap hw⟩
  have hout := hb m Ω hΩ hball v hv hvt
  have hp₁ := cNorm_pair_le a m hΩ hball hf (hdk.prodMk hJ)
  have hp₂ := cNorm_pair_le a m hΩ hball hdk hJ
  have hder := (cNorm_fderiv_le (closedBall a ρ) m k).trans (hright (m + 1))
  let H := 1 + cNorm (closedBall a ρ) (m + 1) f + cNorm (closedBall a ρ) m J
  have hfH : cNorm (closedBall a ρ) m f ≤ H :=
    (cNorm_mono_order (Nat.le_succ m)).trans (by dsimp [H]; linarith [cNorm_nonneg (closedBall a ρ) m J])
  have hJH : cNorm (closedBall a ρ) m J ≤ H := by
    dsimp [H]; linarith [cNorm_nonneg (closedBall a ρ) (m + 1) f]
  have hdH : cNorm (closedBall a ρ) m (fderiv ℝ k) ≤ A (m + 1) * H := hder.trans
    (mul_le_mul_of_nonneg_left (by dsimp [H]; linarith [cNorm_nonneg (closedBall a ρ) m J])
      (hA (m + 1)).le)
  have hp₂H : cNorm (closedBall a ρ) m (fun w ↦ (fderiv ℝ k w, J w)) ≤
      (m + 1 : ℝ) * (A (m + 1) * H + H) := hp₂.trans
    (mul_le_mul_of_nonneg_left (add_le_add hdH hJH) (by positivity))
  have hp₁H : cNorm (closedBall a ρ) m v ≤
      ((m + 1 : ℝ) + (m + 1) ^ 2 * (A (m + 1) + 1)) * H := by
    exact (hp₁.trans (mul_le_mul_of_nonneg_left (add_le_add hfH hp₂H)
      (by positivity))).trans_eq (by ring)
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (closedBall a ρ) (m + 1) f, cNorm_nonneg (closedBall a ρ) m J]
  have htotal : 1 + cNorm (closedBall a ρ) m v ≤
      (1 + (m + 1 : ℝ) + (m + 1) ^ 2 * (A (m + 1) + 1)) * H := by
    nlinarith only [hp₁H, hH]
  exact hout.trans ((mul_le_mul_of_nonneg_left htotal (hC m).le).trans_eq (by ring))

end JanetCartan.NullTransport.CoefficientBounds
