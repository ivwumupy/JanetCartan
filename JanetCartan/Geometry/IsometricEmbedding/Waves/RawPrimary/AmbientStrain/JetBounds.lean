module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.CompactRange

/-!
# One-high bounds for the actual inverse-Gram residual

Tame composition differentiates the complete finite formula in
`app:ch_waves:eq:WKB-residual`. The only high inputs are the immersion
second jet and one derivative of the correction. The low correction budget
is supplied by `exists_fullCorrectionCovector_transport_bounds` at order one.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.RawPrimary.AmbientStrain
open ProjectedStressFrame GeometricProfile NullTransport.CoefficientBounds

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

/-- The inverse-Gram reconstruction has one high input with fixed losses
zero in the immersion jet and one in the correction. The constants are
chosen before the varying fields, frequency and scale
(`app:ch_waves:eq:WKB-strain`). -/
theorem exists_reconstructionJet_tame
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ) (M R L : ℝ)
    {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set (Euclidean n × Z)), IsOpen Ω → closedBall a ρ ⊆ Ω →
      ∀ (J : Euclidean n × Z → StressJet n N)
        (b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)),
        ContDiffOn ℝ ∞ J Ω → ContDiffOn ℝ ∞ b Ω →
        MapsTo J (closedBall a ρ) (admissibleStrainJets n N M κ R γ) →
        cNorm (closedBall a ρ) 1 b ≤ L →
        ∀ m, cNorm (closedBall a ρ) m
          (fun w ↦ reconstructionJet (J w, b w, fderiv ℝ b w)) ≤
          C m * (1 + cNorm (closedBall a ρ) m J +
            cNorm (closedBall a ρ) (m + 1) b) := by
  let t : Set (Jet n N Z) := admissibleStrainJets n N M κ R γ ×ˢ
    (closedBall 0 L ×ˢ closedBall 0 L)
  have ht : IsCompact t := (isCompact_admissibleStrainJets M R γ hκ).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  choose C hC hbnd using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a hρ ht
      (r := m) (k := m) le_rfl (g := @reconstructionJet n N Z _ _)
      (fun p hp ↦ (contDiffAt_reconstructionJet
        (isUnit_jetMetric_of_lower_bound hκ hp.1.1.2.1)
        (isUnit_jetAmbient_of_lower_bound hp.1.1.2.2)
        (firstJetMetric_isUnit_of_gap hκ hp.1.1.2.1)
        (stressGram_isUnit_of_energy _ hγ hp.1.2)).of_le (by simp))
  refine ⟨fun m ↦ C m * (1 + (m + 1) + 2 * (m + 1)^2),
    fun m ↦ mul_pos (hC m) (by positivity), ?_⟩
  intro Ω hΩ hball J b hJ hb hmap hlow m
  have hd := hb.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  let p : Euclidean n × Z → Jet n N Z := fun w ↦ (J w, b w, fderiv ℝ b w)
  have hp : ContDiffOn ℝ ∞ p Ω := hJ.prodMk (hb.prodMk hd)
  have hpt : MapsTo p (closedBall a ρ) t := by
    intro w hw
    have hv : ‖b w‖ ≤ cNorm (closedBall a ρ) 1 b := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ (hb.contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))
          hw (show 0 ≤ 1 by omega)
    have hdv : ‖fderiv ℝ b w‖ ≤ cNorm (closedBall a ρ) 0 (fderiv ℝ b) := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ (hd.contDiffAt (hΩ.mem_nhds (hball hy))).of_le (by simp))
          hw (show 0 ≤ 0 by omega)
    exact ⟨hmap hw, mem_closedBall_zero_iff.mpr (hv.trans hlow),
      mem_closedBall_zero_iff.mpr
        (hdv.trans ((cNorm_fderiv_le _ 0 b).trans hlow))⟩
  have hout := hbnd m Ω hΩ hball p hp hpt
  have hp₁ := cNorm_pair_le a m hΩ hball hJ (hb.prodMk hd)
  have hp₂ := cNorm_pair_le a m hΩ hball hb hd
  let S := 1 + cNorm (closedBall a ρ) m J + cNorm (closedBall a ρ) (m + 1) b
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [cNorm_nonneg (closedBall a ρ) m J,
      cNorm_nonneg (closedBall a ρ) (m + 1) b]
  have hJS : cNorm (closedBall a ρ) m J ≤ S := by
    dsimp [S]; linarith [cNorm_nonneg (closedBall a ρ) (m + 1) b]
  have hbS : cNorm (closedBall a ρ) (m + 1) b ≤ S := by
    dsimp [S]; linarith [cNorm_nonneg (closedBall a ρ) m J]
  have hb₀ := (cNorm_mono_order (f := b) (s := closedBall a ρ) (Nat.le_succ m)).trans hbS
  have hb₁ := (cNorm_fderiv_le (closedBall a ρ) m b).trans hbS
  have hpair : cNorm (closedBall a ρ) m (fun w ↦ (b w, fderiv ℝ b w)) ≤
      2 * (m + 1 : ℝ) * S :=
    (hp₂.trans (mul_le_mul_of_nonneg_left (add_le_add hb₀ hb₁)
      (by positivity))).trans_eq (by ring)
  have hpS : cNorm (closedBall a ρ) m p ≤
      ((m + 1 : ℝ) + 2 * (m + 1)^2) * S :=
    (hp₁.trans (mul_le_mul_of_nonneg_left (add_le_add hJS hpair)
      (by positivity))).trans_eq (by ring)
  exact hout.trans ((mul_le_mul_of_nonneg_left
    (show 1 + cNorm (closedBall a ρ) m p ≤
      (1 + (m + 1 : ℝ) + 2 * (m + 1)^2) * S by nlinarith only [hpS, hS])
      (hC m).le).trans_eq (by ring))

end JanetCartan.RawPrimary.AmbientStrain
