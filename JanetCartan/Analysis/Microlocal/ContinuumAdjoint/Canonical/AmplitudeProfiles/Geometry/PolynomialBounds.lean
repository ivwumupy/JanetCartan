module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.Smoothness

/-!
# Tame polynomial assembly of the geometric component

The squared normal and the original quadratic detector are combined by one
fixed smooth polynomial on a bounded range. This preserves one high norm in
`app:ch_background:eq:bg-T`, instead of multiplying two high budgets.
Consumer: the primitive component estimate in `Geometry.ComponentBounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ProjectedStressFrame FullPhaseCharts.InverseEstimates

/-- Fixed-cutoff polynomial calculus for the exact geometric factor. The
normal and detector inputs here are supplied by `NormalBounds` and
`CanonicalBudgets.Detector` in the primitive assembly, not assumed there.
The estimate preserves their additive high norms (`bg-T`, `joint-tame`). -/
theorem exists_cNorm_geometricPolynomial_le {n N : ℕ}
    (z : Euclidean 3) {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (Mg Mq : ℝ) (j : Fin n) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ (O : Set (Euclidean n × CarrierParameter)), IsOpen O →
      closedBall (chartCenter z) σ ⊆ O →
      ∀ (g : Euclidean n × CarrierParameter → Euclidean N)
        (q : Euclidean n × CarrierParameter → Euclidean n),
      ContDiffOn ℝ ∞ g O → ContDiffOn ℝ ∞ q O →
      cNorm (closedBall (chartCenter z) σ) 0 g ≤ Mg →
      cNorm (closedBall (chartCenter z) σ) 0 q ≤ Mq →
      ∀ m, cNorm (closedBall (chartCenter z) σ) m
        (fun p ↦ ((FixedCutoffs.physical ha 1) p.1 *
          ‖chartBump z ha p • g p‖ ^ 2 * q p j : ℝ) :
          (Euclidean n × CarrierParameter) → ℂ) ≤
        B m * (1 + cNorm (closedBall (chartCenter z) σ) m g +
          cNorm (closedBall (chartCenter z) σ) m q) := by
  let L := closedBall (chartCenter (n := n) z) σ
  have hL : IsCompact L := isCompact_closedBall ..
  let f₀ := fun p : Euclidean n × CarrierParameter ↦
    ((FixedCutoffs.physical ha 1) p.1, chartBump z ha p)
  have hf₀ : ContDiff ℝ ∞ f₀ :=
    ((FixedCutoffs.physical ha 1).contDiff.comp contDiff_fst).prodMk
      (chartBump z ha).contDiff
  let poly : (ℝ × ℝ) × (Euclidean N × Euclidean n) → ℂ := fun p ↦
    (p.1.1 * ‖p.1.2 • p.2.1‖ ^ 2 * p.2.2 j : ℝ)
  have hpoly : ContDiff ℝ ∞ poly := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_fst.fst.mul ((contDiff_fst.snd.smul contDiff_snd.fst).norm_sq ℝ)).mul
        (contDiff_pi.mp (PiLp.contDiff_ofLp.comp contDiff_snd.snd) j))
  let R := cNorm L 0 f₀ + Mg + Mq
  choose C hC hcomp using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn (chartCenter (n := n) z) hσ
      (isCompact_closedBall (0 : (ℝ × ℝ) × (Euclidean N × Euclidean n)) R)
      (r := m) (k := m) le_rfl (g := poly) (fun _ _ ↦ hpoly.contDiffAt.of_le (by simp))
  let B := fun m ↦ C m * (1 + cNorm L m f₀)
  have hB m : 0 < B m := mul_pos (hC m) (by linarith [cNorm_nonneg L m f₀])
  refine ⟨B, hB, ?_⟩
  intro O hO hLO g q hg hq hg0 hq0
  let f := fun p ↦ (f₀ p, g p, q p)
  have hf : ContDiffOn ℝ ∞ f O := hf₀.contDiffOn.prodMk (hg.prodMk hq)
  have hpair (m) : cNorm L m f ≤ cNorm L m f₀ + cNorm L m g + cNorm L m q := by
    have hh := cNorm_prodMk_le_on L hL m
      (fun _ _ ↦ hf₀.contDiffAt.of_le (by simp))
      (fun p hp ↦ ((hg.prodMk hq).contDiffAt (hO.mem_nhds (hLO hp))).of_le (by simp))
    have hh' := cNorm_prodMk_le_on L hL m
      (fun p hp ↦ (hg.contDiffAt (hO.mem_nhds (hLO hp))).of_le (by simp))
      (fun p hp ↦ (hq.contDiffAt (hO.mem_nhds (hLO hp))).of_le (by simp))
    exact hh.trans (by linarith)
  have hmap : MapsTo f L (closedBall (0 : (ℝ × ℝ) × (Euclidean N × Euclidean n)) R) := by
    intro p hp
    rw [mem_closedBall_zero_iff]
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun p hp ↦ (hf.contDiffAt (hO.mem_nhds (hLO hp))).of_le
        (by simp : (0 : ℕ∞ω) ≤ ∞)) hp (le_refl 0)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans ((hpair 0).trans (by dsimp [R]; linarith))
  intro m
  have hh := (hcomp m O hO hLO f hf hmap).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hpair m)) (hC m).le)
  have hid : (poly ∘ f) = (fun p ↦ ((FixedCutoffs.physical ha 1) p.1 *
      ‖chartBump z ha p • g p‖ ^ 2 * q p j : ℝ) :
        (Euclidean n × CarrierParameter) → ℂ) := by
    funext p
    simp [poly, f, f₀]
  rw [hid] at hh
  apply hh.trans
  dsimp [B]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hC m).le
  nlinarith [cNorm_nonneg L m f₀, cNorm_nonneg L m g, cNorm_nonneg L m q,
    mul_nonneg (cNorm_nonneg L m f₀) (cNorm_nonneg L m g),
    mul_nonneg (cNorm_nonneg L m f₀) (cNorm_nonneg L m q)]

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
