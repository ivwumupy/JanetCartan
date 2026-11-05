module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.Field

/-!
# Fixed-shift tame bound for actual reconstruction

The geometric reconstruction part of `app:ch_waves:eq:joint-tame`, with
one high norm of the immersion or covector and reserve two at every order.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius
open scoped JanetCartan.NormalRankStability JanetCartan.TensorFrobenius

namespace JanetCartan.GeometricProfile
open JanetCartan.CompositionBounds

/-- `app:ch_waves:eq:joint-tame`: the joint reconstruction jet is smooth. -/
theorem contDiff_reconstructionJet {n N : ℕ} {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {u : Euclidean n → Euclidean n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (reconstructionJet f u) :=
  (contDiff_secondJet hf).prodMk (hu.prodMk (hu.fderiv_right (by simp)))

private theorem cNorm_pair_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} (hs : IsCompact s) (r : ℕ) {f : E → F} {g : E → G}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    cNorm s r (fun x ↦ (f x, g x)) ≤ (r + 1 : ℝ) * (cNorm s r f + cNorm s r g) := by
  have h := cNorm_le_sum (s := s) (r := r) (f := fun x ↦ (f x, g x))
    (B := fun _ ↦ cNorm s r f + cNorm s r g)
    (fun _ _ ↦ add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)) (by
      intro j hj x hx
      rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt
        (by simp : (j : ℕ∞ω) ≤ ∞), ContinuousMultilinearMap.opNorm_prod]
      exact max_le
        ((norm_iteratedFDeriv_le_cNorm hs (contDiff_infty.mp hf r) hx hj).trans
          (le_add_of_nonneg_right (cNorm_nonneg _ _ _)))
        ((norm_iteratedFDeriv_le_cNorm hs (contDiff_infty.mp hg r) hx hj).trans
          (le_add_of_nonneg_left (cNorm_nonneg _ _ _))))
  simpa [mul_add] using h

/-- `app:ch_waves:eq:joint-tame`: forming the joint jet costs two orders of
the immersion and one of the covector, with no product of high norms. -/
theorem cNorm_reconstructionJet_le {n N : ℕ} {s : Set (Euclidean n)}
    (hs : IsCompact s) (r : ℕ) {f : Euclidean n → Euclidean N}
    (hf : ContDiff ℝ ∞ f) {u : Euclidean n → Euclidean n} (hu : ContDiff ℝ ∞ u) :
    cNorm s r (reconstructionJet f u) ≤
      (2 * (r + 1 : ℝ) ^ 2) * (cNorm s (r + 2) f + cNorm s (r + 1) u) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hpair := cNorm_pair_le hs r hu hd
  have hjet := cNorm_secondJet_le hs r hf
  have hu0 : cNorm s r u ≤ cNorm s (r + 1) u := cNorm_mono_order (by omega)
  have hu1 := cNorm_fderiv_le s r u
  have hlow : cNorm s r (fun x ↦ (u x, fderiv ℝ u x)) ≤
      (r + 1 : ℝ) * (2 * cNorm s (r + 1) u) := by
    apply hpair.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h := cNorm_pair_le hs r (contDiff_secondJet hf) (hu.prodMk hd)
  apply h.trans
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hjet hlow)
    (show (0 : ℝ) ≤ r + 1 by positivity)
  apply hsum.trans
  nlinarith [mul_nonneg (sq_nonneg (r + 1 : ℝ)) (cNorm_nonneg s (r + 2) f)]

/-- `app:ch_waves:eq:joint-tame`: the actual reconstruction has one high
norm of `f` or `u`. The compact joint low-jet range fixes all constants and
geometric gaps. The reserve two is independent of `r`. -/
theorem exists_cNorm_reconstruction_le_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (ReconstructionJet n N)} (ht : IsCompact t)
    (htimm : ∀ q ∈ t, Function.Injective q.1.1)
    (htrank : ∀ q ∈ t, Set.range (secondJetNormalMap q.1) =
      ((LinearMap.range q.1.1.toLinearMap)ᗮ : Set (Euclidean N))) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Euclidean n → Euclidean N) (u : Euclidean n → Euclidean n),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ u →
      Set.MapsTo (reconstructionJet f u) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r
          (LeadingWave.reconstruction f (AmbientResponse.canonicalNormalCompletion f) u) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f +
            cNorm (Metric.closedBall x ρ) (r + 1) u) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    x hρ ht (le_refl r) (fun q hq ↦
      (contDiffAt_reconstructionJetValue (htimm q hq) (htrank q hq)).of_le
        (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C * (2 * (r + 1 : ℝ) ^ 2), mul_pos hC (by positivity), ?_⟩
  intro f u hf hu hft
  have he : cNorm (Metric.closedBall x ρ) r
      (LeadingWave.reconstruction f (AmbientResponse.canonicalNormalCompletion f) u) =
      cNorm (Metric.closedBall x ρ) r (reconstructionJetValue ∘ reconstructionJet f u) := by
    apply cNorm_eq_of_eventuallyEq
    intro y hy
    have hi : Function.Injective (fderiv ℝ f y) := htimm _ (hft hy)
    have hr : Set.range (normalMap f y) = (normalSpace f y : Set (Euclidean N)) := by
      have hh := htrank _ (hft hy)
      change Set.range (secondJetNormalMap (secondJet f y)) = _ at hh
      rw [secondJetNormalMap_eq hf hi] at hh
      exact hh
    have ho := NormalRankStability.isOpen_fullNormalRank_immersionDomain
      isOpen_univ (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffOn
    have hev := ho.mem_nhds (show y ∈ {z | z ∈ immersionDomain f Set.univ ∧
        Set.range (normalMap f z) = (normalSpace f z : Set (Euclidean N))} from
      ⟨⟨Set.mem_univ y, hi⟩, hr⟩)
    filter_upwards [hev] with z hz
    exact (reconstructionJetValue_eq hf hu hz.1.2 hz.2).symm
  rw [he]
  apply (hbound _ (contDiff_reconstructionJet hf hu) hft).trans
  have hj := cNorm_reconstructionJet_le (isCompact_closedBall x ρ) r hf hu
  have hone : (1 : ℝ) ≤ 2 * (r + 1 : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have hh : 1 + cNorm (Metric.closedBall x ρ) r (reconstructionJet f u) ≤
      (2 * (r + 1 : ℝ) ^ 2) * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f +
        cNorm (Metric.closedBall x ρ) (r + 1) u) := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hC.le

end JanetCartan.GeometricProfile
