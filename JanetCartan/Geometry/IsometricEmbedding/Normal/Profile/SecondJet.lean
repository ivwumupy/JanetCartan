module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget

/-!
# One-high bounds for functions of the second jet

For `app:ch_background:eq:bg-frame-tame`, the actual first and second derivatives
form a smooth jet field. Closed-ball interpolation gives a one-high bound with
reserve two for any coefficient smooth near a compact jet range. Concrete
geometric coefficient formulas must still be identified and proved smooth.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open JanetCartan.CompositionBounds

namespace JanetCartan.GeometricProfile

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The first and second derivative data in `app:ch_background:eq:bg-frame-tame`.
No symmetry or immersion condition is built into this ambient jet space. -/
abbrev SecondJet (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)

/-- The actual second jet used in `app:ch_background:eq:bg-frame-tame`. -/
def secondJet (f : E → F) (x : E) : SecondJet E F :=
  (fderiv ℝ f x, fderiv ℝ (fderiv ℝ f) x)

/-- `app:ch_background:eq:bg-frame-tame`: smoothness of the actual second jet. -/
theorem contDiff_secondJet {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (secondJet f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact hd.prodMk (hd.fderiv_right (by simp))

/-- `app:ch_background:eq:bg-frame-tame`: forming the jet costs exactly two
orders; the harmless factor depends only on the differentiated order. -/
theorem cNorm_secondJet_le {s : Set E} (hs : IsCompact s) (r : ℕ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    cNorm s r (secondJet f) ≤ (r + 1 : ℝ) * cNorm s (r + 2) f := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  have h := cNorm_le_sum (s := s) (r := r) (f := secondJet f)
    (B := fun _ ↦ cNorm s (r + 2) f) (fun _ _ ↦ cNorm_nonneg _ _ _) (by
      intro j hj x hx
      change ‖iteratedFDeriv ℝ j (fun y ↦ (fderiv ℝ f y,
        fderiv ℝ (fderiv ℝ f) y)) x‖ ≤ _
      rw [iteratedFDeriv_prodMk hd.contDiffAt hdd.contDiffAt
        (by simp : (j : ℕ∞ω) ≤ ∞)]
      rw [ContinuousMultilinearMap.opNorm_prod]
      apply max_le
      · exact (norm_iteratedFDeriv_le_cNorm hs (contDiff_infty.mp hd r) hx hj).trans
          ((cNorm_fderiv_le s r f).trans (cNorm_mono_order (by omega)))
      · exact (norm_iteratedFDeriv_le_cNorm hs (contDiff_infty.mp hdd r) hx hj).trans
          ((cNorm_fderiv_le s r (fderiv ℝ f)).trans (cNorm_fderiv_le s (r + 1) f)))
  simpa using h

/-- `app:ch_background:eq:bg-frame-tame`: scalar interpolation is discharged,
and the compact jet range supplies every low-order bound. This is a chain-rule
helper, not an assumed package of geometric estimates. -/
theorem exists_cNorm_secondJet_comp_le_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {t : Set (SecondJet E F)} (ht : IsCompact t)
    {r : ℕ} {g : SecondJet E F → G} (hg : ∀ J ∈ t, ContDiffAt ℝ r g J) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (g ∘ secondJet f) ≤
          C * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    x hρ ht (le_refl r) hg
  refine ⟨C * (r + 1), mul_pos hC (by positivity), fun f hf hft ↦ ?_⟩
  apply (hbound _ (contDiff_secondJet hf) hft).trans
  have hjet := cNorm_secondJet_le (isCompact_closedBall x ρ) r hf
  have hh : 1 + cNorm (Metric.closedBall x ρ) r (secondJet f) ≤
      (r + 1 : ℝ) * (1 + cNorm (Metric.closedBall x ρ) (r + 2) f) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hC.le

/-- `app:cor:fixed-profile-transfer`: the second-jet chain-rule estimate transfers
profiles with one order-independent reserve of two. -/
theorem exists_secondJet_comp_profiles_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {t : Set (SecondJet E F)} (ht : IsCompact t)
    {g : SecondJet E F → G} (hg : ∀ J ∈ t, ContDiffAt ℝ ∞ g J) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
      ∀ (R ν : ℕ) (T : ℝ) (A : ℕ → ℝ),
        HasDerivativeProfile (Metric.closedBall x ρ) f R T A →
        1 ≤ T → (∀ r, 0 ≤ A r) → 2 + ν ≤ R →
        HasDerivativeProfile (Metric.closedBall x ρ) (g ∘ secondJet f) ν T
          (fun r ↦ C r * (1 + A (r + 2))) := by
  have hbound := fun (r : ℕ) ↦ exists_cNorm_secondJet_comp_le_closedBall x hρ ht
    (fun J hJ ↦ (hg J hJ).of_le (by simp : (r : ℕ∞ω) ≤ ∞))
  choose C hC hCf using hbound
  refine ⟨C, hC, ?_⟩
  intro f hf hft R ν T A hp hT hA hloss
  exact hp.transfer hT hA (fun r ↦ (hC r).le) hloss (fun r ↦ hCf r f hf hft)

/-- `app:ch_background:eq:bg-frame-tame`: locally equal coefficient formulas have
identical ambient derivative seminorms, including at the boundary of a closed ball. -/
theorem cNorm_eq_of_eventuallyEq {s : Set E} {f g : E → F}
    (h : ∀ x ∈ s, f =ᶠ[𝓝 x] g) (r : ℕ) : cNorm s r f = cNorm s r g := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro x hx
  exact congrArg norm ((h x hx).iteratedFDeriv ℝ j |>.eq_of_nhds)

end JanetCartan.GeometricProfile
