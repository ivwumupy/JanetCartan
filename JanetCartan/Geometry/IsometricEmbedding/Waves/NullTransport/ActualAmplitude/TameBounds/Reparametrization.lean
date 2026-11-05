module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Factor
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Fixed changes of variables for the amplitude estimates

The compact working cylinder of `app:ch_waves:eq:joint-tame` is a fixed linear
image of a ball. These estimates retain the actual operator norms of the
coordinate maps. Constants are uniform in the open smoothness neighborhoods,
which is needed for the literal integral and exponential.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.NullTransport.AmplitudeTame
open FullPhaseCharts.InverseEstimates

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The fixed coordinate cost for `app:ch_waves:eq:joint-tame`. -/
def linearNormCost (L : E →L[ℝ] F) (m : ℕ) : ℝ :=
  (m + 1 : ℝ) * (max 1 ‖L‖) ^ m

/-- Coordinate costs are positive, including at order zero
(`app:ch_waves:eq:joint-tame`). -/
theorem linearNormCost_pos (L : E →L[ℝ] F) (m : ℕ) : 0 < linearNormCost L m := by
  unfold linearNormCost
  positivity

/-- Linear pullback on the actual norms, used in both directions for the
adapted cylinder (`app:ch_waves:eq:joint-tame`). -/
theorem cNorm_comp_linear_le (L : E →L[ℝ] F) {S : Set E} {K U : Set F}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : F → G} (hf : ContDiffOn ℝ ∞ f U) (hm : MapsTo L S K) (m : ℕ) :
    cNorm S m (f ∘ L) ≤ linearNormCost L m * cNorm K m f := by
  have hb : ∀ j ≤ m, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ (max 1 ‖L‖) ^ m * cNorm K m f := by
    intro j hj x hx
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L hU hf
      (hKU (hm hx)) j).trans
    have hp : ‖L‖ ^ j ≤ (max 1 ‖L‖) ^ m :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    exact (mul_le_mul (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp))
      (hm hx) hj) hp (by positivity) (cNorm_nonneg _ _ _)).trans_eq (mul_comm _ _)
  simpa only [linearNormCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, ← mul_assoc] using
    cNorm_le_sum_of_bounds (fun _ _ ↦ mul_nonneg (by positivity) (cNorm_nonneg K m f)) hb

/-- Uniformity in the smoothness neighborhoods for the two varying maps in
`app:ch_waves:eq:joint-tame`. Compactly supported representatives preserve all
jets on the fixed balls, so the constant is chosen before these neighborhoods. -/
theorem exists_cNorm_comp_le_uniform_local
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (a : E) (b : F) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E) (V : Set F), IsOpen U → IsOpen V →
      closedBall a ρ ⊆ U → closedBall b σ ⊆ V →
      ∀ (f : E → F) (g : F → G), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g V →
      MapsTo f (closedBall a ρ) (closedBall b σ) →
      cNorm (closedBall a ρ) 1 f ≤ M → cNorm (closedBall b σ) 1 g ≤ N →
      cNorm (closedBall a ρ) m (g ∘ f) ≤
        C * (1 + cNorm (closedBall a ρ) (m + 2) f +
          cNorm (closedBall b σ) (m + 2) g) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_comp_le_joint_tame_closedBall (G := G)
    a b hρ hσ isOpen_univ isOpen_univ (subset_univ _) (subset_univ _) m hM hN
  refine ⟨C, hC, ?_⟩
  intro U V hU hV ha hb' f g hf hg hmap hfl hgl
  obtain ⟨f', hf', _, _, he⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a hρ hU ha hf
  obtain ⟨g', hg', _, _, he'⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall b hσ hV hb' hg
  have hfn (j) := GeometricProfile.cNorm_eq_of_eventuallyEq he j
  have hgn (j) := GeometricProfile.cNorm_eq_of_eventuallyEq he' j
  have hmap' : MapsTo f' (closedBall a ρ) (closedBall b σ) := by
    intro x hx
    rw [(he x hx).eq_of_nhds]
    exact hmap hx
  have hcomp : ∀ x ∈ closedBall a ρ, g' ∘ f' =ᶠ[𝓝 x] g ∘ f := by
    intro x hx
    exact ((he x hx).fun_comp g').trans
      ((he' (f x) (hmap hx)).comp_tendsto
        (hf.contDiffAt (hU.mem_nhds (ha hx))).continuousAt)
  have hh := hb f' g' hf'.contDiffOn hg'.contDiffOn hmap'
    (by simpa only [hfn] using hfl) (by simpa only [hgn] using hgl)
  simpa only [hfn, hgn, GeometricProfile.cNorm_eq_of_eventuallyEq hcomp m] using hh

/-- The nullvector product estimate is uniform in its smoothness neighborhood
(`app:ch_waves:eq:joint-tame`). No bound on a product is an input. -/
theorem exists_cNorm_smul_le_uniform_local
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (a : E) {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E), IsOpen U → closedBall a ρ ⊆ U →
      ∀ (f : E → ℝ) (g : E → F), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      cNorm (closedBall a ρ) 1 f ≤ M → cNorm (closedBall a ρ) 1 g ≤ N →
      cNorm (closedBall a ρ) m (fun x ↦ f x • g x) ≤
        C * (1 + cNorm (closedBall a ρ) (m + 2) f +
          cNorm (closedBall a ρ) (m + 2) g) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_smul_le_joint_tame_closedBall (F := F)
    a hρ isOpen_univ (subset_univ _) m hM hN
  refine ⟨C, hC, ?_⟩
  intro U hU ha f g hf hg hfl hgl
  obtain ⟨f', hf', _, _, he⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a hρ hU ha hf
  obtain ⟨g', hg', _, _, he'⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a hρ hU ha hg
  have hfn (j) := GeometricProfile.cNorm_eq_of_eventuallyEq he j
  have hgn (j) := GeometricProfile.cNorm_eq_of_eventuallyEq he' j
  have hprod : ∀ x ∈ closedBall a ρ,
      (fun y ↦ f' y • g' y) =ᶠ[𝓝 x] (fun y ↦ f y • g y) := by
    intro x hx
    filter_upwards [he x hx, he' x hx] with y hy hy'
    rw [hy, hy']
  have hh := hb f' g' hf'.contDiffOn hg'.contDiffOn
    (by simpa only [hfn] using hfl) (by simpa only [hgn] using hgl)
  simpa only [hfn, hgn, GeometricProfile.cNorm_eq_of_eventuallyEq hprod m] using hh

end JanetCartan.NullTransport.AmplitudeTame
