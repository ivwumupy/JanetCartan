module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity.Calculus

/-!
# Primitive evaluations at the two genuine inverse points

For `app:ch_osc:prop:osc-normal`, Step 4', the coefficient functions vary
independently of the inverse points. The reference Jacobian is fixed, while
both sets of masks and fields are quantified after the constants. Thus the
bounds remain uniform for shell-rescaled high masks.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity
open ContinuumNormalReduction.TransportSymbol HamiltonPhase.CompositionContinuity
variable {E F G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Fixed shell coordinate evaluations at moving inverse points. Neither an
angular nor a radial composed bound is assumed. Consumer: the primitive
substitution of `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_fixed_evaluation_bounds
    {Q : Set E} {K : Set F} (hQ : IsCompact Q) (hK : IsCompact K)
    {e : F → G} (he : ∀ x ∈ K, ContDiffAt ℝ ∞ e x) (s : ℕ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (g g₀ : E → F) (d : ℝ), 0 ≤ d →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ g p) → (∀ p ∈ Q, ContDiffAt ℝ ∞ g₀ p) →
      MapsTo g Q K → MapsTo g₀ Q K → cNorm Q s g ≤ M → cNorm Q s g₀ ≤ M →
      cNorm Q s (g - g₀) ≤ d →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ (e ∘ g) p ∧ ContDiffAt ℝ ∞ (e ∘ g₀) p) ∧
      cNorm Q s (e ∘ g) ≤ C ∧ cNorm Q s (e ∘ g₀) ≤ C ∧
      cNorm Q s (e ∘ g - e ∘ g₀) ≤ C * d := by
  obtain ⟨R, hR, hb⟩ := exists_cNorm_comp_sub_le_fixed_reference hQ hK he s hM
  let P := compositionMultiplicity s * cNorm K s e * (1 + M) ^ s
  have hP : 0 ≤ P := by
    have hh := cNorm_nonneg K s e
    dsimp [P, compositionMultiplicity]
    positivity
  refine ⟨1 + R + P, by positivity, ?_⟩
  intro g g₀ d hd hg hg₀ hr hr₀ hm hm₀ hdiff
  refine ⟨fun p hp ↦ ⟨(he _ (hr hp)).comp p (hg p hp),
    (he _ (hr₀ hp)).comp p (hg₀ p hp)⟩, ?_, ?_, ?_⟩
  · exact (cNorm_comp_le_from_bounds hQ hK s he hg hr
      (cNorm_nonneg _ _ _) le_rfl hm).trans (by change P ≤ _; linarith)
  · exact (cNorm_comp_le_from_bounds hQ hK s he hg₀ hr₀
      (cNorm_nonneg _ _ _) le_rfl hm₀).trans (by change P ≤ _; linarith)
  · exact (hb e g g₀ d hd he hg hg₀ hr hr₀ hm hm₀
      (by simpa only [sub_self, cNorm_zero] using hd) hdiff).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd)

/-- Primitive differences on `D.carrier` and differences of the actual inverse
coordinates imply the two substituted primitive bounds. The reference order
`s+1` norm is used only to compare evaluations at different points. Both
coefficients occur after the constant, including shell-rescaled high masks.
Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_moving_primitive_evaluation_bounds [FiniteDimensional ℝ G]
    (D : PrimitiveNormChart G) {Q : Set E} {K : Set F}
    (hQ : IsCompact Q) (hK : IsCompact K)
    {e : F → G} (he : ∀ x ∈ K, ContDiffAt ℝ ∞ e x)
    (herange : MapsTo e K D.carrier) (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (f f₀ : G → H) (g g₀ : E → F) (d : ℝ), 0 ≤ d →
      D.Controls s M (M + 1) 1 f → D.Controls (s + 1) M (M + 1) 1 f₀ →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ g p) → (∀ p ∈ Q, ContDiffAt ℝ ∞ g₀ p) →
      MapsTo g Q K → MapsTo g₀ Q K → cNorm Q s g ≤ M → cNorm Q s g₀ ≤ M →
      cNorm D.carrier s (f - f₀) ≤ d → cNorm Q s (g - g₀) ≤ d →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ (f ∘ e ∘ g) p ∧
        ContDiffAt ℝ ∞ (f₀ ∘ e ∘ g₀) p) ∧
      cNorm Q s (f ∘ e ∘ g) ≤ C ∧ cNorm Q s (f₀ ∘ e ∘ g₀) ≤ C ∧
      cNorm Q s (f ∘ e ∘ g - f₀ ∘ e ∘ g₀) ≤ C * d := by
  obtain ⟨R, hR, heval⟩ := exists_fixed_evaluation_bounds hQ hK he s hM
  let P := compositionMultiplicity s * M * (1 + R) ^ s
  let T := jetDifferenceConstant s M R * (1 + M) * (1 + R)
  have hP : 0 ≤ P := by dsimp [P, compositionMultiplicity]; positivity
  have hT : 0 ≤ T := by
    have hh := jetDifferenceConstant_nonneg s hM hR.le
    dsimp [T]; positivity
  refine ⟨1 + P + T, by positivity, ?_⟩
  intro f f₀ g g₀ d hd hf hf₀ hg hg₀ hr hr₀ hm hm₀ hfdiff hgdiff
  have he' := heval g g₀ d hd hg hg₀ hr hr₀ hm hm₀ hgdiff
  have houter : cNorm D.carrier s f ≤ M := by have hh := hf.high; linarith
  have houter₀ : cNorm D.carrier (s + 1) f₀ ≤ M := by have hh := hf₀.high; linarith
  have hf' : ∀ y ∈ D.carrier, ContDiffAt ℝ ∞ f y := fun y hy ↦
    hf.smooth.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hy))
  have hf₀' : ∀ y ∈ D.carrier, ContDiffAt ℝ ∞ f₀ y := fun y hy ↦
    hf₀.smooth.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hy))
  have hrg : MapsTo (e ∘ g) Q D.carrier := herange.comp hr
  have hrg₀ : MapsTo (e ∘ g₀) Q D.carrier := herange.comp hr₀
  refine ⟨fun p hp ↦ ⟨(hf' _ (hrg hp)).comp p (he'.1 p hp).1,
    (hf₀' _ (hrg₀ hp)).comp p (he'.1 p hp).2⟩, ?_, ?_, ?_⟩
  · exact (cNorm_comp_le_from_bounds hQ (isCompact_closedBall D.center D.radius) s
      hf' (fun p hp ↦ (he'.1 p hp).1) hrg hM
      houter he'.2.1).trans
        (by change P ≤ _; linarith)
  · exact (cNorm_comp_le_from_bounds hQ (isCompact_closedBall D.center D.radius) s
      hf₀' (fun p hp ↦ (he'.1 p hp).2) hrg₀ hM
      ((cNorm_mono_order (Nat.le_succ s)).trans houter₀) he'.2.2.1).trans
        (by change P ≤ _; linarith)
  · have hb := PrimitiveNormChart.cNorm_comp_sub_le D hQ s hM hR.le
      (show 0 ≤ (1 + R) * d by positivity) hf.smooth hf₀.smooth
      (fun p hp ↦ (he'.1 p hp).1) (fun p hp ↦ (he'.1 p hp).2)
      hrg hrg₀ houter₀ he'.2.1 he'.2.2.1
      (hfdiff.trans (by nlinarith)) (he'.2.2.2.trans (by nlinarith))
    exact hb.trans (by dsimp [T] at *; nlinarith)

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity
