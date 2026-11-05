module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.InverseStability.Assembly

/-!
# Finite-order continuity of buffered inverse coordinates

For `app:lem:common-hamilton-phase` and `app:lem:buffered-inverse-stability`,
actual smooth inverses on a common open target depend continuously in `C^m`
on the forward map in `C^m`. The half gap is the independent fixed low-order
geometric neighborhood, not a bound on inverse derivatives.

The ball specialization uses a convex source ball of radius `3*r`, and controls
the forward seminorm on the compact radius-`2*r` ball containing both inverse
images. The parent construction instantiates these inputs from
`exists_common_buffered_symbol_charts` or `exists_commonBufferedHamiltonPhases`
and proves forward closeness. Different reference chart choices can be
identified by `ProjectionChart.coordinates_eq_of_projection_eq`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.HamiltonPhase
namespace InverseContinuity

private theorem cNorm_postLinear_le
    {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set P} (hK : IsCompact K) (n : ℕ) (L : F →L[ℝ] G)
    {f : P → F} (hf : ∀ x ∈ K, ContDiffAt ℝ n f x) :
    cNorm K n (L ∘ f) ≤ ‖L‖ * cNorm K n f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun k _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg K k f))
  intro k hk x hx
  apply (L.norm_iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hk)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hk)
      (mem_image_of_mem _ hx)) (norm_nonneg _)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `app:lem:common-hamilton-phase`: a scalar forward tolerance gives `C^m`
continuity of actual inverses on a fixed compact target. The constant linear
equivalence and half gap are precisely the normalized geometry from
`app:lem:buffered-inverse-stability`. No inverse derivative closeness is assumed. -/
theorem exists_inverse_continuity_of_compact
    {f₀ : X → Y} {g₀ : Y → X} {K D : Set X} {S U : Set Y}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hS : IsCompact S)
    (hD : IsOpen D) (hKD : K ⊆ D) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    (A : X ≃L[ℝ] Y) (hrange₀ : MapsTo g₀ S K) (heq₀ : EqOn (f₀ ∘ g₀) id U)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (f : X → Y) (g : Y → X),
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ g U → MapsTo g S K →
      EqOn (f ∘ g) id U →
      (∀ x ∈ D, ‖(A.symm : Y →L[ℝ] X).comp (fderiv ℝ f x) -
        ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) →
      cNorm K m (f - f₀) < δ → cNorm S m (g - g₀) < ε := by
  let L : Y →L[ℝ] X := A.symm
  obtain ⟨C, hC, hb⟩ := exists_normalized_inverse_stability hK hconv hS hD hKD hU hSU
    (hf₀.continuousLinearMap_comp L) hg₀ L hrange₀
    (fun y hy ↦ congrArg L (heq₀ hy)) m
  let d := min 1 (ε / C)
  have hd : 0 < d := lt_min zero_lt_one (div_pos hε hC)
  refine ⟨d / (‖L‖ + 1), div_pos hd (by positivity), ?_⟩
  intro f g hf hg hrange heq hgap hsmall
  have he : L ∘ f - L ∘ f₀ = L ∘ (f - f₀) := by funext x; simp
  have hn : cNorm K m (L ∘ f - L ∘ f₀) ≤ ‖L‖ * cNorm K m (f - f₀) := by
    rw [he]
    exact cNorm_postLinear_le hK m L
      (fun x hx ↦ ((hf.sub hf₀).contDiffAt (hD.mem_nhds (hKD hx))).of_le (by simp))
  have hnd : cNorm K m (L ∘ f - L ∘ f₀) < d := by
    have hs := (lt_div_iff₀ (by positivity : 0 < ‖L‖ + 1)).mp hsmall
    nlinarith [cNorm_nonneg K m (f - f₀)]
  have hnorm := hb (L ∘ f) g (hf.continuousLinearMap_comp L) hg hrange
    (fun y hy ↦ congrArg L (heq hy)) (by
      intro x hx
      rw [(L.hasFDerivAt.comp x
        ((hf.contDiffAt (hD.mem_nhds (hKD hx))).differentiableAt (by simp)).hasFDerivAt).fderiv]
      exact hgap x (hKD hx)) (hnd.le.trans (min_le_left _ _))
  apply hnorm.trans_lt
  have hs := hnd.trans_le (min_le_right _ _)
  calc
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hs hC
    _ = ε := mul_div_cancel₀ _ hC.ne'

/-- `app:lem:common-hamilton-phase`: the common-chart geometry has source radius
`3*r` and inverse images in radius `2*r`. The forward tolerance is measured on
that fixed compact inner source ball, and uses no derivative above `m`. -/
theorem exists_inverse_continuity_on_closedBall [FiniteDimensional ℝ X]
    {f₀ : X → Y} {g₀ : Y → X} (a : X) {r : ℝ} (hr : 0 < r)
    {S U : Set Y} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf₀ : ContDiffOn ℝ ∞ f₀ (ball a (3 * r))) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    (A : X ≃L[ℝ] Y) (hrange₀ : MapsTo g₀ S (ball a (2 * r)))
    (heq₀ : EqOn (f₀ ∘ g₀) id U) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (f : X → Y) (g : Y → X),
      ContDiffOn ℝ ∞ f (ball a (3 * r)) → ContDiffOn ℝ ∞ g U →
      MapsTo g S (ball a (2 * r)) → EqOn (f ∘ g) id U →
      (∀ x ∈ ball a (3 * r), ‖(A.symm : Y →L[ℝ] X).comp (fderiv ℝ f x) -
        ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) →
      cNorm (closedBall a (2 * r)) m (f - f₀) < δ → cNorm S m (g - g₀) < ε := by
  obtain ⟨δ, hδ, hb⟩ := exists_inverse_continuity_of_compact
    (isCompact_closedBall a (2 * r)) (convex_closedBall a (2 * r)) hS
    isOpen_ball (closedBall_subset_ball (by linarith : 2 * r < 3 * r)) hU hSU hf₀ hg₀ A
    (fun y hy ↦ ball_subset_closedBall (hrange₀ hy)) heq₀ m hε
  exact ⟨δ, hδ, fun f g hf hg hrange heq hgap hsmall ↦
    hb f g hf hg (fun y hy ↦ ball_subset_closedBall (hrange hy)) heq hgap hsmall⟩

end InverseContinuity

namespace ProjectionChart
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U]
  {H₀ : HomogeneousSymbol E} {Φ₀ : HamiltonFlow H₀ U}

/-- `app:lem:common-hamilton-phase`: finite-order continuity of the actual
`ProjectionChart` coordinates and their `chartLift` on a fixed compact inner
target. The parent supplies the common target, smoothness, source containments,
and normalized half gap from `exists_common_buffered_symbol_charts` or
`exists_commonBufferedHamiltonPhases`, and then proves forward projection
closeness. Only the order-`m` forward perturbation seminorm occurs here.

The reference chart is arbitrary among these actual inverses; when needed,
`coordinates_eq_of_projection_eq` identifies different reference choices. -/
theorem exists_coordinates_finiteOrder_continuity
    (C₀ : ProjectionChart Φ₀) (a : ℝ × InitialData U) {r : ℝ} (hr : 0 < r)
    {K V : Set (E × (ℝ × U))} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hV₀ : V ⊆ C₀.target)
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀.augmentedProjection (ball a (3 * r)))
    (hC₀ : ContDiffOn ℝ ∞ C₀.coordinates C₀.target)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hrange₀ : MapsTo (chartLift C₀.coordinates) K (ball a (2 * r)))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (Φ : HamiltonFlow H U)
      (C : ProjectionChart Φ),
      V ⊆ C.target → ContDiffOn ℝ ∞ Φ.augmentedProjection (ball a (3 * r)) →
      ContDiffOn ℝ ∞ C.coordinates C.target →
      MapsTo (chartLift C.coordinates) K (ball a (2 * r)) →
      (∀ q ∈ ball a (3 * r),
        ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ.augmentedProjection q) -
          ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) →
      cNorm (closedBall a (2 * r)) m (Φ.augmentedProjection - Φ₀.augmentedProjection) < δ →
      cNorm K m (chartLift C.coordinates - chartLift C₀.coordinates) +
        cNorm K m (C.coordinates - C₀.coordinates) < ε := by
  let P : (ℝ × InitialData U) →L[ℝ] (ℝ × U) :=
    (ContinuousLinearMap.fst ℝ ℝ (InitialData U)).prod
      ((ContinuousLinearMap.fst ℝ U (ℝ × U)).comp
        (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))
  have hg₀ : ContDiffOn ℝ ∞ (chartLift C₀.coordinates) V :=
    (hC₀.fst.prodMk (hC₀.snd.prodMk contDiff_snd.contDiffOn)).mono hV₀
  obtain ⟨δ, hδ, hb⟩ := InverseContinuity.exists_inverse_continuity_on_closedBall
    a hr hK hV hKV hΦ₀ hg₀ A hrange₀
    (fun z hz ↦ Prod.ext (C₀.right_inverse z (hV₀ hz)) rfl) m
    (div_pos hε (by positivity : 0 < 1 + ‖P‖))
  refine ⟨δ, hδ, ?_⟩
  intro H Φ C hVC hΦ hC hrange hgap hsmall
  have hg : ContDiffOn ℝ ∞ (chartLift C.coordinates) V :=
    (hC.fst.prodMk (hC.snd.prodMk contDiff_snd.contDiffOn)).mono hVC
  have hi := hb Φ.augmentedProjection (chartLift C.coordinates) hΦ hg hrange
    (fun z hz ↦ Prod.ext (C.right_inverse z (hVC hz)) rfl) hgap hsmall
  have he : P ∘ (chartLift C.coordinates - chartLift C₀.coordinates) =
      C.coordinates - C₀.coordinates := by
    funext z
    apply Prod.ext <;> simp [P, chartLift]
  have hc : cNorm K m (C.coordinates - C₀.coordinates) ≤
      ‖P‖ * cNorm K m (chartLift C.coordinates - chartLift C₀.coordinates) := by
    rw [← he]
    exact InverseContinuity.cNorm_postLinear_le hK m P
      (fun z hz ↦ ((hg.sub hg₀).contDiffAt (hV.mem_nhds (hKV hz))).of_le (by simp))
  have hh := (lt_div_iff₀ (by positivity : 0 < 1 + ‖P‖)).mp hi
  nlinarith

end ProjectionChart
end JanetCartan.HamiltonPhase
