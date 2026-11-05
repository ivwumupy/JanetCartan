module

public import JanetCartan.Iteration.RevisedConvergence.Limit
public import JanetCartan.Geometry.IsometricEmbedding.Coordinates

/-!
# Restoring the same target parameter and normalized coordinates

The final paragraph of §18 in `paper-v2.tex`.  The map here is literally
`(s * ρ) • M∞ ((s * ρ)⁻¹ • coordinateMap A⁻¹ x)`.  The positive `s`, positive
`ρ`, coordinate matrix `A`, and global sum are the ones supplied to the revised
iteration; none is selected again for a derivative order.  The final domain is
one intersection with the original metric domain.

`exists_local_metric_of_revised_bounds` has the Euclidean local-realization
conclusion consumed by `exists_local_isometric_embedding_of_euclidean_local_existence`.
It remains explicitly conditional on the actual revised increment and defect
budgets.  This implication is not a proof of the unconditional Main theorem.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RevisedConvergence

/-- §18: undo the same positive dilation `sρ` and the same coordinate matrix.
No translation or derivative-order-dependent choice is introduced. -/
def restoredMap {n N : ℕ} (A : MetricTensor n) (s ρ : ℝ)
    (F : Euclidean n → Euclidean N) : Euclidean n → Euclidean N :=
  fun x ↦ (s * ρ) • F ((s * ρ)⁻¹ • coordinateMap A⁻¹ x)

/-- §18: the single inverse-coordinate image of the scaled fixed neighborhood. -/
def restoredDomain {n : ℕ} (A : MetricTensor n) (s ρ : ℝ)
    (W : Set (Euclidean n)) : Set (Euclidean n) :=
  coordinateMap A⁻¹ ⁻¹' ((fun x ↦ (s * ρ)⁻¹ • x) ⁻¹' W)

/-- §18 after `main:eq:isometry`: restore the literal map by reusing the
fixed-rescaling and coordinate-restoration identities.  The metric equation
is assumed only for the intermediate smooth sum, not for the restored map. -/
theorem restore_same_parameters {n N : ℕ} {g : MetricField n}
    (A : MetricTensor n) (hA : IsUnit A) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    {W : Set (Euclidean n)} (hW : IsOpen W) (hW0 : (0 : Euclidean n) ∈ W)
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hmetric : IsIsometricOn (scaledMetric (coordinatePullback g A) (s * ρ)) F W) :
    IsOpen (restoredDomain A s ρ W) ∧ (0 : Euclidean n) ∈ restoredDomain A s ρ W ∧
      ContDiffOn ℝ ∞ (restoredMap A s ρ F) (restoredDomain A s ρ W) ∧
      IsIsometricOn g (restoredMap A s ρ F) (restoredDomain A s ρ W) := by
  have ha : s * ρ ≠ 0 := ne_of_gt (mul_pos hs hρ)
  obtain ⟨hV, hV0⟩ := dilation_preimage_neighborhood hW hW0 (s * ρ)⁻¹
  have hscaled : ContDiff ℝ ∞ (fun x ↦ (s * ρ) • F ((s * ρ)⁻¹ • x)) :=
    (hF.comp (contDiff_id.const_smul (s * ρ)⁻¹)).const_smul (s * ρ)
  have hscaledMetric : IsIsometricOn (coordinatePullback g A)
      (fun x ↦ (s * ρ) • F ((s * ρ)⁻¹ • x))
      ((fun x ↦ (s * ρ)⁻¹ • x) ⁻¹' W) :=
    isIsometricOn_rescale ha (hF.differentiable (by simp)).differentiableOn hW hmetric
  obtain ⟨hreg, hiso⟩ := restore_coordinates A hA hV hscaled.contDiffOn hscaledMetric
  exact ⟨(coordinate_preimage_neighborhood hV hV0 A⁻¹).1,
    (coordinate_preimage_neighborhood hV hV0 A⁻¹).2, hreg, hiso⟩

/-- §18, with the exact Euclidean local-realization output consumed by `Main`:
the revised budgets yield a smooth metric realization after restoring the
same `sρ` and `A`, on one neighborhood inside the original domain.  Neither
positivity nor an embedding is assumed of the unknown limit.  The actual
analytic producers of the displayed budgets remain explicit obligations. -/
theorem exists_local_metric_of_revised_bounds {n N : ℕ}
    (H : ℕ → ℝ) (kMin : ℕ) {R₀ : ℝ} (hR₀ : 1 < R₀)
    {G : Euclidean n → Euclidean N} {u : ℕ → Euclidean n → Euclidean N}
    {D W V : Set (Euclidean n)} {g : MetricField n} {C : ℕ → ℝ}
    (A : MetricTensor n) (hA : IsUnit A) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (hD : IsCompact D) (hW : IsOpen W) (hW0 : (0 : Euclidean n) ∈ W)
    (hWD : W ⊆ D) (hV : IsOpen V) (hV0 : (0 : Euclidean n) ∈ V)
    (hG : ContDiff ℝ ∞ G) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hg : ContinuousOn (scaledMetric (coordinatePullback g A) (s * ρ)) D)
    (hderiv : ∀ r, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ r (u j) x‖ ≤ derivativeBudget n H kMin R₀ C r j)
    (hmetric : ∀ j, cNorm D 0
      (inducedMetric (currentHistoryMap G u j) -
        scaledMetric (coordinatePullback g A) (s * ρ)) ≤
      (iterationScale R₀ growthExponent j ^
        (-(powerAdaptiveSchedule H R₀ growthExponent kMin j : ℝ))) ^ 2) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ (0 : Euclidean n) ∈ U ∧ U ⊆ V ∧
      ∃ F : Euclidean n → Euclidean N,
        F = restoredMap A s ρ (limitMap G u) ∧
        ContDiffOn ℝ ∞ F U ∧ IsIsometricOn g F U := by
  obtain ⟨hlim, _, hiso⟩ := smooth_isometric_limit_of_revised_bounds
    H kMin hR₀ hD hG hu hg hderiv hmetric
  obtain ⟨hU, hU0, hreg, hrestored⟩ := restore_same_parameters A hA hs hρ hW hW0 hlim
    (fun _ hx ↦ hiso (hWD hx))
  refine ⟨restoredDomain A s ρ W ∩ V, hU.inter hV, ⟨hU0, hV0⟩,
    Set.inter_subset_right, restoredMap A s ρ (limitMap G u), rfl,
    hreg.mono Set.inter_subset_left, ?_⟩
  exact fun _ hx ↦ hrestored hx.1

/-- §18 final restriction: positivity of the given metric turns the same
restored smooth realization into an embedding on one smaller neighborhood.
The construction and all derivative orders continue to use the same map. -/
theorem exists_local_embedding_of_revised_bounds {n N : ℕ}
    (H : ℕ → ℝ) (kMin : ℕ) {R₀ : ℝ} (hR₀ : 1 < R₀)
    {G : Euclidean n → Euclidean N} {u : ℕ → Euclidean n → Euclidean N}
    {D W V : Set (Euclidean n)} {g : MetricField n} {C : ℕ → ℝ}
    (A : MetricTensor n) (hA : IsUnit A) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (hD : IsCompact D) (hW : IsOpen W) (hW0 : (0 : Euclidean n) ∈ W)
    (hWD : W ⊆ D) (hV : IsOpen V) (hV0 : (0 : Euclidean n) ∈ V)
    (hpositive : ∀ x ∈ V, (g x).PosDef)
    (hG : ContDiff ℝ ∞ G) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hg : ContinuousOn (scaledMetric (coordinatePullback g A) (s * ρ)) D)
    (hderiv : ∀ r, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ r (u j) x‖ ≤ derivativeBudget n H kMin R₀ C r j)
    (hmetric : ∀ j, cNorm D 0
      (inducedMetric (currentHistoryMap G u j) -
        scaledMetric (coordinatePullback g A) (s * ρ)) ≤
      (iterationScale R₀ growthExponent j ^
        (-(powerAdaptiveSchedule H R₀ growthExponent kMin j : ℝ))) ^ 2) :
    ∃ U : TopologicalSpace.Opens (Euclidean n), (0 : Euclidean n) ∈ U ∧
      (U : Set (Euclidean n)) ⊆ V ∧
      ContDiffOn ℝ ∞ (restoredMap A s ρ (limitMap G u)) U ∧
      Topology.IsEmbedding (fun x : U ↦ restoredMap A s ρ (limitMap G u) x.val) ∧
      IsIsometricOn g (restoredMap A s ρ (limitMap G u)) U := by
  obtain ⟨U, hU, hU0, hUV, F, rfl, hF, hiso⟩ := exists_local_metric_of_revised_bounds
    H kMin hR₀ A hA hs hρ hD hW hW0 hWD hV hV0 hG hu hg hderiv hmetric
  obtain ⟨U', h0, hsub, hreg, hemb, heq⟩ := exists_local_embedding_of_isIsometricOn
    hU hU0 hF (fun x hx ↦ hpositive x (hUV hx)) hiso
  exact ⟨U', h0, hsub.trans hUV, hreg, hemb, heq⟩

end JanetCartan.RevisedConvergence
