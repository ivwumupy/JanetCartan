module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricProfiles
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FrameExtension

/-!
# Fixed extensions of the actual geometric coefficients

The same prescribed Seeley operator extends the metric, inverse metric,
second fundamental form, projected stresses and canonical normal inverse at
all orders and stages. This supplies their global coefficient norms in
`main:prop:current-scale` and `app:eq:uniform-high-coeff`, with reserve two.
The reference and extension parameters are retained, so this result applies
to the reference already selected for the phase and transport families.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.NormalRankStability
namespace JanetCartan.CurrentCoefficientProfiles
open ProjectedStressFrame AmbientResponse ProtectedFlow

/-- The actual fixed extensions of all geometric coefficients in
`app:eq:uniform-high-coeff`. Each occurrence is the same Seeley operator,
independent of the history and requested order. -/
def extendedGeometricCoefficientNorm {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (m : ℕ)
    (F : Euclidean n → Euclidean N) : ℝ :=
  (cNorm univ m (p.seeleyExtension (inducedMetric F)) +
    cNorm univ m (p.seeleyExtension (fun x ↦ (inducedMetric F x)⁻¹))) +
    (∑ i, ∑ j, cNorm univ m (p.seeleyExtension (fun x ↦ secondFundamentalForm F x i j))) +
    (∑ i, cNorm univ m (p.seeleyExtension (fun x ↦ projectedStress F x i))) +
    cNorm univ m (p.seeleyExtension (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap))

private theorem exists_extended_geometric_coefficient_bound {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (m : ℕ) :
    ∃ C > 0, ∀ (U : Set (Euclidean n)), IsOpen U → closedBall p.center p.radius ⊆ U →
      ∀ (F : Euclidean n → Euclidean N), ContDiffOn ℝ ∞ F U →
      IsImmersionOn F U → HasFullNormalRankOn F U →
      extendedGeometricCoefficientNorm p m F ≤
        C * currentGeometricCoefficientNorm (closedBall p.center p.radius) m F := by
  obtain ⟨A, hA, hbA⟩ := exists_cNorm_vector_seeleyExtension_le (F := MetricTensor n) p m
  obtain ⟨B, hB, hbB⟩ := exists_cNorm_vector_seeleyExtension_le (F := Euclidean N) p m
  obtain ⟨D, hD, hbD⟩ := exists_cNorm_vector_seeleyExtension_le
    (F := MetricTensor n →L[ℝ] Euclidean N) p m
  let C := A + B + D
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro U hU hKU F hF hi hrank
  have hmetric := contDiffOn_inducedMetric hU hF
  have hinverse := contDiffOn_inverse_inducedMetric hU hF hi
  have hform := contDiffOn_secondFundamentalForm_of_smooth hU hF hi
  have hstress := contDiffOn_projectedStress hU hF hi hrank
  have hnormal : ContDiffOn ℝ ∞
      (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap) U := by
    apply contDiffOn_clm_apply.mpr
    intro H
    exact contDiffOn_canonicalNormalCompletion hU hF contDiffOn_const hi hrank
  have hmetricB := (hbA (inducedMetric F)
    (fun x hx ↦ hmetric.contDiffAt (hU.mem_nhds (hKU hx)))).trans
      (mul_le_mul_of_nonneg_right hAC (cNorm_nonneg _ _ _))
  have hinverseB := (hbA (fun x ↦ (inducedMetric F x)⁻¹)
    (fun x hx ↦ hinverse.contDiffAt (hU.mem_nhds (hKU hx)))).trans
      (mul_le_mul_of_nonneg_right hAC (cNorm_nonneg _ _ _))
  have hformB (i j : Fin n) := (hbB (fun x ↦ secondFundamentalForm F x i j)
    (fun x hx ↦ (hform i j).contDiffAt (hU.mem_nhds (hKU hx)))).trans
      (mul_le_mul_of_nonneg_right hBC (cNorm_nonneg _ _ _))
  have hstressB (i : Fin n) := (hbA (fun x ↦ projectedStress F x i)
    (fun x hx ↦ (hstress i).contDiffAt (hU.mem_nhds (hKU hx)))).trans
      (mul_le_mul_of_nonneg_right hAC (cNorm_nonneg _ _ _))
  have hnormalB := (hbD (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap)
    (fun x hx ↦ hnormal.contDiffAt (hU.mem_nhds (hKU hx)))).trans
      (mul_le_mul_of_nonneg_right hDC (cNorm_nonneg _ _ _))
  have hb := add_le_add (add_le_add (add_le_add (add_le_add hmetricB hinverseB)
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hformB i j))
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hstressB i)) hnormalB
  simpa only [extendedGeometricCoefficientNorm, currentGeometricCoefficientNorm,
    ← Finset.mul_sum, ← mul_add] using hb

/-- The global metric, inverse metric, second form, projected stress and normal
inverse coefficient profiles for actual admissible histories
(`main:prop:current-scale`, `app:eq:uniform-high-coeff`). The reserve remains
two. One prescribed extension is used at every order; its agreement on the
closed ball and fixed compact support are the literal Seeley identities.
No current-map or analytic coefficient estimate is assumed. -/
theorem exists_admissible_history_extended_geometric_profiles {n : ℕ}
    (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ E : ℕ → ℝ, (∀ m, 0 ≤ E m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
        ∀ m, extendedGeometricCoefficientNorm p m (finiteHistoryMap G.map u) ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀) := by
  obtain ⟨S, hS, _, _, _, _, _, E, _, hE, hgeom⟩ :=
    exists_admissible_history_geometric_profiles G hr hrR hR hStar hreserve horder
  choose C hC hbound using exists_extended_geometric_coefficient_bound
    (N := embeddingDimension n) p
  refine ⟨S, hS, fun m ↦ C m * E m,
    fun m ↦ mul_nonneg (hC m).le (hE m), ?_⟩
  intro R₀ hR₀ j u ell hu m
  obtain ⟨hi, hrank, _, _, _, _, hp⟩ := hgeom R₀ hR₀ j u ell hu
  have hKU : closedBall p.center p.radius ⊆ ball (0 : Euclidean n) R := by
    simpa only [hpcenter, hpradius] using closedBall_subset_ball hrR
  have hb := hbound m (ball 0 R) isOpen_ball hKU (finiteHistoryMap G.map u)
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn hi hrank
  rw [hpcenter, hpradius] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hp m) (hC m).le).trans_eq (mul_assoc _ _ _).symm)

end JanetCartan.CurrentCoefficientProfiles
