module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Compact

/-!
# The frozen cube inputs to complete source coverage

For `app:ch_regular:thm:no-return`, the covariable transversality required by
`PhaseCover.exists_finite_comparison_cover` follows from the cube simple-stratum
theorem. It holds at every characteristic direction outside the forbidden cone,
not merely at the carrier seeds.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow

open ActualCarriers ActualCarriers.FrozenPhaseReference HamiltonPhase PhaseCover

/-- The literal normalized determinant has the conic domain and homogeneity
needed for complete phase coverage (`app:ch_regular:thm:no-return`). -/
theorem normalizedHomogeneousSymbol_conic {n : ℕ} {U : Set (Euclidean n)}
    (hU : IsOpen U) (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : ContDiffOn ℝ ∞ Q U) :
    (normalizedHomogeneousSymbol hU Q hQ).ConicHomogeneous := by
  constructor
  · intro z hz r hr
    exact ⟨hz.1, smul_ne_zero hr.ne' hz.2⟩
  · intro z _ r hr
    exact normalizedSymbol_pos_homogeneous Q z hr

/-- The entire frozen forbidden cone is closed, including its vertex
(`app:ch_seed:prop:seed-strata`, `app:ch_regular:thm:no-return`). -/
theorem isClosed_cubeBadSubspaceUnion (n : ℕ) : IsClosed (cubeBadSubspaceUnion n) :=
  (cubeBadSubspaces n).finite_toSet.isClosed_biUnion
    (fun L _ ↦ Submodule.closed_of_finiteDimensional L)

/-- A frozen characteristic outside the nonprincipal cone has a nonzero
covariable Hamilton derivative. This discharges the transversality input of
`PhaseCover.exists_finite_comparison_cover` on the whole source set
(`app:ch_regular:thm:no-return`). -/
theorem frozenSymbol_hp_ne_zero {n : ℕ} (hn : 5 ≤ n)
    {x ξ : Euclidean n} (hξ : ξ ∉ cubeBadSubspaceUnion n)
    (hchar : (frozenSymbol n).h (x, ξ) = 0) :
    (frozenSymbol n).hp (x, ξ) ≠ 0 := by
  have hne : ξ ≠ 0 := by
    rintro rfl
    exact hξ (zero_mem_cubeBadSubspaceUnion hn)
  have hdet : cubeDeterminant ξ = 0 := by
    rw [frozenSymbol_h] at hchar
    exact (mul_eq_zero.mp hchar).resolve_left (determinantNormalization_pos hne).ne'
  have hd := fderiv_cubeDeterminant_ne_zero_of_not_mem_badSubspaceUnion hn hξ hdet
  obtain ⟨v, hv⟩ : ∃ v : Euclidean n, fderiv ℝ cubeDeterminant ξ v ≠ 0 := by
    by_contra! hz
    apply hd
    ext v
    exact hz v
  obtain ⟨v, hv⟩ : ∃ v : Euclidean n, 0 < fderiv ℝ cubeDeterminant ξ v := by
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · exact ⟨-v, by simpa using neg_pos.mpr hneg⟩
    · exact ⟨v, hpos⟩
  have hpos := frozenSymbol_transverse_pos (x := x) hne hdet hv
  intro he
  rw [he, inner_zero_left] at hpos
  exact lt_irrefl 0 hpos

/-- Normalizing a covector does not enter the forbidden cone. This connects
annular source neighborhoods with regular angular chart images
(`app:ch_regular:thm:no-return`). -/
theorem normalizedCovector_not_mem_cubeBadSubspaceUnion {n : ℕ}
    {ξ : Euclidean n} (hξ : ξ ≠ 0) (hbad : ξ ∉ cubeBadSubspaceUnion n) :
    normalizedCovector ξ ∉ cubeBadSubspaceUnion n := by
  intro h
  obtain ⟨L, hL, hmem⟩ := mem_iUnion₂.mp h
  apply hbad
  apply mem_iUnion₂.mpr
  refine ⟨L, hL, ?_⟩
  have hh := L.smul_mem ‖ξ‖ hmem
  simpa [normalizedCovector, smul_smul, norm_ne_zero_iff.mpr hξ] using hh

/-- The complete compact annular source admits fixed comparison geometry for
the literal cube symbol. The only geometric input is avoidance of the actual
forbidden cone; transversality and regularity are proved here. The current
symbol threshold will be discharged by the fixed coefficient extension
(`app:ch_regular:thm:no-return`). -/
theorem exists_cube_comparison_cover {n : ℕ} (hn : 5 ≤ n)
    {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hbad : Disjoint Ω (cubeBadSubspaceUnion n)) :
    ∃ (s : Finset {p : Euclidean n // p ∈ Ω ∧ (frozenSymbol n).h (0, p) = 0})
      (g : s → ComparisonGeometry (Euclidean n)) (r δ c C ε : ℝ)
      (K : Set (Euclidean n × Euclidean n)) (A : Set (Euclidean n)),
      0 < r ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      IsCompact K ∧ K ⊆ (frozenSymbol n).domain ∧
      closedBall (0 : Euclidean n) (3 * r) ×ˢ Ω ⊆ K ∧
      (∀ i : s, 3 * r < (g i).radius) ∧ IsCompact A ∧
      A ⊆ (cubeBadSubspaceUnion n)ᶜ ∧
      (∀ q ∈ A, closedBall q ε ⊆ (cubeBadSubspaceUnion n)ᶜ) ∧
      ∀ (H : HomogeneousSymbol (Euclidean n)), (frozenSymbol n).domain ⊆ H.domain →
        ContDiffOn ℝ ∞ H.h (frozenSymbol n).domain → H.ConicHomogeneous →
        cNorm K 3 (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ δ →
        ∃ charts : (i : s) → ComparisonChart H (g i),
          (∀ η : ComparisonGeometry.ParameterFamily g,
            ∀ x ∈ closedBall 0 (2 * r),
            c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
              ‖ComparisonChart.familyGradient charts η x‖ ≤ C ∧
              normalizedCovector (ComparisonChart.familyGradient charts η x) ∈ A) ∧
          ∀ x ∈ closedBall 0 r, ∀ p ∈ Ω, H.h (x, p) = 0 →
            ∃ η : ComparisonGeometry.ParameterFamily g,
              p = ComparisonChart.familyGradient charts η x := by
  have hb (p) (hp : p ∈ Ω) : p ∉ cubeBadSubspaceUnion n := disjoint_left.mp hbad hp
  have hnz (p) (hp : p ∈ Ω) : p ≠ 0 := by
    rintro rfl
    exact hb 0 hp (zero_mem_cubeBadSubspaceUnion hn)
  have hsource : ({0} : Set (Euclidean n)) ×ˢ Ω ⊆ (frozenSymbol n).domain :=
    fun z hz ↦ (mem_frozenSymbol_domain z).mpr (hnz z.2 hz.2)
  simpa only [compl_eq_univ_sdiff] using exists_finite_comparison_cover (frozenSymbol n)
    (frozenSymbol n).isOpen_domain Subset.rfl (frozenSymbol_smooth n)
    (normalizedHomogeneousSymbol_conic isOpen_univ _ contDiffOn_const)
    (fun _ _ ↦ rfl) hΩ hsource hnz
    (fun p hp hz ↦ frozenSymbol_hp_ne_zero hn (hb p hp) hz)
    isOpen_univ (isClosed_cubeBadSubspaceUnion n)
    (fun p hp ↦ ⟨mem_univ _, normalizedCovector_not_mem_cubeBadSubspaceUnion
      (hnz p hp) (hb p hp)⟩)

end JanetCartan.ProtectedFlow
