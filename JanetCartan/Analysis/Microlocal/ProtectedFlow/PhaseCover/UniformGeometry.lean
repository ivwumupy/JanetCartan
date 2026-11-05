module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.ChartData

/-!
# Uniform rectangles for a retained local comparison family

The fixed-source compactness argument in `app:ch_regular:thm:no-return`.
The quantitative fields used here are proved for the actual local construction
in `LocalConstruction`; no rectangle cover or physical buffer is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow.PhaseCover
open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace LocalComparisonFamily

/-- A fixed positive upper bound for rectangle widths works for every smaller
width. Centers, the scalar threshold and the physical buffer are selected
before the current symbol. The entire current inverse image is covered, and
all doubled rectangles stay in that same retained chart. This is the local
input to the finite uniform assembly of `app:ch_regular:thm:no-return`. -/
theorem exists_uniform_rectangle_margin
    {H₀ : HomogeneousSymbol E} {D : Set (E × E)} {G M : Set E} {ξ : E}
    (F : LocalComparisonFamily H₀ D G M ξ)
    {r : ℝ} (hr : 0 < r) (hgr : r ≤ F.geometry.radius) :
    ∃ a > (0 : ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ a →
      ∃ (d εx : ℝ) (centers : Finset ((ℝ × F.geometry.tangentSpace) ×
          (ℝ × F.geometry.tangentSpace))),
        0 < d ∧ d ≤ F.threshold ∧ 0 < εx ∧
        ∀ H, cNorm (closedBall (0, ξ) F.stateRadius) 3
            (fun z ↦ H.1.h z - H₀.h z) ≤ d →
          (fun z ↦ ((F.charts H).chart.coordinates z, z.2)) ''
              (closedBall (0 : E) r ×ˢ F.geometry.parameters) ⊆
            ⋃ q ∈ centers, ball q (ρ / 8) ∧
          ∀ q ∈ centers, ∀ z ∈ closedBall q (2 * ρ),
            (z.1.1, (z.1.2, z.2)) ∈ (F.charts H).chart.source ∧
            closedBall ((F.charts H).flow.position (z.1.1, (z.1.2, z.2))) εx ⊆
              ball 0 (2 * r) := by
  classical
  let a := min (F.sourceRadius / 4)
    (min (F.geometry.parameterRadius / 4) (r / (8 * (F.flowBound + 1))))
  have ha : 0 < a := by
    dsimp [a]
    positivity [F.sourceRadius_pos, F.geometry.parameterRadius_pos, F.flowBound_pos]
  refine ⟨a, ha, ?_⟩
  intro ρ hρ hρa
  have hρs : 4 * ρ ≤ F.sourceRadius := by
    have hh := hρa.trans (min_le_left _ _); linarith only [hh]
  have hρp : 4 * ρ ≤ F.geometry.parameterRadius := by
    have hh := hρa.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hh]
  have hρL : 8 * (F.flowBound + 1) * ρ ≤ r := by
    have hh := hρa.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (show 0 < 8 * (F.flowBound + 1) by
      positivity [F.flowBound_pos])).mp hh
    linarith only [hh']
  let K := closedBall (0 : E) r ×ˢ F.geometry.parameters
  have hK : IsCompact K := (isCompact_closedBall _ _).prod F.geometry.isCompact_parameters
  have hKg : K ⊆ F.geometry.domain := fun z hz ↦
    F.geometry.outer_product_subset_domain
      ⟨closedBall_subset_closedBall (by linarith [F.geometry.radius_pos]) hz.1, hz.2⟩
  let f₀ := fun z : E × (ℝ × F.geometry.tangentSpace) ↦
    (F.reference.chart.coordinates z, z.2)
  have hK₀ : IsCompact (f₀ '' K) := hK.image_of_continuousOn
    ((F.reference.coordinates_smooth.continuousOn.mono
      (hKg.trans F.reference.target_contains)).prodMk continuousOn_snd)
  have hcover : f₀ '' K ⊆ ⋃ q : f₀ '' K, ball q.1 (ρ / 32) := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, mem_ball_self (by positivity)⟩
  obtain ⟨s, hs⟩ := hK₀.elim_finite_subcover
    (fun q : f₀ '' K ↦ ball q.1 (ρ / 32)) (fun _ ↦ isOpen_ball) hcover
  let d := min F.threshold (ρ / (64 * (F.coordinateBound + 1)))
  have hd : 0 < d := by dsimp [d]; positivity [F.threshold_pos, F.coordinateBound_pos]
  refine ⟨d, r / 4, s.image Subtype.val, hd, min_le_left _ _, by positivity, ?_⟩
  intro H hsmall
  let C := F.charts H
  have hnear (z) (hz : z ∈ K) :
      dist (C.chart.coordinates z, z.2) (f₀ z) ≤ ρ / 64 := by
    have hh := (F.coordinates_dist_le H z (hKg hz)).trans
      (mul_le_mul_of_nonneg_left hsmall F.coordinateBound_pos.le)
    have hdρ : d * (64 * (F.coordinateBound + 1)) ≤ ρ :=
      (le_div_iff₀ (by positivity [F.coordinateBound_pos])).mp (min_le_right _ _)
    change dist (C.chart.coordinates z, z.2) (F.reference.chart.coordinates z, z.2) ≤ _
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    change dist ((F.charts H).chart.coordinates z) (F.reference.chart.coordinates z) ≤ _
    nlinarith only [hh, hdρ, hd, hρ]
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨q, hq, hqz⟩ := mem_iUnion₂.mp (hs (mem_image_of_mem f₀ hz))
    refine mem_iUnion₂.mpr ⟨q.1, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
    have ht := dist_triangle (C.chart.coordinates z, z.2) (f₀ z) q.1
    have hh := hnear z hz
    have hball := mem_ball.mp hqz
    exact mem_ball.mpr (by linarith only [ht, hh, hball, hρ])
  · intro q hq z hz
    obtain ⟨q₀, _hq₀, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨w, hw, he⟩ := q₀.property
    have ht := C.target_contains (hKg hw)
    have hsource := C.chart.maps_to_source w ht
    let qc := (C.chart.coordinates w, w.2)
    let lift := fun v : (ℝ × F.geometry.tangentSpace) × (ℝ × F.geometry.tangentSpace) ↦
      (v.1.1, (v.1.2, v.2))
    have hdist : dist z qc < 3 * ρ := by
      have hh := hnear w hw
      rw [he] at hh
      have hh' := dist_triangle z q₀.1 qc
      rw [dist_comm q₀.1 qc] at hh'
      have hz' := mem_closedBall.mp hz
      change dist qc q₀.1 ≤ ρ / 64 at hh
      linarith only [hh, hh', hz', hρ]
    have hlift : dist (lift z) (lift qc) = dist z qc := by
      simp only [lift, Prod.dist_eq, max_assoc]
    have hqc : lift qc ∈ ball ((0 : ℝ), (0, F.geometry.center)) (2 * F.sourceRadius) := by
      rw [← F.sourceRadius_eq H]
      exact C.source_subset hsource
    have hqc' : lift qc ∈ ball ((0 : ℝ), (0, F.geometry.center)) (3 * F.sourceRadius) :=
      ball_subset_ball (by linarith only [F.sourceRadius_pos]) hqc
    have hzs : lift z ∈ ball ((0 : ℝ), (0, F.geometry.center)) (3 * F.sourceRadius) := by
      have hh := dist_triangle (lift z) (lift qc) ((0 : ℝ), (0, F.geometry.center))
      rw [hlift] at hh
      have hc := mem_ball.mp hqc
      exact mem_ball.mpr (by linarith only [hh, hc, hdist, hρs, hρ])
    have hposition : dist (C.flow.position (lift z)) w.1 ≤ r / 2 := by
      have hh := F.position_dist_le H (lift z) hzs (lift qc) hqc'
      have heq : C.flow.position (lift qc) = w.1 := C.chart.right_inverse w ht
      rw [heq, hlift] at hh
      have hh' := mul_le_mul_of_nonneg_left hdist.le F.flowBound_pos.le
      change dist (C.flow.position (lift z)) w.1 ≤ _ at hh
      nlinarith only [hh, hh', hρL, hρ, F.flowBound_pos]
    have hx : dist (C.flow.position (lift z)) 0 ≤ 3 * r / 2 := by
      have hh := dist_triangle (C.flow.position (lift z)) w.1 0
      have hwx := mem_closedBall.mp hw.1
      linarith only [hh, hwx, hposition]
    have hη : dist z.2 F.geometry.center < 3 * F.geometry.parameterRadius := by
      have hh := dist_triangle z.2 w.2 F.geometry.center
      have hp : dist z.2 w.2 ≤ dist z qc := le_max_right _ _
      have hwη := mem_closedBall.mp hw.2.1
      linarith only [hh, hp, hwη, hdist, hρp, hρ]
    refine ⟨?_, ?_⟩
    · rw [C.source_eq, F.sourceRadius_eq H]
      refine ⟨hzs, C.target_contains ?_⟩
      change (C.flow.position (lift z), z.2) ∈ F.geometry.domain
      exact ⟨mem_ball.mpr (by linarith only [hx, hgr, hr]), mem_ball.mpr hη⟩
    · intro y hy
      have hh := dist_triangle y (C.flow.position (lift z)) 0
      have hy' := mem_closedBall.mp hy
      exact mem_ball.mpr (by linarith only [hh, hy', hx, hr])

end LocalComparisonFamily
end JanetCartan.ProtectedFlow.PhaseCover
