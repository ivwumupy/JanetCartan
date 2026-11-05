module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualInverses

/-!
# The actual inverse graphs fit the primitive integration balls

These containments discharge the inverse-range hypothesis in the sharp
phase estimate of `app:ch_seed:prop:seed-phase-charts`. The only radius
conditions are imposed when constructing the actual charts. Transverse
coordinates are regrouped literally, retaining time, carrier, and epsilon.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualComparison InverseEstimates

variable {n : ℕ}
local notation "E" => Euclidean (n - 1)
local notation "X" => WithLp 2 (ℝ × E)

/-- Regroup transverse parameters into the primitive quotient convention,
without changing a coordinate (`app:ch_seed:prop:seed-phase-charts`). -/
def transverseParameterReindex :
    (ℝ × ((Euclidean 2 × ℝ × ℝ) × E × E)) →L[ℝ]
      (ℝ × Euclidean 2 × ℝ × ℝ × E × E) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p ↦ (p.1, p.2.1.1, p.2.1.2.1, p.2.1.2.2, p.2.2.1, p.2.2.2)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Literal formula for the regrouping used by the transverse inverse
estimate (`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseParameterReindex_apply
    (p : ℝ × ((Euclidean 2 × ℝ × ℝ) × E × E)) :
    transverseParameterReindex p =
      (p.1, p.2.1.1, p.2.1.2.1, p.2.1.2.2, p.2.2.1, p.2.2.2) := rfl

/-- The same closed transverse parameter core in primitive coordinate order
(`app:ch_seed:prop:seed-phase-charts`). -/
def transversePrimitiveBox (z₀ : Euclidean 3) (r e : ℝ) :
    Set (ℝ × ((Euclidean 2 × ℝ × ℝ) × E × E)) :=
  Icc (-e) e ×ˢ (closedBall (spectatorCenter z₀) r ×ˢ
    closedBall 0 (r / 4) ×ˢ closedBall (z₀ 0) r) ×ˢ
    closedBall 0 (r / 4) ×ˢ closedBall 0 (r / 4)

/-- Compactness of the regrouped transverse core
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem isCompact_transversePrimitiveBox (z₀ : Euclidean 3) (r e : ℝ) :
    IsCompact (transversePrimitiveBox (n := n) z₀ r e) :=
  isCompact_Icc.prod (((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))

/-- Regrouping identifies the closed cores exactly
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transversePrimitiveBox_eq_preimage (z₀ : Euclidean 3) (r e : ℝ) :
    transversePrimitiveBox (n := n) z₀ r e =
      transverseParameterReindex ⁻¹' transverseParameterBox z₀ r e := by
  ext p
  simp only [transversePrimitiveBox, transverseParameterBox, mem_prod, mem_preimage,
    transverseParameterReindex_apply, and_assoc]

/-- Every full physical/data core is inside the fixed forward-estimate ball
when the actual chart radius obeys the constructed cap
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem full_chartBox_subset_ball (z₀ : Euclidean 3) (ηb : E)
    {r s e ρ : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrρ : 2 * r ≤ ρ) (heρ : e ≤ ρ) :
    fullParameterBox z₀ (s / 2) e ×ˢ dataBox z₀ ηb (2 * r) ⊆
      closedBall (((0 : ℝ), spectatorCenter z₀, (0 : X), (0 : X)), (z₀ 0,ηb)) ρ := by
  intro q hq
  have hε : q.1.1 ∈ closedBall (0 : ℝ) ρ := by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hq.1.1.1], by linarith [hq.1.1.2]⟩
  have hsρ : s / 2 ≤ ρ := by linarith
  simp only [← closedBall_prod_same, mem_prod]
  exact ⟨⟨hε, closedBall_subset_closedBall hsρ hq.1.2.1,
    closedBall_subset_closedBall hsρ hq.1.2.2.1,
    closedBall_subset_closedBall hsρ hq.1.2.2.2⟩,
    closedBall_subset_closedBall hrρ hq.2.1, closedBall_subset_closedBall hrρ hq.2.2⟩

/-- Every transverse physical/data core is inside the corresponding fixed
forward-estimate ball, with time and both spectators retained
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverse_chartBox_subset_ball (z₀ : Euclidean 3) (ηb : E)
    {r s e ρ : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrρ : 2 * r ≤ ρ) (heρ : e ≤ ρ) :
    transversePrimitiveBox z₀ (s / 2) e ×ˢ closedBall ηb (2 * r) ⊆
      closedBall (((0 : ℝ), (spectatorCenter z₀, (0 : ℝ), z₀ 0),
        (0 : E), (0 : E)), ηb) ρ := by
  intro q hq
  have hε : q.1.1 ∈ closedBall (0 : ℝ) ρ := by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hq.1.1.1], by linarith [hq.1.1.2]⟩
  have hsρ : s / 2 ≤ ρ := by linarith
  have hsρ' : s / 2 / 4 ≤ ρ := by linarith
  simp only [← closedBall_prod_same, mem_prod]
  exact ⟨⟨hε, ⟨closedBall_subset_closedBall hsρ hq.1.2.1.1,
    closedBall_subset_closedBall hsρ' hq.1.2.1.2.1,
    closedBall_subset_closedBall hsρ hq.1.2.1.2.2⟩,
    closedBall_subset_closedBall hsρ' hq.1.2.2.1,
    closedBall_subset_closedBall hsρ' hq.1.2.2.2⟩,
    closedBall_subset_closedBall hrρ hq.2⟩

/-- The full actual inverse graph lies in the fixed primitive ball whenever
the constructed radius is capped by half that ball radius. This uses the
proved inverse range, and assumes no inverse norm estimate
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem full_inverseGraph_mem_ball
    {f : (ℝ × Euclidean 2 × X × X) → (ℝ × E) → (ℝ × E)}
    {z₀ : Euclidean 3} {ηb : E} {r s e ρ b c : ℝ}
    {V L Limage : Set (ℝ × E)} {G : (ℝ × E) ≃L[ℝ] (ℝ × E)}
    (hs : 0 < s) (he : 0 < e) (hsr : s ≤ r) (hrρ : 2 * r ≤ ρ) (heρ : e ≤ ρ)
    (hLV : L ⊆ cthickening b (closure V))
    (h : BufferedPhaseInverse f (fullParameterSet z₀ s (2 * e))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V Limage b c G) :
    MapsTo (inverseGraph (Function.uncurry (phaseChartInverse f (dataSet z₀ ηb (2 * r)))))
      (fullParameterBox z₀ (s / 2) e ×ˢ L)
      (closedBall (((0 : ℝ), (spectatorCenter z₀, (0 : X), (0 : X))), (z₀ 0, ηb)) ρ) := by
  intro q hq
  have hp : q.1 ∈ fullParameterSet z₀ s (2 * e) := by
    simpa only [show 2 * (s / 2) = s by ring] using
      (fullParameterBox_geometry z₀ (by positivity : 0 < s / 2) he).2.2.2 hq.1
  have hu := (phaseChartInverse_spec (h.outer_buffer q.1 hp (hLV hq.2))).1
  have he' : q.1.1 ∈ closedBall (0 : ℝ) ρ := by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hq.1.1.1], by linarith [hq.1.1.2]⟩
  have hsρ : s / 2 ≤ ρ := by linarith
  simp only [inverseGraph, ← closedBall_prod_same, mem_prod]
  exact ⟨⟨he', closedBall_subset_closedBall hsρ hq.1.2.1, closedBall_subset_closedBall hsρ hq.1.2.2.1, closedBall_subset_closedBall hsρ hq.1.2.2.2⟩,
    closedBall_subset_closedBall hrρ (ball_subset_closedBall hu.1),
    closedBall_subset_closedBall hrρ (ball_subset_closedBall hu.2)⟩

/-- The transverse actual inverse graph fits its primitive integration ball,
with every spectator and physical coordinate retained
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverse_inverseGraph_mem_ball
    {f : (ℝ × Euclidean 2 × ℝ × ℝ × E × E) → E → E}
    {z₀ : Euclidean 3} {ηb : E} {r s e ρ b c : ℝ}
    {V L Limage : Set E} {G : E ≃L[ℝ] E}
    (hs : 0 < s) (he : 0 < e) (hsr : s ≤ r) (hrρ : 2 * r ≤ ρ) (heρ : e ≤ ρ)
    (hLV : L ⊆ cthickening b (closure V))
    (h : BufferedPhaseInverse f (transverseParameterSet z₀ s (2 * e))
      (closedBall ηb r) (ball ηb (2 * r)) (closedBall ηb (2 * r)) V Limage b c G) :
    MapsTo (inverseGraph (fun q ↦ phaseChartInverse f (ball ηb (2 * r))
      (transverseParameterReindex q.1) q.2))
      (transversePrimitiveBox z₀ (s / 2) e ×ˢ L)
      (closedBall (((0 : ℝ), ((spectatorCenter z₀, (0 : ℝ), z₀ 0), (0 : E), (0 : E))), ηb) ρ) := by
  intro q hq
  have hb : transverseParameterReindex q.1 ∈ transverseParameterBox z₀ (s / 2) e := by
    rw [transversePrimitiveBox_eq_preimage] at hq
    exact hq.1
  have hp : transverseParameterReindex q.1 ∈ transverseParameterSet z₀ s (2 * e) := by
    simpa only [show 2 * (s / 2) = s by ring] using
      (transverseParameterBox_geometry z₀ (by positivity : 0 < s / 2) he).2.2.2 hb
  have hu := (phaseChartInverse_spec (h.outer_buffer _ hp (hLV hq.2))).1
  have he' : q.1.1 ∈ closedBall (0 : ℝ) ρ := by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hq.1.1.1], by linarith [hq.1.1.2]⟩
  have hsρ : s / 2 ≤ ρ := by linarith
  have hsρ' : s / 2 / 4 ≤ ρ := by linarith
  simp only [inverseGraph, ← closedBall_prod_same, mem_prod]
  exact ⟨⟨he', ⟨closedBall_subset_closedBall hsρ hq.1.2.1.1,
    closedBall_subset_closedBall hsρ' hq.1.2.1.2.1,
    closedBall_subset_closedBall hsρ hq.1.2.1.2.2⟩,
    closedBall_subset_closedBall hsρ' hq.1.2.2.1,
    closedBall_subset_closedBall hsρ' hq.1.2.2.2⟩,
    closedBall_subset_closedBall hrρ (ball_subset_closedBall hu)⟩

end JanetCartan.FullPhaseCharts.ActualEstimates
