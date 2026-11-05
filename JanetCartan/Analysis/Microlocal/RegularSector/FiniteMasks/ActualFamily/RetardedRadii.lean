module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily

/-!
# Retarded radii on the actual finite chart family

The stronger uniform amplitude constructor proves `ρ ≤ b` and `src ≤ ρ / 4`
on its original witnesses. Choose the local charts from that constructor
before applying finite compactness, then retain these inequalities for every
selected chart. All masks, the determinant gap, the doubled physical radial
threshold and the shell-cover consequences belong to this same `ActualMaskFamily`.

Consumer: `UniformEvolution` on the selected charts of the actual sector
construction. The inequalities feed
`UniformAmplitudes.retained_source_slab_bounds`, fitting the source-compatible
elapsed slab into the retained phase radius. Sources in `paper-v2.tex`:
`app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular_base:eq:energy-complete-residual`.
This constructs the finite geometric inputs; the actual retarded/PDO estimates,
finite operator sum and complete residual remain with the sector construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open ActualCarriers Characteristic.UniformAmplitudes
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- Construct the local chart with the stronger uniform producer, preserving
its radius comparisons on the same root, section, masks and varying-field
evolution. These are proved conclusions, before any finite selection.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_localChart_with_retarded_radii
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E)
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ c : LocalChart Ω x RQ A₀ ξ M,
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 := by
  obtain ⟨r, c, hm⟩ := exists_nonzero_adjugate_entry_of_regular A₀ ξ hreg
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost, hℓ,
    σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii hΩ x hRQ hKΩ
      A₀ ξ r c hξ hp hreg hm hM
  exact ⟨⟨i, r, c, hm, ℓ, H, ε, L, a, b, ρ, ρo, src, μ, ν,
    phaseCost, σ, κ, hε, hL, ha, hb, hρ, hρo, hsrc, hsrca, hμ, hν,
    hphaseCost, hℓ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ,
    hevolution⟩, hρb, hsrcρ⟩

/-- Select one actual finite family from the enriched local choices. Every
selected chart retains `ρ ≤ b` and `src ≤ ρ / 4`, so the source-compatible
slab fits its own phase/amplitude buffer. The original `ActualMaskFamily`
fields and all its partition, support, plateau and shell-cover theorems apply
to these very witnesses. No previously selected covering is shrunk.
Source: `app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_actualMaskFamily_with_retarded_radii
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ f : ActualMaskFamily Ω x RQ A₀ K M, ∀ p : f.centers,
      (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4 := by
  classical
  let Z := {ξ : E | ξ ∈ K ∧ determinant A₀ ξ = 0}
  have hc (p : Z) : ∃ c : LocalChart Ω x RQ A₀ p.val M,
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 :=
    exists_localChart_with_retarded_radii hΩ x hRQ hKΩ A₀ p.val
      (fun hz ↦ hKzero (hz ▸ p.property.1)) p.property.2
      (hregular p.val p.property.1 p.property.2) hM
  let charts : ∀ p : Z, LocalChart Ω x RQ A₀ p.val M := fun p ↦ (hc p).choose
  -- Repeat only the finite selection from `Selection`, using the enriched charts.
  obtain ⟨s, χ, ε₀, hε₀, δ, hδ, hχ, hrange, hcompact, hsupp, hsum, hstable⟩ :=
    exists_finite_pencil_masks A₀ hK (fun p : Z ↦ (charts p).angularNeighborhood)
      (fun p ↦ (charts p).isOpen_angularNeighborhood) (by
        intro ξ hξ hp
        exact ⟨⟨ξ, hξ, hp⟩, (charts ⟨ξ, hξ, hp⟩).center_mem_angularNeighborhood⟩)
  let chart : ∀ p : s, LocalChart Ω x RQ A₀ p.val.val M := fun p ↦ charts p.val
  obtain ⟨ε₁, hε₁, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : s ↦ (0 : ℝ)) (y := fun p ↦ (chart p).coefficientRadius)
    (fun p ↦ (chart p).coefficientRadius_pos)
  let V : Set E := ball x RQ ∩ ⋂ p : s, (chart p).physicalNeighborhood
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_iInter_of_finite fun p ↦ (chart p).isOpen_physicalNeighborhood)
  have hxV : x ∈ V := ⟨mem_ball_self hRQ,
    mem_iInter.mpr fun p ↦ (chart p).center_mem_physicalNeighborhood⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV x hxV
  have hball : closedBall x (4 * (r / 8)) ⊆ V :=
    (closedBall_subset_ball (by linarith : 4 * (r / 8) < r)).trans hrV
  obtain ⟨a, L, hL, ha, hap, _⟩ := exists_common_physical_radial_masks
    (fun p : s ↦ p.val.val) chart χ hsupp
  obtain ⟨input, output, hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, _⟩ :=
    exists_common_physical_masks x (show 0 < r / 8 by positivity)
  refine ⟨⟨s, chart, χ, a, min ε₀ ε₁, δ, r / 8, L, input, output,
    lt_min hε₀ hε₁, hδ, by positivity, hL, ?_,
    (fun y hy ↦ hKΩ (ball_subset_closedBall (hball hy).1)),
    (fun y hy ↦ ball_subset_closedBall (hball hy).1),
    (fun p y hy ↦ mem_iInter.mp (hball hy).2 p),
    hχ, hrange, hcompact, hsupp, hsum, ha, hap,
    hi, ho, hir, hor, hic, hoc, his, hos, hop, hip, ?_⟩, ?_⟩
  · intro p
    exact (min_le_right _ _).trans (by simpa using (hsmall p).le)
  · intro Q X hQ
    exact hstable Q X fun y hy ↦ (hQ y hy).trans (min_le_left _ _)
  · intro p
    exact (hc p.val).choose_spec

end JanetCartan.RegularSector.FiniteMasks.ActualFamily
