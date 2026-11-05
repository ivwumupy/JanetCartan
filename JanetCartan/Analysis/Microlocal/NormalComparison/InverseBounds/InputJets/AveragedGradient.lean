module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Differential
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral

/-!
# Quantitative spatial jets of the averaged gradient

For `app:ch_osc:setup:osc-normal` and `app:ch_osc:prop:osc-normal`, the
order-`k` jet of the actual averaged gradient on `X × X × D` is bounded by
`3 ^ k * |C (k + 1)|`. Both physical positions remain independent. The
constant is defined before the phase, and the generic result can also be
applied to a parameter-differentiated phase once its spatial bounds are known.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.NormalComparison

variable {n : ℕ}

/-- The physical differential evaluated along the segment, using the full
spatial differential (`app:ch_osc:setup:osc-normal`). -/
def segmentPhaseDifferential (φ : Euclidean n → Euclidean n → ℝ)
    (t : ℝ) (q : Euclidean n × (Euclidean n × Euclidean n)) : Euclidean n →L[ℝ] ℝ :=
  phaseDifferentialRestriction n
    (fderiv ℝ (Function.uncurry φ) (averagedGradientSegmentInput n t q))

/-- Joint smoothness of the segment differential follows from the phase
on the open convex box (`app:ch_osc:setup:osc-normal`). -/
theorem segmentPhaseDifferential_contDiffAt
    {φ : Euclidean n → Euclidean n → ℝ} {X D : Set (Euclidean n)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    {z : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ (X ×ˢ (X ×ˢ D))) :
    ContDiffAt ℝ ∞ (fun w ↦ segmentPhaseDifferential φ w.1 w.2) z := by
  have hm : averagedGradientSegmentInput n z.1 z.2 ∈ X ×ˢ D :=
    ⟨hcX.add_smul_sub_mem hz.2.2.1 hz.2.1 hz.1, hz.2.2.2⟩
  have hd := (hφ.contDiffAt ((hX.prod hD).mem_nhds hm)).fderiv_right (m := ∞) (by simp)
  exact (phaseDifferentialRestriction n).contDiff.contDiffAt.comp z
    (hd.comp z (((contDiffAt_snd.snd.fst.add (contDiffAt_fst.smul
      (contDiffAt_snd.fst.sub contDiffAt_snd.snd.fst))).prodMk contDiffAt_snd.snd.snd)))

/-- Spatial differentiation of the segment differential costs one phase
derivative and at most `3 ^ k` (`app:ch_osc:prop:osc-normal`). -/
theorem norm_iteratedFDeriv_segmentPhaseDifferential_le
    {φ : Euclidean n → Euclidean n → ℝ} {X D : Set (Euclidean n)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    {C : ℕ → ℝ} {k : ℕ}
    (hb : ∀ z ∈ X ×ˢ D, ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry φ) z‖ ≤ C (k + 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ X ×ˢ (X ×ˢ D)) :
    ‖iteratedFDeriv ℝ k (segmentPhaseDifferential φ t) q‖ ≤ averagedGradientJetBound C k := by
  let L := averagedGradientSegmentInput n t
  have hm : L q ∈ X ×ˢ D :=
    ⟨hcX.add_smul_sub_mem hq.2.1 hq.1 ht, hq.2.2⟩
  have hd : ContDiffOn ℝ ∞
      (fun z ↦ phaseDifferentialRestriction n (fderiv ℝ (Function.uncurry φ) z)) (X ×ˢ D) := by
    intro z hz
    exact ((phaseDifferentialRestriction n).contDiff.contDiffAt.comp z
      ((hφ.contDiffAt ((hX.prod hD).mem_nhds hz)).fderiv_right (by simp))).contDiffWithinAt
  calc
    _ ≤ ‖iteratedFDeriv ℝ k
        (fun z ↦ phaseDifferentialRestriction n (fderiv ℝ (Function.uncurry φ) z)) (L q)‖ * ‖L‖ ^ k :=
      norm_iteratedFDeriv_comp_linear_on_open_le L (hX.prod hD) hd hm k
    _ ≤ ‖iteratedFDeriv ℝ (k + 1) (Function.uncurry φ) (L q)‖ * ‖L‖ ^ k := by
      gcongr
      exact norm_iteratedFDeriv_phaseDifferential_le
        (hφ.contDiffAt ((hX.prod hD).mem_nhds hm)) k
    _ ≤ |C (k + 1)| * 3 ^ k := by
      gcongr
      · exact (hb _ hm).trans (le_abs_self _)
      · exact norm_averagedGradientSegmentInput_le n ht
    _ = _ := mul_comm _ _

/-- The segment differential is the actual integrand defining the averaged
gradient (`app:ch_osc:setup:osc-normal`). -/
theorem segmentPhaseDifferential_eq
    {φ : Euclidean n → Euclidean n → ℝ} {X D : Set (Euclidean n)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ X ×ˢ (X ×ˢ D)) :
    segmentPhaseDifferential φ t q =
      fderiv ℝ (fun x ↦ φ x q.2.2) (q.2.1 + t • (q.1 - q.2.1)) := by
  exact phaseDifferentialRestriction_fderiv (z := averagedGradientSegmentInput n t q)
    ((hφ.contDiffAt (x := averagedGradientSegmentInput n t q) ((hX.prod hD).mem_nhds
      ⟨hcX.add_smul_sub_mem hq.2.1 hq.1 ht, hq.2.2⟩)).differentiableAt (by simp))

/-- Quantitative spatial jets of the actual averaged gradient of any smooth
scalar phase on an open box with convex physical domain
(`app:ch_osc:setup:osc-normal`, `app:ch_osc:prop:osc-normal`). -/
theorem norm_iteratedFDeriv_averagedGradient_le
    {φ : Euclidean n → Euclidean n → ℝ} {X D : Set (Euclidean n)}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    {C : ℕ → ℝ} {N k : ℕ}
    (hb : ∀ j ≤ N, ∀ z ∈ X ×ˢ D, ‖iteratedFDeriv ℝ j (Function.uncurry φ) z‖ ≤ C j)
    (hk : k + 1 ≤ N)
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ X ×ˢ (X ×ˢ D)) :
    ‖iteratedFDeriv ℝ k (fun w ↦ averagedGradient φ w.1 w.2.1 w.2.2) q‖ ≤
      averagedGradientJetBound C k := by
  let H := fun z : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
    segmentPhaseDifferential φ z.1 z.2
  have hH : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (X ×ˢ (X ×ˢ D)), ContDiffAt ℝ ∞ H z :=
    fun _ hz ↦ segmentPhaseDifferential_contDiffAt hX hD hcX hφ hz
  have hB : ∀ j ≤ k, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ X ×ˢ (X ×ˢ D),
      ‖iteratedFDeriv ℝ j (fun x ↦ H (t, x)) y‖ ≤ averagedGradientJetBound C j := by
    intro j hj t ht y hy
    exact norm_iteratedFDeriv_segmentPhaseDifferential_le hX hD hcX hφ
      (hb (j + 1) (by omega)) ht hy
  have heq : (fun w ↦ averagedPhaseDifferential φ w.1 w.2.1 w.2.2) =ᶠ[𝓝 q]
      (fun w ↦ ∫ t in (0 : ℝ)..1, H (t, w)) := by
    filter_upwards [(hX.prod (hX.prod hD)).mem_nhds hq] with w hw
    apply intervalIntegral.integral_congr
    intro t ht
    exact (segmentPhaseDifferential_eq hX hD hcX hφ (by simpa using ht) hw).symm
  change ‖iteratedFDeriv ℝ k
    ((InnerProductSpace.toDual ℝ (Euclidean n)).symm ∘
      (fun w ↦ averagedPhaseDifferential φ w.1 w.2.1 w.2.2)) q‖ ≤ _
  rw [(InnerProductSpace.toDual ℝ (Euclidean n)).symm.norm_iteratedFDeriv_comp_left,
    (heq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact norm_iteratedFDeriv_unitIntervalIntegral_le (hX.prod (hX.prod hD)) hH hB hq

/-- The manuscript's input budget gives the averaged-gradient spatial jets
through `k + 1 ≤ 20 * (n + 1)`, uniformly in the parameter and both physical
positions (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.averagedGradient_spatial_jet_bound
    {r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {k : ℕ} (hk : k + 1 ≤ 20 * (n + 1))
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) :
    ‖iteratedFDeriv ℝ k (fun w ↦ averagedGradient (F.phase ε) w.1 w.2.1 w.2.2) q‖ ≤
      averagedGradientJetBound C k := by
  exact norm_iteratedFDeriv_averagedGradient_le G.isOpen_X G.isOpen_D G.convex_X
    (F.phase_contDiffOn_spatial (F.parameter_subset hε))
    (fun _ hj _ hz ↦ (F.input_jet_bounds hε hz hj).1) hk hq

end JanetCartan.NormalComparison
