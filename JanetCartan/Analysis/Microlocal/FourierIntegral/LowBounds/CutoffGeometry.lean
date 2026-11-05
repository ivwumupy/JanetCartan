module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Geometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.CompactSupport
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.GraphConvergence

/-!
# The fixed inverse geometry survives frequency truncation

The consumer is `exists_graphL2_of_primitive_cutoffs`, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. No new support buffer, inverse,
or geometric gap is needed for the constructed frequency cutoffs. The separate
quantitative cutoff-jet obligation is not asserted here.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Frequency truncation preserves every primitive buffered chart field, with
the same original carrier and closed image. This discharges the geometry input
for every regularization in actual-calculus Step 1. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem PrimitiveNormalGeometry.cutAmplitude
    {X D : Set E} {S : E → E → ℝ} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables n)}
    (G : PrimitiveNormalGeometry X D S A B η J W K) (j k : ℕ) :
    PrimitiveNormalGeometry X D S (cutAmplitude A j) (cutAmplitude B k) η J W K := by
  refine ⟨G.open_domain, G.inverse_smooth, G.mapsTo, ?_, G.gap,
    G.rightInverse, ?_, G.closed_image, G.buffer, ?_, ?_⟩
  · have hj : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ complexPhysicalCutoff j q.2.2) W :=
      ((complexPhysicalCutoff_contDiff j).comp contDiff_snd.snd).contDiffOn
    have hk : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ complexPhysicalCutoff k q.2.2) W :=
      ((complexPhysicalCutoff_contDiff k).comp contDiff_snd.snd).contDiffOn
    exact G.input_smooth.fst.prodMk
      ((hj.smul G.input_smooth.snd.fst).prodMk (hk.smul G.input_smooth.snd.snd))
  · intro q hq hleft hright
    apply G.carrier q hq
    · intro h
      exact hleft (by simp [FrequencyCutoff.cutAmplitude, h])
    · intro h
      exact hright (by simp [FrequencyCutoff.cutAmplitude, h])
  · intro x u hx
    simp [FrequencyCutoff.cutAmplitude, G.left_output x u hx]
  · intro y u hy
    simp [FrequencyCutoff.cutAmplitude, G.right_output y u hy]

/-- The actual frequency-cut carrier is contained in the original one; hence
forward continuity need only be supplied once. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem jointNormalCarrier_cutAmplitude_subset (A B : E → E → Mat) (j k : ℕ) :
    jointNormalCarrier (cutAmplitude A j) (cutAmplitude B k) ⊆ jointNormalCarrier A B := by
  intro q hq
  exact ⟨tsupport_smul_subset_right
    (fun p : E × E ↦ complexPhysicalCutoff j p.2) (Function.uncurry A) hq.1,
    tsupport_smul_subset_right
    (fun p : E × E ↦ complexPhysicalCutoff k p.2) (Function.uncurry B) hq.2⟩

end JanetCartan.FourierIntegral.LowBounds
