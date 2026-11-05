module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Limit
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Removing the frequency cutoff in the pure graph

The consumer is the primitive low bound in actual-calculus Step 1
(`app:ch_regular_base:thm:actual-calculus`). This leaf constructs the unique
bounded extension using the existing Fatou/density theorem, then proves its
Schwartz realization and strong convergence of the literal adjoints. Its
explicit uniform compact-graph bound must be supplied by the primitive normal
estimate; it is not an unconditional low-bound theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Pointwise convergence of the actual L² representatives on compact smooth
tests. Countably many null sets suffice to use the literal integral convergence
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem compactVectorGraph_cut_tendsto_ae
    {S : E → E → ℝ} {A : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set E} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (u : graphTestSpace n r) :
    ∀ᵐ x ∂volume, Tendsto (fun j ↦ compactVectorGraph hS
      (cutAmplitude_entry_continuous hA j) (cutAmplitude_entry_hasCompactSupport hK hsA j)
      (graphTestToLp u) x) atTop
      (𝓝 (WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
        (graphTestToSchwartz u) x))) := by
  have he : ∀ᵐ x ∂volume, ∀ j : ℕ, compactVectorGraph hS
      (cutAmplitude_entry_continuous hA j) (cutAmplitude_entry_hasCompactSupport hK hsA j)
      (graphTestToLp u) x = WithLp.toLp 2
        (graphOperator S (fun z _ η ↦ cutAmplitude A j z η) (graphTestToSchwartz u) x) := by
    apply ae_all_iff.mpr
    intro j
    simpa only [schwartzVectorToLp_graphTestToSchwartz, Filter.EventuallyEq] using
      compactVectorGraph_schwartz_ae hS (cutAmplitude_entry_continuous hA j)
        (cutAmplitude_entry_hasCompactSupport hK hsA j) (graphTestToSchwartz u)
  filter_upwards [he] with x hx
  simp_rw [hx]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).continuousAt.tendsto.comp
    (FrequencyCutoff.graphOperator_tendsto S A (graphTestToSchwartz u) x
      (hS.comp (continuous_const.prodMk continuous_id))
      (hA.comp (continuous_const.prodMk continuous_id)) C k (hb x))

/-- Construct the pure graph from a proved uniform compact-graph bound. Fatou
and density produce `T`; uniform boundedness and test convergence give its
strong limit on all L², hence its literal Schwartz realization. The exact
right Fourier multiplier identity then gives strong adjoint convergence.
The consuming primitive construction must discharge `hbound`; no limiting
operator or convergence is assumed. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem exists_graphL2_of_cutoff_bound
    {S : E → E → ℝ} {A : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
    {K : Set E} (hK : IsCompact K) (hsA : ∀ x η, x ∉ K → A x η = 0)
    (C : ℝ) (k : ℕ) (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ j, ‖compactVectorGraph hS (cutAmplitude_entry_continuous hA j)
      (cutAmplitude_entry_hasCompactSupport hK hsA j)‖ ≤ B) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ B ∧ ‖T.adjoint‖ ≤ B ∧
      (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
          (graphTestToSchwartz u) x)) ∧
      (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) ∧
      (∀ f : H, Tendsto (fun j ↦ compactVectorGraph hS
        (cutAmplitude_entry_continuous hA j) (cutAmplitude_entry_hasCompactSupport hK hsA j) f)
        atTop (𝓝 (T f))) ∧
      (∀ f : H, Tendsto (fun j ↦ (compactVectorGraph hS
        (cutAmplitude_entry_continuous hA j) (cutAmplitude_entry_hasCompactSupport hK hsA j)).adjoint f)
        atTop (𝓝 (T.adjoint f))) ∧
      ∀ U : H →L[ℂ] H, (∀ u : graphTestSpace n r, U (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
          (graphTestToSchwartz u) x)) → U = T := by
  let Tj : ℕ → H →L[ℂ] H := fun j ↦ compactVectorGraph hS
    (cutAmplitude_entry_continuous hA j) (cutAmplitude_entry_hasCompactSupport hK hsA j)
  obtain ⟨T, hT, hTa, htest, huniq⟩ := exists_graphLimit_extension Tj
    (fun u x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) (graphTestToSchwartz u) x))
    hB hbound (compactVectorGraph_cut_tendsto_ae hS hA hK hsA C k hb)
  have hequi : Equicontinuous (fun j ↦ (Tj j : H → H)) :=
    (LipschitzWith.uniformEquicontinuous _ ⟨B, hB⟩
      (fun j ↦ (Tj j).lipschitzWith.weaken (hbound j))).equicontinuous
  have hstrong (f : H) : Tendsto (fun j ↦ Tj j f) atTop (𝓝 (T f)) := by
    refine denseRange_graphTestToLp.induction_on
      (p := fun f : H ↦ Tendsto (fun j ↦ Tj j f) atTop (𝓝 (T f))) f
      (hequi.isClosed_setOfPred_tendsto T.continuous) ?_
    intro u
    have heq : T (graphTestToLp u) =
        (graphOperator_memLp S A (graphTestToSchwartz u) hS hA hK hsA C k hb).toLp
          (fun x ↦ WithLp.toLp 2
            (graphOperator S (fun z _ η ↦ A z η) (graphTestToSchwartz u) x)) :=
      Lp.ext ((htest u).trans (MemLp.coeFn_toLp _).symm)
    rw [heq]
    exact compactVectorGraph_cut_tendsto_graphTest S A u hS hA hK hsA C k hb
  have hschwartz (u : SchwartzMap E (Fin r → ℂ)) :
      T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x) := by
    have heq := tendsto_nhds_unique (hstrong (schwartzVectorToLp u))
      (compactVectorGraph_cut_tendsto S A u hS hA hK hsA C k hb)
    rw [heq]
    exact MemLp.coeFn_toLp _
  exact ⟨T, hT, hTa, htest, hschwartz, hstrong,
    compactVectorGraph_cut_adjoint_tendsto_of_realizes hS hA hK hsA T hschwartz, huniq⟩

end JanetCartan.FourierIntegral.LowBounds
