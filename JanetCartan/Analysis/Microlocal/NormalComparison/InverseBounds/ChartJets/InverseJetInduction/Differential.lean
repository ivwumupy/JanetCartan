module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InputJacobian

/-!
# The first inverse-chart differential

Differentiate the actual inverse equation of `app:ch_osc:setup:osc-normal`,
as used in Step 1 of `app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
namespace InverseChartJet
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Keep the physical coordinates and zero the input coordinate, for the
implicit differentiation in `app:ch_osc:prop:osc-normal`. -/
def chartBaseMap : (E × (E × E)) →L[ℝ] (E × (E × E)) :=
  (ContinuousLinearMap.fst ℝ E (E × E)).prod
    (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))).prod 0)

/-- Insert the unknown input coordinate (`app:ch_osc:prop:osc-normal`). -/
def chartInputMap : E →L[ℝ] (E × (E × E)) :=
  (ContinuousLinearMap.inr ℝ E (E × E)).comp (ContinuousLinearMap.inr ℝ E E)

/-- The target coordinate of the inverse equation (`app:ch_osc:setup:osc-normal`). -/
def chartOutputMap : (E × (E × E)) →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))

end InverseChartJet
open InverseChartJet
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Differentiate the actual inverse equation and solve with the inverse input
Jacobian (`app:ch_osc:prop:osc-normal`, Step 1). The base map freezes the input
coordinate, so the right-hand side contains no derivatives of the inverse. -/
theorem UniformNormalData.inverseChart_fderiv_eq (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {z : Euclidean n × (Euclidean n × Euclidean n)} (hz : z ∈ G.X ×ˢ (G.X ×ˢ G.V)) :
    fderiv ℝ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.inverseChart ε q.1 q.2.1 q.2.2) z =
    (fderiv ℝ (averagedGradient (F.phase ε) z.1 z.2.1)
      (F.inverseChart ε z.1 z.2.1 z.2.2)).inverse ∘L
      (chartOutputMap (Euclidean n) -
        fderiv ℝ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          averagedGradient (F.phase ε) q.1 q.2.1 q.2.2)
          (z.1, (z.2.1, F.inverseChart ε z.1 z.2.1 z.2.2)) ∘L
            chartBaseMap (Euclidean n)) := by
  let E := Euclidean n
  let S := E × (E × E)
  let U := G.X ×ˢ (G.X ×ˢ G.V)
  let W := G.X ×ˢ (G.X ×ˢ G.D)
  let g : S → E := fun q ↦ F.inverseChart ε q.1 q.2.1 q.2.2
  let f : S → E := fun q ↦ averagedGradient (F.phase ε) q.1 q.2.1 q.2.2
  let Q := chartBaseMap E
  let L := chartInputMap E
  let P := chartOutputMap E
  let T : S → S := fun q ↦ Q q + L (g q)
  have hTval (q : S) : T q = (q.1, (q.2.1, g q)) := by
    simp [T, Q, L, chartBaseMap, chartInputMap]
  have hU : IsOpen U := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_V)
  have hW : IsOpen W := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  have hmem : T z ∈ W := by
    rw [hTval]
    exact ⟨hz.1, hz.2.1, F.inverseChart_mem hε hz.1 hz.2.1 hz.2.2⟩
  have hg : DifferentiableAt ℝ g z :=
    ((F.inverseChart_spatial_contDiffOn hε).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ f (T z) :=
    ((F.averagedGradient_spatial_contDiffOn (F.parameter_subset hε)).contDiffAt
      (hW.mem_nhds hmem)).differentiableAt (by simp)
  have hEq : (f ∘ T) =ᶠ[𝓝 z] P := by
    filter_upwards [hU.mem_nhds hz] with q hq
    simpa [Function.comp_def, hTval, f, g, P, chartOutputMap] using
      F.averagedGradient_inverseChart hε hq.1 hq.2.1 hq.2.2
  have hd : fderiv ℝ f (T z) ∘L (Q + L ∘L fderiv ℝ g z) = P := by
    have hc := hf.hasFDerivAt.comp z (Q.hasFDerivAt.add (L.hasFDerivAt.comp z hg.hasFDerivAt))
    exact hc.fderiv.symm.trans (hEq.fderiv_eq.trans P.fderiv)
  let a := fderiv ℝ (averagedGradient (F.phase ε) z.1 z.2.1) (g z)
  have ha : fderiv ℝ f (T z) ∘L L = a := by
    have hi : HasFDerivAt (fun u : E ↦ (z.1, (z.2.1, u))) L (g z) :=
      (hasFDerivAt_prodMk_right z.1 (z.2.1, g z)).comp (g z)
        (hasFDerivAt_prodMk_right z.2.1 (g z))
    have hc := (hTval z ▸ hf).hasFDerivAt.comp (g z) hi
    simpa only [hTval, f, a, Function.comp_def] using hc.fderiv.symm
  have hsolve : a ∘L fderiv ℝ g z = P - fderiv ℝ f (T z) ∘L Q := by
    rw [ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc, ha] at hd
    exact eq_sub_of_add_eq' hd
  have hinv := F.jacobian_isInvertible hε hz.1 hz.2.1
    (F.inverseChart_mem hε hz.1 hz.2.1 hz.2.2)
  change fderiv ℝ g z = a.inverse ∘L (P - fderiv ℝ f (z.1, (z.2.1, g z)) ∘L Q)
  rw [← hTval z, ← hsolve, ← ContinuousLinearMap.comp_assoc, hinv.inverse_comp_self]
  simp

end JanetCartan.NormalComparison
