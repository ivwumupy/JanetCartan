module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets.InputJacobian
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InverseJetInduction

/-!
# Joint inverse jets on arbitrary open image domains

The inverse-jet induction is applied to the covector alone, whose zeroth jet
is bounded by the source radius. Positive jets of both position coordinates
are then restored. The consumer is `exists_normalizedWholeImage_jet_bounds`
for `app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison NormalComparison.InverseChartJet
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Differentiate the inverse equation on an arbitrary open part of the joint
image, keeping both physical positions. This is the whole-image version of
`UniformNormalData.inverseChart_fderiv_eq`, used in actual-calculus Step 1. -/
theorem jointInverse_fderiv_eq
    {φ : E → E → ℝ} {X D : Set E} {U : Set (NormalVariables n)}
    {g : NormalVariables n → E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (fun q ↦ (q.1, (q.2.1, g q))) U (X ×ˢ (X ×ˢ D)))
    (heq : ∀ q ∈ U, averagedGradient φ q.1 q.2.1 (g q) = q.2.2)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q ∈ X ×ˢ (X ×ˢ D), δ ≤ |(averagedJacobian φ q.1 q.2.1 q.2.2).det|)
    {z : NormalVariables n} (hz : z ∈ U) :
    fderiv ℝ g z = (averagedJacobian φ z.1 z.2.1 (g z)).inverse ∘L
      (chartOutputMap E - fderiv ℝ
        (fun q : NormalVariables n ↦ averagedGradient φ q.1 q.2.1 q.2.2)
        (z.1, (z.2.1, g z)) ∘L chartBaseMap E) := by
  let f : NormalVariables n → E := fun q ↦ averagedGradient φ q.1 q.2.1 q.2.2
  let Q := chartBaseMap E
  let L := chartInputMap E
  let P := chartOutputMap E
  let T : NormalVariables n → NormalVariables n := fun q ↦ Q q + L (g q)
  have hTval (q : NormalVariables n) : T q = (q.1, (q.2.1, g q)) := by
    simp [T, Q, L, chartBaseMap, chartInputMap]
  have hmem : T z ∈ X ×ˢ (X ×ˢ D) := by rw [hTval]; exact hmap hz
  have hgd : DifferentiableAt ℝ g z :=
    (hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ f (T z) :=
    ((averagedGradient_contDiffOn hX hD hcX hφ).contDiffAt
      ((hX.prod (hX.prod hD)).mem_nhds hmem)).differentiableAt (by simp)
  have hEq : (f ∘ T) =ᶠ[𝓝 z] P := by
    filter_upwards [hU.mem_nhds hz] with q hq
    simpa [Function.comp_def, hTval, f, P, chartOutputMap] using heq q hq
  have hd : fderiv ℝ f (T z) ∘L (Q + L ∘L fderiv ℝ g z) = P := by
    have hc := hf.hasFDerivAt.comp z (Q.hasFDerivAt.add (L.hasFDerivAt.comp z hgd.hasFDerivAt))
    exact hc.fderiv.symm.trans (hEq.fderiv_eq.trans P.fderiv)
  let a := averagedJacobian φ z.1 z.2.1 (g z)
  have ha : fderiv ℝ f (T z) ∘L L = a := by
    have hi : HasFDerivAt (fun u : E ↦ (z.1, (z.2.1, u))) L (g z) :=
      (hasFDerivAt_prodMk_right z.1 (z.2.1, g z)).comp (g z)
        (hasFDerivAt_prodMk_right z.2.1 (g z))
    have hc := (hTval z ▸ hf).hasFDerivAt.comp (g z) hi
    simpa only [hTval, f, a, averagedJacobian, Function.comp_def] using hc.fderiv.symm
  have hsolve : a ∘L fderiv ℝ g z = P - fderiv ℝ f (T z) ∘L Q := by
    rw [ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc, ha] at hd
    exact eq_sub_of_add_eq' hd
  have hinv := isInvertible_of_det_gap hδ (hgap _ (hmap hz))
  change fderiv ℝ g z = a.inverse ∘L (P - fderiv ℝ f (z.1, (z.2.1, g z)) ∘L Q)
  rw [← hTval z, ← hsolve, ← ContinuousLinearMap.comp_assoc, hinv.inverse_comp_self]
  simp

/-- A determinant gap, forward jets and a covector radius bound give every
positive joint inverse jet on any open joint image domain. The constant is
chosen before the phase, charts and inverse. There is no zeroth bound on
physical positions and no common-target premise. This supplies the inverse
field of `PrimitiveNormalShellInputs` in actual-calculus Step 1. -/
theorem exists_jointInverse_jet_bound (N : ℕ) (B b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K > 0, ∀ (φ : E → E → ℝ) (X D : Set E) (U : Set (NormalVariables n))
      (g : NormalVariables n → E),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D) →
      IsOpen U → ContDiffOn ℝ ∞ g U →
      MapsTo (fun q ↦ (q.1, (q.2.1, g q))) U (X ×ˢ (X ×ˢ D)) →
      (∀ q ∈ U, averagedGradient φ q.1 q.2.1 (g q) = q.2.2) →
      (∀ q ∈ U, ‖g q‖ ≤ b) →
      (∀ q ∈ X ×ˢ (X ×ˢ D), δ ≤ |(averagedJacobian φ q.1 q.2.1 q.2.2).det|) →
      (∀ q ∈ X ×ˢ (X ×ˢ D), ∀ k ≤ N + 1, ‖iteratedFDeriv ℝ k
        (fun w : NormalVariables n ↦ averagedGradient φ w.1 w.2.1 w.2.2) q‖ ≤ B) →
      ∀ z ∈ U, ∀ k, 1 ≤ k → k ≤ N →
        ‖iteratedFDeriv ℝ k (fun q ↦ (q.1, (q.2.1, g q))) z‖ ≤ K := by
  let Q := chartBaseMap E
  let L := chartInputMap E
  let P := chartOutputMap E
  obtain ⟨J, _, hj⟩ := exists_inverse_field_jet_bound_of_det_gap («E» := E) N B hδ
  let M := (2 : ℝ)^N * max 0 J * (‖P‖ + ‖Q‖ * max 0 B)
  obtain ⟨K, _, hbound⟩ := exists_jet_bound_of_fderiv_eq_comp Q L N b M
  refine ⟨max 1 (‖Q‖ + ‖L‖ * K), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro φ X D U g hX hD hcX hφ hU hg hmap heq hb hgap hfjet
  let W := X ×ˢ (X ×ˢ D)
  let f : NormalVariables n → E := fun q ↦ averagedGradient φ q.1 q.2.1 q.2.2
  let a : NormalVariables n → E →L[ℝ] E := fun q ↦
    (averagedJacobian φ q.1 q.2.1 q.2.2).inverse
  let H : NormalVariables n → NormalVariables n →L[ℝ] E :=
    fun q ↦ a q ∘L (P - fderiv ℝ f q ∘L Q)
  have hW : IsOpen W := hX.prod (hX.prod hD)
  have hf : ContDiffOn ℝ ∞ f W := averagedGradient_contDiffOn hX hD hcX hφ
  have hJac := averagedJacobian_contDiffOn hX hD hcX hφ
  have ha : ContDiffOn ℝ ∞ a W := by
    intro q hq
    exact ((isInvertible_of_det_gap hδ (hgap q hq)).contDiffAt_map_inverse.comp q
      (hJac.contDiffAt (hW.mem_nhds hq))).contDiffWithinAt
  have hajet : ∀ q ∈ W, ∀ k ≤ N, ‖iteratedFDeriv ℝ k a q‖ ≤ J := by
    apply hj _ W hW (hJac.of_le (by simp)) hgap
    intro q hq k hk
    exact (norm_iteratedFDeriv_averagedJacobian_le hX hD hcX hφ hq k).trans
      (hfjet q hq (k + 1) (by omega))
  have hH : ContDiffOn ℝ ∞ H W := ha.clm_comp
    (contDiffOn_const.sub ((hf.fderiv_of_isOpen hW (m := ∞) (by simp)).clm_comp contDiffOn_const))
  have hgraph (z : NormalVariables n) : Q z + L (g z) = (z.1, (z.2.1, g z)) := by
    simp [Q, L, chartBaseMap, chartInputMap]
  have hgjet : ∀ z ∈ U, ∀ k ≤ N, ‖iteratedFDeriv ℝ k g z‖ ≤ K := by
    apply hbound g H U W hU hW hg hH
    · intro z hz
      change Q z + L (g z) ∈ W
      rw [hgraph]
      exact hmap hz
    · intro z hz
      rw [hgraph]
      exact jointInverse_fderiv_eq hX hD hcX hφ hU hg hmap heq hδ hgap hz
    · exact hb
    · intro z hz k hk
      exact norm_iteratedFDeriv_implicitCoefficient_le P Q hW hf ha hfjet hajet hz hk
  intro z hz k hk hkN
  have hgz := hg.contDiffAt (hU.mem_nhds hz)
  have hfun : (fun q ↦ (q.1, (q.2.1, g q))) = fun q ↦ Q q + (L ∘ g) q :=
    funext fun q ↦ (hgraph q).symm
  rw [hfun, fun_iteratedFDeriv_add_apply ((Q.contDiff (n := k)).contDiffAt)
    (((L.contDiff (n := k)).contDiffAt.comp z (hgz.of_le (by simp))))]
  apply (norm_add_le _ _).trans
  exact (add_le_add (norm_iteratedFDeriv_linear_pos_le Q z hk)
    ((L.norm_iteratedFDeriv_comp_left hgz (by simp)).trans
      (mul_le_mul_of_nonneg_left (hgjet z hz k hkN) (norm_nonneg L)))).trans
    (le_max_right _ _)

end JanetCartan.FourierIntegral.WholeImageGeometry
