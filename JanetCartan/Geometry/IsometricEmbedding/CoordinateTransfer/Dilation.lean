module

public import JanetCartan.Geometry.IsometricEmbedding.Local

/-!
# Undoing the final constant dilation

The last paragraph of Section 9 of paper.tex uses `r = s * ρ` and replaces a
solution `F` for `x ↦ g (r • x)` by `x ↦ r • F (r⁻¹ • x)`.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set TopologicalSpace

namespace JanetCartan

/-- Section 9, final paragraph: undo the simultaneous domain and target dilation. -/
def undoDilation {n N : ℕ} (r : ℝ) (F : Euclidean n → Euclidean N) :
    Euclidean n → Euclidean N := fun x ↦ r • F (r⁻¹ • x)

/-- Section 9: the two constant factors in the differential cancel. -/
theorem fderiv_undoDilation {n N : ℕ} {r : ℝ} (hr : r ≠ 0)
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (r⁻¹ • x)) :
    fderiv ℝ (undoDilation r F) x = fderiv ℝ F (r⁻¹ • x) := by
  have h := (hF.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r⁻¹)).const_smul r
  convert h.fderiv using 1
  · rfl
  · ext v
    simp [smul_smul, hr]


/-- Section 9: undoing dilation transports the induced metric by inverse dilation. -/
theorem inducedMetric_undoDilation {n N : ℕ} {r : ℝ} (hr : r ≠ 0)
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (r⁻¹ • x)) :
    inducedMetric (undoDilation r F) x = inducedMetric F (r⁻¹ • x) := by
  ext i j
  simp only [inducedMetric, partialDeriv, fderiv_undoDilation hr hF]

/-- Section 9: a single open domain supports every derivative order after dilation. -/
theorem contDiffOn_undoDilation {n N : ℕ} {r : ℝ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hF : ContDiffOn ℝ ∞ F s) :
    ContDiffOn ℝ ∞ (undoDilation r F) ((fun x ↦ r⁻¹ • x) ⁻¹' s) :=
  (hF.comp (contDiff_id.const_smul r⁻¹).contDiffOn (fun _ hx ↦ hx)).const_smul r

/-- Section 9, final metric identity: an actual solution for the dilated metric
produces an actual solution for the original metric on the dilated domain. -/
theorem isIsometricOn_undoDilation {n N : ℕ} {r : ℝ} (hr : r ≠ 0)
    {g : MetricField n} {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (hmetric : IsIsometricOn (fun x ↦ g (r • x)) F s) :
    IsIsometricOn g (undoDilation r F) ((fun x ↦ r⁻¹ • x) ⁻¹' s) := by
  intro x hx
  rw [inducedMetric_undoDilation hr
    ((hF.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)), hmetric hx]
  simp [smul_smul, hr]

/-- Section 9: dilation followed by the inverse-function restriction gives a smooth
local metric realization which is a topological embedding. -/
theorem exists_local_embedding_undoDilation {n N : ℕ} {r : ℝ} (hr : r ≠ 0)
    {g : MetricField n} {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    {p : Euclidean n} (hs : IsOpen s) (hp : r⁻¹ • p ∈ s)
    (hF : ContDiffOn ℝ ∞ F s)
    (hg : ∀ x ∈ (fun x ↦ r⁻¹ • x) ⁻¹' s, (g x).PosDef)
    (hmetric : IsIsometricOn (fun x ↦ g (r • x)) F s) :
    ∃ U : Opens (Euclidean n), p ∈ U ∧
      (U : Set (Euclidean n)) ⊆ (fun x ↦ r⁻¹ • x) ⁻¹' s ∧
      ContDiffOn ℝ ∞ (undoDilation r F) U ∧
      Topology.IsEmbedding (fun x : U ↦ undoDilation r F x.val) ∧
      IsIsometricOn g (undoDilation r F) U :=
  exists_local_embedding_of_isIsometricOn (hs.preimage (continuous_const_smul r⁻¹)) hp
    (contDiffOn_undoDilation hF) hg (isIsometricOn_undoDilation hr hs hF hmetric)

end JanetCartan
