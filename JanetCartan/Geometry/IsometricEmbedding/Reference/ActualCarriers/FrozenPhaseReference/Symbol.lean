module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol

/-!
# The literal frozen Hamilton symbol

The reference symbol for Steps 1–2 of `app:ch_seed:prop:seed-actual-menu`.
These identities supply the position-independent Hamiltonian to the reference
chart construction; no flow or phase identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase NormalizedSymbol

/-- The constant cube frame, with precisely the normalization used in
`app:ch_seed:prop:seed-actual-menu`, Step 1. -/
def frozenSymbol (n : ℕ) : HomogeneousSymbol (Euclidean n) :=
  normalizedHomogeneousSymbol isOpen_univ (fun _ ↦ cubeStress n) contDiffOn_const

/-- The reference domain excludes exactly the zero covectors
(`app:lem:common-hamilton-phase`). -/
@[simp] theorem mem_frozenSymbol_domain {n : ℕ} (q : Euclidean n × Euclidean n) :
    q ∈ (frozenSymbol n).domain ↔ q.2 ≠ 0 := by
  simp [frozenSymbol, normalizedHomogeneousSymbol, normalizedSymbolDomain]

/-- Literal scalar formula for the frozen symbol
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem frozenSymbol_h {n : ℕ} (q : Euclidean n × Euclidean n) :
    (frozenSymbol n).h q = ‖q.2‖ ^ (1 - (n : ℤ)) * cubeDeterminant q.2 := by
  simpa [frozenSymbol] using normalizedHomogeneousSymbol_h isOpen_univ
    (fun _ : Euclidean n ↦ cubeStress n) contDiffOn_const q

/-- Smoothness on the actual punctured domain, for the common buffered-chart
construction in `app:lem:common-hamilton-phase`. -/
theorem frozenSymbol_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (frozenSymbol n).h (frozenSymbol n).domain :=
  contDiffOn_normalizedSymbol isOpen_univ contDiffOn_const

/-- There is no physical force for the constant frame. This is the input to
momentum conservation in the affine reference phase proof
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem frozenSymbol_hx_eq_zero {n : ℕ} {q : Euclidean n × Euclidean n}
    (hq : q ∈ (frozenSymbol n).domain) : (frozenSymbol n).hx q = 0 := by
  change physicalGradient (frozenSymbol n).h q = 0
  rw [physicalGradient_eq_gradient
    ((frozenSymbol n).hasFDerivAt_h q hq).differentiableAt]
  simp only [frozenSymbol_h]
  simp [gradient]

/-- The adapted Hamilton derivative has the positive determinant sign on the
characteristic set (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem frozenSymbol_transverse_pos {n : ℕ} {x ξ ν : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0)
    (hgap : 0 < fderiv ℝ cubeDeterminant ξ ν) :
    0 < ⟪(frozenSymbol n).hp (x, ξ), ν⟫_ℝ := by
  have heq : determinant (cubeStress n) = cubeDeterminant :=
    funext determinant_cubeStress
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hh := normalizedHomogeneousSymbol_transverse_gap isOpen_univ
    (fun _ : Euclidean n ↦ cubeStress n) contDiffOn_const
    (z := (x, ξ)) ⟨mem_univ _, hξ⟩ ν hnorm hgap le_rfl le_rfl
    (by simpa using hchar) (by rw [heq])
  exact lt_of_lt_of_le (mul_pos (div_pos hnorm (pow_pos hnorm _)) hgap) hh

end JanetCartan.ActualCarriers.FrozenPhaseReference
