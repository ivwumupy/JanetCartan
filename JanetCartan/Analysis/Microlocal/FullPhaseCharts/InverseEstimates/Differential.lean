module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.JacobianBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differentiation of the fixed quotient-chart inverse

The inverse equation in `app:ch_seed:prop:seed-phase-charts` is differentiated
jointly, with every physical, normalized data and spectator variable retained.
`P` contains all parameters (including epsilon); `E` is the inverted data space.
The same statements apply to the full and transverse maps by changing `P` and
`E`. The forward map is expressed in the actual normalized coordinates; no
measure or change of data model is involved.

The smooth inverse, its equation, and its containment in the forward domain
are explicit inputs from the inverse-family construction. No inverse derivative
estimate is an input. These are conditional identities, not an existence theorem.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Retain all parameters and set the inverted data coordinate to zero, for
`app:ch_seed:prop:seed-phase-charts`. -/
def inverseBaseMap : (P × E) →L[ℝ] (P × E) :=
  (ContinuousLinearMap.fst ℝ P E).prod 0

/-- The actual inverse graph in `app:ch_seed:prop:seed-phase-charts`. -/
def inverseGraph (g : P × E → E) (z : P × E) : P × E := (z.1, g z)

/-- Joint inverse differentiation from the actual inverse equation of
`app:ch_seed:prop:seed-phase-charts`. All domains are fixed open buffered domains.
The only inverse-derivative premise is pointwise invertibility of the forward
input Jacobian. -/
theorem fderiv_inverse_eq
    {f g : P × E → E} {U W : Set (P × E)}
    (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (inverseGraph g) U W)
    (heq : ∀ z ∈ U, f (inverseGraph g z) = z.2)
    {z : P × E} (hz : z ∈ U)
    (hinv : (fderiv ℝ (fun u ↦ f (z.1, u)) (g z)).IsInvertible) :
    fderiv ℝ g z =
      (fderiv ℝ (fun u ↦ f (z.1, u)) (g z)).inverse ∘L
        (ContinuousLinearMap.snd ℝ P E -
          fderiv ℝ f (inverseGraph g z) ∘L inverseBaseMap) := by
  let Q : (P × E) →L[ℝ] (P × E) := inverseBaseMap
  let L := ContinuousLinearMap.inr ℝ P E
  let R := ContinuousLinearMap.snd ℝ P E
  have hg' := (hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hf' := (hf.contDiffAt (hW.mem_nhds (hmap hz))).differentiableAt (by simp)
  have hgraph : HasFDerivAt (inverseGraph g) (Q + L ∘L fderiv ℝ g z) z := by
    convert Q.hasFDerivAt.add (L.hasFDerivAt.comp z hg'.hasFDerivAt) using 1
    ext q <;> simp [inverseGraph, Q, L, inverseBaseMap]
  have hEq : (f ∘ inverseGraph g) =ᶠ[𝓝 z] R := by
    filter_upwards [hU.mem_nhds hz] with q hq
    exact heq q hq
  have hd : fderiv ℝ f (inverseGraph g z) ∘L (Q + L ∘L fderiv ℝ g z) = R :=
    (hf'.hasFDerivAt.comp z hgraph).fderiv.symm.trans (hEq.fderiv_eq.trans R.fderiv)
  have ha : fderiv ℝ f (inverseGraph g z) ∘L L =
      fderiv ℝ (fun u ↦ f (z.1, u)) (g z) :=
    (hf'.hasFDerivAt.comp (g z) (hasFDerivAt_prodMk_right z.1 (g z))).fderiv.symm
  rw [ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc, ha] at hd
  have hsolve := eq_sub_of_add_eq' hd
  change fderiv ℝ g z = _ ∘L (R - fderiv ℝ f (inverseGraph g z) ∘L Q)
  rw [← hsolve, ← ContinuousLinearMap.comp_assoc, hinv.inverse_comp_self]
  simp

/-- Parameter directions hold the output covector fixed. This specializes the
joint inverse identity to epsilon and to every physical or spectator direction
in `app:ch_seed:prop:seed-phase-charts`. -/
theorem fderiv_inverse_parameter_eq
    {f g : P × E → E} {U W : Set (P × E)}
    (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (inverseGraph g) U W)
    (heq : ∀ z ∈ U, f (inverseGraph g z) = z.2)
    {z : P × E} (hz : z ∈ U)
    (hinv : (fderiv ℝ (fun u ↦ f (z.1, u)) (g z)).IsInvertible) (v : P) :
    fderiv ℝ g z (v, 0) =
      -(fderiv ℝ (fun u ↦ f (z.1, u)) (g z)).inverse
        (fderiv ℝ f (inverseGraph g z) (v, 0)) := by
  rw [fderiv_inverse_eq hU hW hf hg hmap heq hz hinv]
  simp [inverseBaseMap]

/-- Higher joint identities are obtained by differentiating the proved first
inverse identity on the same open domain. This is the input to the inverse-jet
induction in the final paragraph of `app:ch_seed:prop:seed-phase-charts`;
the right-hand side consists of the actual forward differential, its pointwise
linear inverse, and the actual inverse graph. No high-jet bound is assumed. -/
theorem iteratedFDeriv_fderiv_inverse_eq
    {f g : P × E → E} {U W : Set (P × E)}
    (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (inverseGraph g) U W)
    (heq : ∀ z ∈ U, f (inverseGraph g z) = z.2)
    (hinv : ∀ z ∈ U, (fderiv ℝ (fun u ↦ f (z.1, u)) (g z)).IsInvertible)
    {z : P × E} (hz : z ∈ U) (r : ℕ) :
    iteratedFDeriv ℝ r (fderiv ℝ g) z =
      iteratedFDeriv ℝ r (fun q : P × E ↦
        (fderiv ℝ (fun u ↦ f (q.1, u)) (g q)).inverse ∘L
          (ContinuousLinearMap.snd ℝ P E -
            fderiv ℝ f (inverseGraph g q) ∘L inverseBaseMap)) z := by
  have h := iteratedFDerivWithin_congr (𝕜 := ℝ)
    (show EqOn (fderiv ℝ g) (fun q : P × E ↦
        (fderiv ℝ (fun u ↦ f (q.1, u)) (g q)).inverse ∘L
          (ContinuousLinearMap.snd ℝ P E -
            fderiv ℝ f (inverseGraph g q) ∘L inverseBaseMap)) U from
      fun q hq ↦ fderiv_inverse_eq hU hW hf hg hmap heq hq (hinv q hq)) hz r
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hz] using h

/-- The quantitative first parameter derivative from the fixed inverse gap,
used for the epsilon derivative in `app:ch_seed:prop:seed-phase-charts`.
The central equivalence is fixed before the phase or epsilon is chosen. -/
theorem norm_fderiv_inverse_parameter_le [FiniteDimensional ℝ E]
    (G : E ≃L[ℝ] E) {f g : P × E → E} {U W : Set (P × E)}
    (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo (inverseGraph g) U W)
    (heq : ∀ z ∈ U, f (inverseGraph g z) = z.2)
    {z : P × E} (hz : z ∈ U)
    (hgap : ‖(G.symm : E →L[ℝ] E) ∘L
      fderiv ℝ (fun u ↦ f (z.1, u)) (g z) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    (v : P) :
    ‖fderiv ℝ g z (v, 0)‖ ≤
      (2 * ‖(G.symm : E →L[ℝ] E)‖) *
        (‖fderiv ℝ f (inverseGraph g z)‖ * ‖v‖) := by
  have hi : (fderiv ℝ (fun u ↦ f (z.1, u)) (g z)).IsInvertible := by
    refine ⟨(LinearEquiv.ofBijective _ (bijective_of_normalized_gap G hgap)).toContinuousLinearEquiv, rfl⟩
  rw [fderiv_inverse_parameter_eq hU hW hf hg hmap heq hz hi, norm_neg]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  apply mul_le_mul (norm_inverse_le_of_normalized_gap G hgap)
    ?_ (norm_nonneg _) (by positivity)
  simpa using (fderiv ℝ f (inverseGraph g z)).le_opNorm (v, 0)

end JanetCartan.FullPhaseCharts.InverseEstimates
