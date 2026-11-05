module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSplit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.Locality

/-!
# The uncut split for the original supported phase

The original elapsed phase may be smooth only on its supported chart.
`exists_smooth_phase_extension` constructs an auxiliary smooth phase; the
existing locality theorems identify every cut and uncut operator with the
original phase before returning the result. No smoothness at spatial frequency
zero is imposed and the physical operator is unchanged.

Consumer: the complement in `app:ch_response:lem:energy-carrier-jets`, for the
original `app:ch_response:eq:direct-envelope-profile`. The actual supported
chart and original strong realization come from
`FullLowBounds` / `PrimitiveRealization.exists_fullGraphFamily_of_wholeImage_phase`
and the elapsed-time sector construction.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.SourceExpansion
open JanetCartan.AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Exact forward and literal-adjoint identities for the SAME original graph,
from the existing strong realizations, a smooth supported chart, and the
original finite source-symbol budget. The complement's realization is a
conclusion. The theorem covers the complete frequency complement of an
arbitrary compact selector, hence includes both shoulders and all tails.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem fullGraphOperator_complement_eq_sub_of_supported_strong_limit
    (hn : 0 < n) {R : ℝ}
    (S : E → E → ℝ) {D O : Set (E × E)}
    (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) O)
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E => A p.1 p.2.1 p.2.2))
    (hsD : ∀ x z ξ, A x z ξ ≠ 0 → (x, ξ) ∈ D)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x z ξ, x ∉ X ∨ z ∉ Y → A x z ξ = 0)
    (hbox : ∀ x ξ i j, SupportedInCenteredBox R (fun z => A x z ξ i j))
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (q : E → ℂ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    {Bq : ℝ} (hqb : ∀ ξ, ‖q ξ‖ ≤ Bq)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχc : ∀ j, HasCompactSupport (χ j)) (hχb : ∀ j ξ, ‖χ j ξ‖ ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun j => χ j ξ) atTop (𝓝 1))
    (hstrong : ∀ u : H, Tendsto
      (fun j => fullGraphOperator S (frequencyCutFullAmplitude (χ j) A) u)
      atTop (𝓝 (fullGraphOperator S A u))) :
    fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A) =
      fullGraphOperator S A - fullGraphOperator S (frequencyCutFullAmplitude q A) ∧
    (fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A)).adjoint =
      (fullGraphOperator S A).adjoint -
        (fullGraphOperator S (frequencyCutFullAmplitude q A)).adjoint := by
  obtain ⟨S', hS', he⟩ := exists_smooth_phase_extension S hD hO hDO hS
  have heA (x z ξ : E) (h : A x z ξ ≠ 0) : S' x ξ = S x ξ :=
    (he (x, ξ) (hsD x z ξ h)).eq_of_nhds
  have hfull := fullGraphOperator_phase_congr S S' A heA
  have hcut (θ : E → ℂ) :
      fullGraphOperator S' (frequencyCutFullAmplitude θ A) =
        fullGraphOperator S (frequencyCutFullAmplitude θ A) := by
    apply fullGraphOperator_phase_congr
    intro x z ξ h
    apply heA x z ξ
    intro hz
    exact h (by simp [frequencyCutFullAmplitude, hz])
  have hlim (u : H) : Tendsto
      (fun j => fullGraphOperator S' (frequencyCutFullAmplitude (χ j) A) u)
      atTop (𝓝 (fullGraphOperator S' A u)) := by
    simpa only [hfull, hcut] using hstrong u
  have hid := fullGraphOperator_complement_eq_sub_of_strong_limit hn S' hS' A hA
    hX hY hs hbox μ hb q hq hqc hqb χ hχ hχc hχb hχlim hlim
  rw [hcut, hfull, hcut] at hid
  exact ⟨hid, fullGraphOperator_complement_adjoint_eq_sub S A q hid⟩

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
