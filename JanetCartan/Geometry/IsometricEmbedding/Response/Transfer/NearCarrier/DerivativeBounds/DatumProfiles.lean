module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.ParameterAssembly

/-!
# Pure parameter datum jets

The input family in the parameter paragraph of
`app:ch_response:thm:response-literal-transfer` has pure parameter derivatives
with spatial Sobolev profiles. This leaf records those actual derivatives on
the open parameter domain. It does not assume mixed spatial derivatives or
any output estimate. Conversion to `ParameterAssembly.HasMixedDatumJets`
remains a separate construction.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- The finite pure parameter datum jets of
`app:ch_response:thm:response-literal-transfer`. The head of a word is the
outermost derivative. Continuity and differentiation are local on `U`;
neither a global extension nor any mixed-jet estimate is required. -/
def HasPureParameterDatumJets (U : Set Y) (w : Fin m → Y) (N : ℕ)
    (G : List (Fin m) → Y → L2) : Prop :=
  (∀ z, z.length ≤ N → ContinuousOn (G z) U) ∧
    ∀ z, z.length < N → ∀ i t, t ∈ U →
      HasLineDerivAt ℝ (G z) (G (i :: z) t) t (w i)

/-- Every pure datum jet is its genuine ordered derivative in
`app:ch_response:thm:response-literal-transfer`, using the shared ordered-word
convention. Only the finite first-derivative identities are used. -/
theorem HasPureParameterDatumJets.orderedLineDeriv_eq
    {U : Set Y} (hU : IsOpen U) {w : Fin m → Y} {N : ℕ}
    {G : List (Fin m) → Y → L2} (hG : HasPureParameterDatumJets U w N G)
    (z : List (Fin m)) (hz : z.length ≤ N) (t : Y) (ht : t ∈ U) :
    orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) z (G []) t = G z t := by
  induction z generalizing t with
  | nil => rfl
  | cons i z ih =>
    have hzn : z.length < N := by simp only [List.length_cons] at hz; omega
    have heq : orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) z (G [])
        =ᶠ[𝓝 t] G z := by
      filter_upwards [hU.mem_nhds ht] with u hu
      exact ih (by omega) u hu
    exact (heq.lineDeriv_eq (v := w i)).trans (hG.2 z hzn i t ht).lineDeriv

end JanetCartan.IsometricEmbedding.Response.NearCarrier
