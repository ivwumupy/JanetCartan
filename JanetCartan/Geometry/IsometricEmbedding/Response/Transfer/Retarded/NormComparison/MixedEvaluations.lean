module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.UnivGrade

/-!
# Ordered mixed evaluations of Euclidean jets

Shared finite-dimensional interface for the norm comparison in
`app:ch_osc:prop:osc-retarded-tube`, consumed by the actual envelope estimate
`app:ch_response:eq:fixed-factor-transfer`. Time directions precede the ordered
transverse word. No distinct-word quotient or multiplicity cancellation is used.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ResponseTransfer

open RetardedSobolev.Spaces LocalSobolev

/-- Total order of an actual retarded mixed jet
(`app:ch_osc:prop:osc-retarded-tube`). -/
def retardedJetOrder {d s : ℕ} (i : JetIndex d s) : ℕ := i.2.2.val + i.1.val

/-- Every mixed jet has order at most its Sobolev grade
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem retardedJetOrder_le {d s : ℕ} (i : JetIndex d s) : retardedJetOrder i ≤ s := by
  have := i.1.isLt
  have := i.2.2.isLt
  dsimp [retardedJetOrder]
  omega

/-- The Euclidean coordinate directions of the ordered time/transverse jet.
The definition also applies when there are no transverse coordinates
(`app:ch_osc:prop:osc-retarded-tube`). -/
def retardedJetDirections {d s : ℕ} (i : JetIndex d s) :
    Fin (retardedJetOrder i) → Euclidean (d + 1) :=
  fun q ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ
    (Fin.addCases (fun _ : Fin i.2.2.val ↦ 0) (fun r ↦ (i.2.1 r).succ) q)

/-- Mixed evaluations of a family of multilinear jets, retaining all ordered
word multiplicities (`app:ch_osc:prop:osc-retarded-tube`). -/
def retardedJetEvaluation {d s : ℕ}
    (J : (j : ℕ) → (Euclidean (d + 1)) [×j]→L[ℝ] ℂ) (i : JetIndex d s) : ℂ :=
  J (retardedJetOrder i) (retardedJetDirections i)

/-- Mixed coordinate evaluations are bounded by the full Fréchet operator norm
with constant one (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem norm_retardedJetEvaluation_le {d s : ℕ}
    (J : (j : ℕ) → (Euclidean (d + 1)) [×j]→L[ℝ] ℂ) (i : JetIndex d s) :
    ‖retardedJetEvaluation J i‖ ≤ ‖J (retardedJetOrder i)‖ := by
  simpa [retardedJetEvaluation, retardedJetDirections,
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).norm_eq_one] using
    (J (retardedJetOrder i)).le_opNorm (retardedJetDirections i)

end JanetCartan.ResponseTransfer
