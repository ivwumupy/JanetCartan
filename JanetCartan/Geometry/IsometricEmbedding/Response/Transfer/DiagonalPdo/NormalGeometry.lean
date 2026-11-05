module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.UniformBranches
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.Realization.Bounded.LinearPhase
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Jets.Normalized

/-!
# Exact normal geometry of the full-frequency diagonal PDO

The physical normal map and its shell-normalized inverse are identities.
Their explicit unit derivative bounds and constant-two scale comparison
supply the same low-calculus inputs on every original shell, including zero.
Consumer: the diagonal full-amplitude carrier branch construction.
Sources: `app:ch_regular_base:eq:actual-normal-amplitude`, `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open FourierIntegral FourierIntegral.LowBounds NormalComparison WeightedPrincipalLocalization
section NormalGeometry
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "Nv" => NormalVariables n

/-- The physical diagonal normal map is literally the identity at every
covector (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem diagonal_normalForwardCoordinates :
    normalForwardCoordinates (fun x ξ : E ↦ inner ℝ x ξ) = id := by
  funext q
  simp [normalForwardCoordinates, averagedGradient_principal_linearPhase]

/-- The diagonal normal domain retains the original two physical positions
and every full covector (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem diagonal_bufferedNormalDomain (X : Set E) :
    bufferedNormalDomain X univ (fun x ξ : E ↦ inner ℝ x ξ) = X ×ˢ X ×ˢ univ := by
  ext q
  simp [bufferedNormalDomain, averagedGradient_principal_linearPhase]

/-- Exact shell normalization of the actual diagonal inverse, with no
frequency removed (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem diagonal_normalizedInverse {ρ : ℝ} (hρ : ρ ≠ 0) :
    normalInverseCoordinates (normalizedNormalInverse ρ (fun _ _ ξ : E ↦ ξ)) = id := by
  funext q
  simp [normalInverseCoordinates, normalizedNormalInverse, inv_smul_smul₀ hρ]

private theorem norm_iteratedFDeriv_identity_le (i : ℕ) (hi : 1 ≤ i) (z : Nv) :
    ‖iteratedFDeriv ℝ i (id : Nv → Nv) z‖ ≤ 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  rw [show fderiv ℝ (id : Nv → Nv) = (fun _ ↦ ContinuousLinearMap.id ℝ Nv) from
    funext (fun _ ↦ fderiv_id)]
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero] using
      (show ‖ContinuousLinearMap.id ℝ Nv‖ ≤ 1 from ContinuousLinearMap.norm_id_le)
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

/-- The original diagonal shell, including the low shoulder, has scale
comparison constant two (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem diagonal_normalShell_scale (X : Set E) (l : ℕ) (z : Nv)
    (hz : z ∈ normalDyadicShell (X ×ˢ X ×ˢ univ) l) :
    (2 : ℝ)^l ≤ 2 * (1 + ‖(2 : ℝ)^l • z.2.2‖) := by
  have h := hz.2.1
  have hs : Real.sqrt (1 + ‖(2 : ℝ)^l • z.2.2‖^2) ≤ 1 + ‖(2 : ℝ)^l • z.2.2‖ :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith [norm_nonneg ((2 : ℝ)^l • z.2.2)]⟩
  linarith

/-- All normalized diagonal inverse and Jacobian jets have unit bounds,
independent of the shell and the derivative order. These are the literal
inputs of the full-amplitude branch constructor
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem diagonal_normalShell_jets (l : ℕ) (z : Nv) :
    (∀ i, ‖iteratedFDeriv ℝ i (fun q : Nv ↦
      normalizedNormalJacobian ((2 : ℝ)^l)
        (fun _ _ _ : E ↦ ContinuousLinearMap.id ℝ E) q.1 q.2.1 q.2.2) z‖ ≤ 1) ∧
    ∀ i, 1 ≤ i → ‖iteratedFDeriv ℝ i
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (fun _ _ ξ : E ↦ ξ))) z‖ ≤ 1 := by
  constructor
  · intro i
    simp only [normalizedNormalJacobian]
    cases i with
    | zero => simpa only [norm_iteratedFDeriv_zero] using
        (show ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 from ContinuousLinearMap.norm_id_le)
    | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]
  · rw [diagonal_normalizedInverse (by positivity : (2 : ℝ)^l ≠ 0)]
    exact fun i hi ↦ norm_iteratedFDeriv_identity_le i hi z

end NormalGeometry
end JanetCartan.ResponseTransfer.DiagonalPdo
