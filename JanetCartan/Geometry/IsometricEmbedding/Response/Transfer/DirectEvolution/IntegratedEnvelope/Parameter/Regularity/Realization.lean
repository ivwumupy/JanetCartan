module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.CompactRealization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.JointOperators

/-!
# Constructing the initial annular test realizations

The original compact carrier support gives compact source and frequency
projections. Together with the original output support, these discharge both
physical test identities needed for fixed-time parameter smoothness. No
operator realization is assumed. Source: `new:eq:carrier-ibp` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
open FourierIntegral FourierIntegral.FullLowBounds CompactTransfer BranchAmplitudes ModifiedLow
open FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Both test realizations of the restored initial branch follow from the
original supported primitive geometry. The second identity uses the literal
Hilbert adjoint after exchanging and conjugate-transposing the amplitude.
Consumer: fixed-time annular parameter smoothness (`new:eq:carrier-ibp`). -/
theorem initialBranch_test_realizations_of_supported_geometry
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (S : E → E → ℝ) (hS : Continuous (Function.uncurry S))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    {X : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    (c : P)
    (hslice : ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) →
      normalizedSlice c q ∈ U ×ˢ D)
    {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ) :
    let A := modifiedAmplitude lam p
      (normalizedTermAmplitude b f w₀ α initialJointTransferTerm c)
    (∀ u : graphTestSpace n r,
      fullGraphOperator S A (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
    (∀ u : graphTestSpace n r,
      (fullGraphOperator S (fun x y ξ => (A y x ξ).conjTranspose)).adjoint
        (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
          (reverseGraphOperator S (fun y z ξ => A z y ξ)
            (fun y => (u.val y).ofLp) x)) := by
  let κ := normalizedTermAmplitude b f w₀ α initialJointTransferTerm c
  let A := modifiedAmplitude lam p κ
  have hκ : ContDiff ℝ ∞ κ := contDiff_normalizedTermAmplitude b hU hD hα
    (contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hinv) [] _
    (by simp [jointTransferTerms, Pseudodifferential.orderedTransferAction]) c hslice
  have hA : Continuous (fun q : (E × E) × E => A q.1.1 q.1.2 q.2) :=
    (contDiff_modifiedAmplitude lam p hκ).continuous
  let Y := (fun w : CarrierVariables n => w.fst) '' K
  let Z := (fun w : CarrierVariables n => lam • w.snd) '' K
  have hY : IsCompact Y := hK.image (by fun_prop)
  have hZ : IsCompact Z := hK.image (by fun_prop)
  have hsupport (x y ξ : E) (hout : x ∉ X ∨ y ∉ Y ∨ ξ ∉ Z) : A x y ξ = 0 := by
    by_contra hn
    change (lam ^ p) • α (x, c) (WithLp.toLp 2 (y, lam⁻¹ • ξ)) ≠ 0 at hn
    have hnα : α (x, c) (WithLp.toLp 2 (y, lam⁻¹ • ξ)) ≠ 0 :=
      fun hz => hn (by rw [hz, smul_zero])
    have ht : normalizedSlice c ((x, y), lam⁻¹ • ξ) ∈ tsupport (Function.uncurry α) :=
      subset_tsupport _ hnα
    have hmem : WithLp.toLp 2 (y, lam⁻¹ • ξ) ∈ K :=
      hs (x, c) (hslice _ ht).1 hnα
    rcases hout with hx | hy | hξ
    · exact hx (houtput _ ht)
    · exact hy ⟨_, hmem, rfl⟩
    · exact hξ ⟨_, hmem, by simp [smul_smul, hlam]⟩
  have hforward := (compact_fullGraphOperator_realizations S hS A hA hX hY hZ hsupport).1
  have hreverse := (compact_fullGraphOperator_realizations S hS
    (fun x y ξ => (A y x ξ).conjTranspose)
    ((hA.comp ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd)).matrix_conjTranspose)
    hY hX hZ (fun x y ξ h => by
      rw [hsupport y x ξ (by tauto), Matrix.conjTranspose_zero])).2
  exact ⟨hforward, by simpa only [Matrix.conjTranspose_conjTranspose] using hreverse⟩

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
