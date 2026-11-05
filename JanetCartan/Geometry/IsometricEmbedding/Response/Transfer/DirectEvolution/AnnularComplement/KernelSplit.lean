module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.ActualGraph.AllInputRealization.Graph
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Limit

/-!
# Subtracting the annular cut of the same full graph

The frequency localization in `app:ch_response:lem:energy-carrier-jets` is
performed in the two-position amplitude. Both physical masks and the high-pass
factor remain inside that amplitude. These identities never commute a
multiplier past its source position.

The uncut identity uses the existing source-integrability theorem and actual
strong graph realization. It constructs the complement's bounded realization
as the difference of the SAME full graph and its compact annular cut; a
complementary operator bound or realization is not a premise.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.SourceExpansion
open JanetCartan.AmplitudeBound
set_option maxHeartbeats 800000
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual outside-annulus amplitude; its source and output variables
are unchanged (`app:ch_response:lem:energy-carrier-jets`). -/
def annularComplementAmplitude (π : E → ℂ) (lam : ℝ) (A : FullAmplitude n r) :
    FullAmplitude n r :=
  frequencyCutFullAmplitude (fun ξ => 1 - π (lam⁻¹ • ξ)) A

/-- Pointwise amplitude subtraction, before taking any integral or limit. -/
theorem frequencyCut_complement_eq_sub (A : FullAmplitude n r) (q : E → ℂ) :
    frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A =
      A - frequencyCutFullAmplitude q A := by
  funext x z ξ
  simp [frequencyCutFullAmplitude, sub_smul]

/-- Literal adjoint conjugation of the complete complementary amplitude.
The matrix factor stays in its original order and both positions are retained. -/
theorem annularComplementAmplitude_conjTranspose (π : E → ℂ) (lam : ℝ)
    (A : FullAmplitude n r) (x z ξ : E) :
    (annularComplementAmplitude π lam A x z ξ).conjTranspose =
      (1 - star (π (lam⁻¹ • ξ))) • (A x z ξ).conjTranspose := by
  simp [annularComplementAmplitude, frequencyCutFullAmplitude, Matrix.conjTranspose_smul]

private theorem graphOperator_frequencyCut_eq (S : E → E → ℝ)
    (A : FullAmplitude n r) (q : E → ℂ) (u : E → Fin r → ℂ) (x : E) :
    graphOperator S (frequencyCutFullAmplitude q A) u x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ ξ, q ξ •
        ∫ z, graphOscillation S x z ξ • (A x z ξ).mulVec (u z) := by
  simp only [graphOperator, frequencyCutFullAmplitude, Matrix.smul_mulVec,
    smul_comm (graphOscillation S x _ _) (q _), integral_smul]

/-- Exact subtraction of the uncut literal integrals whenever the original
source integral is integrable. That integrability is supplied below by the
original finite symbol budget, not assumed as a remainder estimate. -/
theorem graphOperator_frequencyCut_complement (S : E → E → ℝ)
    (A : FullAmplitude n r) (q : E → ℂ) (u : E → Fin r → ℂ) (x : E)
    (hi : Integrable (fun ξ => ∫ z, graphOscillation S x z ξ • (A x z ξ).mulVec (u z)))
    (hq : AEStronglyMeasurable q volume) {Bq : ℝ} (hqb : ∀ ξ, ‖q ξ‖ ≤ Bq) :
    graphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A) u x =
      graphOperator S A u x - graphOperator S (frequencyCutFullAmplitude q A) u x := by
  have hqi := hi.bdd_smul Bq hq (Eventually.of_forall hqb)
  change Integrable (fun ξ => q ξ •
    ∫ z, graphOscillation S x z ξ • (A x z ξ).mulVec (u z)) at hqi
  rw [graphOperator_frequencyCut_eq, graphOperator_frequencyCut_eq]
  simp only [sub_smul, one_smul]
  rw [integral_sub hi hqi, smul_sub]
  rfl

/-- Compact-frequency all-input realization supplies its test specialization,
with the original physical `(2π)⁻ⁿ` normalization. -/
theorem fullGraphOperator_frequencyCut_test
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E => A p.1 p.2.1 p.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x z ξ, x ∉ X ∨ z ∉ Y → A x z ξ = 0)
    (q : E → ℂ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (u : graphTestSpace n r) :
    fullGraphOperator S (frequencyCutFullAmplitude q A) (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (frequencyCutFullAmplitude q A) u := by
  refine ((fullGraphOperator_frequencyCut_allInput S hS A hA hX hY hs q hq hqc).1
    (graphTestToLp u)).trans (Eventually.of_forall fun x => ?_)
  apply congrArg (WithLp.toLp 2)
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [(graphTest_memLp u).coeFn_toLp] with z hz
  rw [show graphTestToLp u z = u.val z from hz]

/-- The complement is the exact difference of the same uncut graph and its
amplitude cut, as an equality on ALL L² inputs. Its bounded realization is
constructed here. `hfull` is the literal test conclusion of
`FullLowBounds.exists_fullGraphFamily_of_primitive_inputs`; the next theorem
also obtains it directly from that producer's strong regularizations.
Only the original low symbol budget is required for absolute source integration.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem fullGraphOperator_complement_eq_sub_of_realizes
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E => A p.1 p.2.1 p.2.2))
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hs : ∀ x z ξ, x ∉ X ∨ z ∉ Y → A x z ξ = 0)
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (q : E → ℂ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    {Bq : ℝ} (hqb : ∀ ξ, ‖q ξ‖ ≤ Bq)
    (hfull : ∀ u : graphTestSpace n r, fullGraphOperator S A (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S A u) :
    fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A) =
      fullGraphOperator S A - fullGraphOperator S (frequencyCutFullAmplitude q A) := by
  apply fullGraphOperator_eq_of_realizes
  intro u
  have hcut := fullGraphOperator_frequencyCut_test S hS A hA hX hY hs q hq hqc u
  filter_upwards [Lp.coeFn_sub (fullGraphOperator S A (graphTestToLp u))
    (fullGraphOperator S (frequencyCutFullAmplitude q A) (graphTestToLp u)), hfull u, hcut]
      with x hx hf hc
  change (fullGraphOperator S A (graphTestToLp u) -
    fullGraphOperator S (frequencyCutFullAmplitude q A) (graphTestToLp u)) x = _
  rw [hx, Pi.sub_apply, hf, hc]
  have hi := integrable_graph_sourceIntegral A hA μ hb S hS.continuous
    (fun z => (u.val z).ofLp) (PiLp.contDiff_ofLp.comp u.property.1)
    (u.property.2.comp_left rfl) x
  have he := graphOperator_frequencyCut_complement S A q (fun z => (u.val z).ofLp) x
    hi hq.continuous.aestronglyMeasurable hqb
  simpa only [graphTestOutput, ← WithLp.toLp_sub] using
    (congrArg (WithLp.toLp 2) he).symm

/-- Obtain the same uncut identity from the actual strong graph
regularizations. Compact test actions and the source-symbol budget prove
literal cutoff removal. No uncut action or remainder realization is assumed.
The actual producer of `hstrong` is `FullLowBounds` for the SAME original
phase and amplitude; it remains a sector-instantiation obligation.
Source: the frequency localization in `app:ch_response:lem:energy-carrier-jets`. -/
theorem fullGraphOperator_complement_eq_sub_of_strong_limit
    (hn : 0 < n) {R : ℝ}
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E => A p.1 p.2.1 p.2.2))
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
      fullGraphOperator S A - fullGraphOperator S (frequencyCutFullAmplitude q A) := by
  apply fullGraphOperator_complement_eq_sub_of_realizes S hS A hA hX hY hs μ hb q hq hqc hqb
  intro u
  exact graphTestOutput_eq_of_strong_source_regularization_limit hn A hbox hA μ hb
    S hS χ hχ hχc hχb hχlim (fullGraphOperator S A)
    (fun j => fullGraphOperator S (frequencyCutFullAmplitude (χ j) A)) u
    (fun j => fullGraphOperator_frequencyCut_test S hS A hA hX hY hs
      (χ j) (hχ j) (hχc j) u) (hstrong (graphTestToLp u))

/-- Literal Hilbert adjunction of the same subtraction. This is an operator
identity, so it holds on every input and retains reversed composition order.
The forward identity is proved from primitive source integration and actual
strong realization above, rather than postulated as an error estimate. -/
theorem fullGraphOperator_complement_adjoint_eq_sub
    (S : E → E → ℝ) (A : FullAmplitude n r) (q : E → ℂ)
    (h : fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A) =
      fullGraphOperator S A - fullGraphOperator S (frequencyCutFullAmplitude q A)) :
    (fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A)).adjoint =
      (fullGraphOperator S A).adjoint -
        (fullGraphOperator S (frequencyCutFullAmplitude q A)).adjoint := by
  rw [h]
  exact ContinuousLinearMap.adjoint.map_sub _ _

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
