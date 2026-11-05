module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.Family
public import JanetCartan.Analysis.Microlocal.FourierIntegral.BranchRealization
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.PairedBounds

/-!
# Integer Sobolev bounds for the constructed full graph

This assembles the whole-image low construction, the actual derivative-branch
realizations, and the supported Sobolev estimates. There are no operator-bound
or realization premises. The normal chart has a positive frequency collar;
the larger chart used for homogeneous differentiation is a cone. They are
kept distinct, since a nonempty cone cannot have a positive frequency collar.

The consumer is actual-calculus item (2), and subsequently the order-zero and
gain-one factors in the weighted inverse and complete residual. The primitive
phase, support, gap and symbol assumptions remain explicit. This does not
construct the particular Hamilton phase in item (1).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles SupportedSobolev FullLowBounds WholeImageGeometry
open NormalComparison LowBounds
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The same constructed full graph and its literal Hilbert adjoint satisfy
the natural-order tame estimates, including gain one for order minus one.
All low operators and branch realizations are constructed from the original
phase and amplitude data. Constants are chosen before the phase, amplitude,
and data; the high derivative reserve is `fullLowReserve n + 2 = 3*n+6`.

`D` is the homogeneous conic chart. The smaller `Dnormal` has the low-frequency
collar required for the whole averaged-gradient inverse. Only the latter
needs a smooth extension across its closed boundary; the exported operator
always uses the original phase. Source: `app:ch_regular_base:eq:fio-input`
and actual-calculus Steps 1--3. -/
theorem exists_fullGraph_integer_sobolev_constants_of_wholeImage_phase
    (hn : 0 < n) (R ℓ B₀ Bφ : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {gap ε : ℝ} (hgap : 0 < gap) (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a,
      ∀ (z : ι → Point n) (δ : ι → ℝ), (∀ i, 0 < δ i) →
      ∀ (U : ι → Set (Point n)) (V : Set (Point n)),
        (∀ i, IsOpen (U i)) → IsOpen V →
        (∀ i, Metric.closedBall (z i) (δ i) ⊆ U i) →
        (∀ i, ∀ t : ℝ, 1 ≤ t → ∀ p ∈ U i, (p.1, t • p.2) ∈ V) →
      ∀ (X D : Set E), IsOpen X → IsOpen D → Convex ℝ X →
        (∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D) →
        (∀ t : ℝ, 0 < t → ∀ η ∈ D, t • η ∈ D) →
      ∀ (M B c : ℝ), 0 ≤ M → 1 ≤ c →
      ∀ d : ℕ, (d = 0 ∨ d = 1) →
      ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
        (∀ y ∈ Y₀, ∀ i : Fin n, |y i| ≤ R) →
        IsClosed F₀ → (0 : E) ∉ F₀ → X₀ ⊆ X →
      ∀ (Dnormal : Set E) (O : Set (E × E)),
        IsOpen Dnormal → Dnormal ⊆ D → F₀ ⊆ Dnormal →
        IsOpen O → closure (X ×ˢ Dnormal) ⊆ O →
      ∀ (S : E → E → ℝ), ContDiffOn ℝ ∞ (Function.uncurry S) O →
        ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
        (∀ t : ℝ, 0 < t → ∀ x ∈ X, ∀ η ∈ D, S x (t • η) = t * S x η) →
        (∀ x ∈ X, ∀ η ∈ D, IsUnit (mixedPhaseMatrix S x η).det) →
        (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i),
          ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
        (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n + d + 2)
          (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
        (∀ x ∈ X, ∀ u ∈ Dnormal,
          ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun w ↦ S w v) x) u‖ ≤ B₀) →
        (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) Dnormal) →
        (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ Dnormal,
          gap ≤ |(averagedJacobian S x y u).det|) →
        (∀ u ∈ Dnormal, ε < ‖u‖) →
        (∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) a b,
          ∀ k ≤ wholeImagePhaseReserve n, ‖iteratedFDeriv ℝ k
            (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) p‖ ≤ Bφ) →
        (∀ x ∈ X, ‖x‖ ≤ R) →
      ∀ (A : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
        (∀ i j, if d = 0 then
          BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)
          else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
        (∀ i, (if d = 0 then
          normalizedSeminorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n) (uncurry A)
          else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (fullLowReserve n + 1) A)
            ≤ M) →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
        (∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ t : ℝ, 1 ≤ t ∧
          ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, t • v.2) ∧
            ρ p.2 ≤ t ∧ t ≤ c * ρ p.2) →
      ∀ W : H →L[ℂ] H,
        W = fullGraphOperator S A ∨ W = (fullGraphOperator S A).adjoint →
      ∀ u : H, MemVectorFourierSobolev ((s - d : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤ C *
            (vectorFourierSobolevNorm ((s - d : ℕ) : ℝ) u +
              normalizedGraphOrderHigh d z δ (s + (fullLowReserve n + 2)) S A * ‖u‖) := by
  obtain ⟨a, ha, b, hab, C₀, hC₀, hfamily⟩ :=
    exists_fullGraphFamily_of_wholeImage_phase (r := r) hn R ℓ B₀ Bφ hℓ hRcell hgap hε
  refine ⟨a, ha, b, hab, ?_⟩
  intro z δ hδ U V hU hV hball hrad X D hX hD hcX hchart hcone M B c hM hc d hd s
  obtain ⟨C, hC, hbound⟩ := exists_graph_adjoint_integer_sobolev_constant (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone (fullLowReserve n) hM
    B c (C₀ * (1 + M)) hc (mul_nonneg hC₀.le (by linarith)) d hd s
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hX₀ hY₀ hYbox hF₀ hF₀0 hXsub Dnormal O hDn hDsub hFsub hO hbuffer
    S hSO hS hhom hinv hmixGap hlowS hmix hinj hdet hcollar hphase hR
    A hA hbA hlowA ρ hρ hηρ hcover W hW u hu
  obtain ⟨χ, hχ, hχcompact, hχzero, _hχpreserve, hfamily⟩ :=
    hfamily X₀ Y₀ F₀ hX₀ hYbox hF₀ hF₀0
  obtain ⟨_hconstruct, hforward, hreverse⟩ :=
    hfamily X Dnormal O S hX hDn hcX hO hbuffer hSO
      (fun x hx η hη t ht _ ↦ hhom t ht x hx η (hDsub hη))
      hmix hinj hdet hcollar hphase hR hXsub hFsub
  let Ω : Set (Point n) := (X ×ˢ Set.univ) ×ˢ D
  have hΩ : IsOpen Ω := (hX.prod isOpen_univ).prod hD
  have hcarrier : (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ Ω :=
    fun _ hp ↦ ⟨⟨hXsub hp.1.1, Set.mem_univ _⟩, hDsub (hFsub hp.2)⟩
  have hsupported : SupportedPhaseRegularity S Ω := by
    intro p hp _
    exact hS.contDiffAt ((hX.prod hD).mem_nhds ⟨hp.1.1, hp.2⟩)
  have hinvSupported : SupportedMixedInvertibility S Ω :=
    fun p hp ↦ hinv p.1.1 hp.1.1 p.2 hp.2
  have hhomSupported : SupportedPhaseHomogeneity S Ω := by
    intro p hp _
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    filter_upwards [hX.mem_nhds hp.1.1] with x hx
    exact hhom t ht x hx p.2 hp.2
  have hinvChart : ∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det :=
    fun p hp ↦ hinv p.1.1 (hchart p hp).1 p.2 (hchart p hp).2
  obtain ⟨hreal, hlow, hadjoint, hlowForward, hlowReverse, hbranches⟩ :=
    BranchRealization.supported_graph_operator_inputs z δ hδ U hU hV hball hrad
      hX hD hchart hcone hM B c C₀ hc hC₀.le d hd hX₀ hY₀ hF₀ hF₀0 hΩ hcarrier
      S hsupported hinvSupported hS hhom hinvChart hmixGap hlowS χ A hA hbA hlowA
      ρ hρ hηρ hcover hforward hreverse
  exact hbound X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 Ω hΩ hcarrier S hsupported
    hinvSupported hhomSupported hS hhom hinvChart hmixGap hlowS χ hχ hχcompact hχzero
    (fullGraphOperator S) (reverseFullGraphOperator S) A hA hreal hlow hadjoint hbA hlowA
    ρ hρ hηρ hcover hlowForward (hbranches s).1 hlowReverse (hbranches s).2 W hW u hu

end JanetCartan.FourierIntegral
