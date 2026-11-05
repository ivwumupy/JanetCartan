module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.FrequencyIntegration
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives

/-!
# Differentiation of the full annular frequency integral

Dominated differentiation on the open joint physical/parameter neighborhood
for `app:ch_response:lem:energy-carrier-jets`. The hypotheses concern actual
derivatives of the source kernel, never derivatives of an asserted remainder.
The producer is `AnnularComplement.SourceBounds`; the consumer is the compact
vector Sobolev conversion in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement

variable {n : ℕ} {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrable bounds for every actual joint jet imply smoothness of the
full frequency integral on the original open neighborhood. This is the
regularity step of `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularIntegral_of_jet_majorants
    {κ : Euclidean n → X → F} {U : Set X} (hU : IsOpen U)
    (hκ : ∀ ξ, ContDiffOn ℝ ∞ (κ ξ) U)
    (hm : ∀ j z, z ∈ U →
      AEStronglyMeasurable (fun ξ ↦ iteratedFDeriv ℝ j (κ ξ) z) volume)
    (b : ℕ → Euclidean n → ℝ) (hi : ∀ j, Integrable (b j))
    (hb : ∀ j ξ z, z ∈ U → ‖iteratedFDeriv ℝ j (κ ξ) z‖ ≤ b j ξ) :
    ContDiffOn ℝ ∞ (fun z ↦ ∫ ξ, κ ξ z) U := by
  have hint (j : ℕ) (z : X) (hz : z ∈ U) :
      Integrable (fun ξ ↦ iteratedFDeriv ℝ j (κ ξ) z) :=
    (hi j).mono' (hm j z hz) (ae_of_all _ (fun ξ ↦ hb j ξ z hz))
  have he (j : ℕ) : EqOn
      (iteratedFDerivWithin ℝ j (fun z ↦ ∫ ξ, κ ξ z) U)
      (fun z ↦ ∫ ξ, iteratedFDeriv ℝ j (κ ξ) z) U := by
    intro z hz
    rw [iteratedFDerivWithin_of_isOpen j hU hz]
    exact MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
      (r := j) (b := b) hU
      (ae_of_all _ (fun ξ y hy ↦ ((hκ ξ).contDiffAt (hU.mem_nhds hy)).of_le (by simp)))
      (fun k _ y hy ↦ hm k y hy) (fun k _ ↦ hi k)
      (fun k _ ↦ ae_of_all _ (fun ξ y hy ↦ hb k ξ y hy)) le_rfl hz
  have hd (j : ℕ) (z : X) (hz : z ∈ U) : DifferentiableAt ℝ
      (fun y ↦ ∫ ξ, iteratedFDeriv ℝ j (κ ξ) y) z := by
    apply HasFDerivAt.differentiableAt
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun y ξ ↦ fderiv ℝ (iteratedFDeriv ℝ j (κ ξ)) y)
      (bound := b (j + 1)) (hU.mem_nhds hz)
    · exact Filter.mem_of_superset (hU.mem_nhds hz) (fun y hy ↦ hm j y hy)
    · exact hint j z hz
    · exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) ↦ X) F).continuous.comp_aestronglyMeasurable
          (hm (j + 1) z hz)
    · exact ae_of_all _ (fun ξ y hy ↦ by
        simpa only [norm_fderiv_iteratedFDeriv] using hb (j + 1) ξ y hy)
    · exact hi (j + 1)
    · exact ae_of_all _ (fun ξ y hy ↦
        (((hκ ξ).contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top j : (j : ℕ∞ω) < ∞)).hasFDerivAt)
  apply (contDiffOn_iff_continuousOn_differentiableOn hU.uniqueDiffOn).mpr
  constructor
  · intro j _
    exact ContinuousOn.congr
      (fun z hz ↦ (hd j z hz).continuousAt.continuousWithinAt) (he j)
  · intro j _
    exact DifferentiableOn.congr
      (fun z hz ↦ (hd j z hz).differentiableWithinAt) (he j)

/-- The actual joint derivative commutes with the uncut physical frequency
integral in `app:ch_response:lem:energy-carrier-jets`. The same integrable
majorants also prove smoothness, by the preceding theorem. -/
theorem iteratedFDeriv_annularIntegral_of_jet_majorants
    {κ : Euclidean n → X → F} {U : Set X} (hU : IsOpen U)
    (hκ : ∀ ξ, ContDiffOn ℝ ∞ (κ ξ) U)
    (hm : ∀ j z, z ∈ U →
      AEStronglyMeasurable (fun ξ ↦ iteratedFDeriv ℝ j (κ ξ) z) volume)
    (b : ℕ → Euclidean n → ℝ) (hi : ∀ j, Integrable (b j))
    (hb : ∀ j ξ z, z ∈ U → ‖iteratedFDeriv ℝ j (κ ξ) z‖ ≤ b j ξ)
    (j : ℕ) {z : X} (hz : z ∈ U) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ ξ, κ ξ y) z =
      ∫ ξ, iteratedFDeriv ℝ j (κ ξ) z :=
  MeasureEnvelopes.iteratedFDeriv_integral_of_dominated (r := j) hU
    (ae_of_all _ (fun ξ y hy ↦ ((hκ ξ).contDiffAt (hU.mem_nhds hy)).of_le (by simp)))
    (fun k _ y hy ↦ hm k y hy) (fun k _ ↦ hi k)
    (fun k _ ↦ ae_of_all _ (fun ξ y hy ↦ hb k ξ y hy)) le_rfl hz

/-- The displayed annular profiles supply all integrable majorants; there is
no domination hypothesis on the integrated output. Losses are fixed before
the source integration order. Consumer: differentiation and L² realization
in `app:ch_response:lem:energy-carrier-jets`. -/
theorem exists_annular_jet_majorants
    {κ : Euclidean n → X → F} {U : Set X}
    (dLoss : ℕ → ℝ) (s ell b : ℕ → ℕ) (C : ℕ → ℕ → ℝ)
    {ν lam L K A : ℝ}
    (hν : 0 < ν) (hνlt : ν < 1) (hlam : 1 ≤ lam)
    (hL : 1 ≤ L) (hLK : L ≤ K) (hK : K ≤ lam ^ (1 - ν))
    (hb : ∀ j N ξ z, z ∈ U → ‖iteratedFDeriv ℝ j (κ ξ) z‖ ≤
      C j N * A * lam ^ dLoss j * L ^ ell j * K ^ b j *
        (lam + ‖ξ‖) ^ s j * (K / (lam + ‖ξ‖)) ^ N) :
    ∃ B : ℕ → Euclidean n → ℝ, (∀ j, Integrable (B j)) ∧
      ∀ j ξ z, z ∈ U → ‖iteratedFDeriv ℝ j (κ ξ) z‖ ≤ B j ξ := by
  choose N _ hN using fun j ↦
    exists_annular_radial_precision n (s j) (ell j) (b j) (dLoss j) 0 hν hνlt
  refine ⟨fun j ξ ↦ (C j (N j) * A * lam ^ dLoss j * L ^ ell j * K ^ b j) *
    ((lam + ‖ξ‖) ^ s j * (K / (lam + ‖ξ‖)) ^ N j), ?_, ?_⟩
  · intro j
    exact ((hN j lam L K hlam hL hLK hK).1).const_mul _
  · intro j ξ z hz
    simpa only [mul_assoc] using hb j (N j) ξ z hz

/-- Uniform precision for the actual joint derivatives of the integrated
kernel, from the all-order source profiles. The constant precedes every
family member. This is the differentiated full-frequency deduction in
`app:ch_response:lem:energy-carrier-jets`, used separately for physical and
demodulated kernels. -/
theorem exists_annular_integral_jet_precision
    {I : Type*} {κ : I → Euclidean n → X → F} {U : Set X} (hU : IsOpen U)
    (hκ : ∀ i ξ, ContDiffOn ℝ ∞ (κ i ξ) U)
    (hm : ∀ i j z, z ∈ U →
      AEStronglyMeasurable (fun ξ ↦ iteratedFDeriv ℝ j (κ i ξ) z) volume)
    (dLoss : ℕ → ℝ) (s ell b : ℕ → ℕ) (C : ℕ → ℕ → ℝ)
    (hC : ∀ j N, 0 ≤ C j N) {ν : ℝ} (hν : 0 < ν) (hνlt : ν < 1)
    (lam L K A : I → ℝ) (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i)
    (hLK : ∀ i, L i ≤ K i) (hK : ∀ i, K i ≤ lam i ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i)
    (hb : ∀ j N i ξ z, z ∈ U → ‖iteratedFDeriv ℝ j (κ i ξ) z‖ ≤
      C j N * A i * lam i ^ dLoss j * L i ^ ell j * K i ^ b j *
        (lam i + ‖ξ‖) ^ s j * (K i / (lam i + ‖ξ‖)) ^ N) :
    (∀ i, ContDiffOn ℝ ∞ (fun z ↦ ∫ ξ, κ i ξ z) U) ∧
    (∀ i j z, z ∈ U →
      Integrable (fun ξ ↦ iteratedFDeriv ℝ j (κ i ξ) z) ∧
      iteratedFDeriv ℝ j (fun y ↦ ∫ ξ, κ i ξ y) z =
        ∫ ξ, iteratedFDeriv ℝ j (κ i ξ) z) ∧
    ∀ j (Q : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ i z, z ∈ U →
      ‖iteratedFDeriv ℝ j (fun y ↦ ∫ ξ, κ i ξ y) z‖ ≤ D * A i * lam i ^ (-Q) := by
  have hmajor (i : I) := exists_annular_jet_majorants dLoss s ell b C
    hν hνlt (hlam i) (hL i) (hLK i) (hK i) (fun j N ξ z hz ↦ hb j N i ξ z hz)
  choose B hi hbound using hmajor
  have he (i : I) (j : ℕ) (z : X) (hz : z ∈ U) :=
    iteratedFDeriv_annularIntegral_of_jet_majorants hU (hκ i) (hm i)
      (B i) (hi i) (hbound i) j hz
  refine ⟨fun i ↦ contDiffOn_annularIntegral_of_jet_majorants hU (hκ i) (hm i)
    (B i) (hi i) (hbound i), ?_, ?_⟩
  · intro i j z hz
    exact ⟨(hi i j).mono' (hm i j z hz)
      (ae_of_all _ (fun ξ ↦ hbound i j ξ z hz)), he i j z hz⟩
  · intro j Q
    obtain ⟨N, D, hD, hprec⟩ := exists_annular_integral_precision
      (F := X [×j]→L[ℝ] F) (n := n) (s j) (ell j) (b j) (dLoss j) Q
      hν hνlt (C j) (hC j)
    refine ⟨D, hD, fun i z hz ↦ ?_⟩
    rw [he i j z hz]
    exact (hprec (lam i) (L i) (K i) (A i) (hlam i) (hL i) (hLK i) (hK i) (hA i)
      (fun ξ ↦ iteratedFDeriv ℝ j (κ i ξ) z) (hm i j z hz)
      (fun ξ ↦ hb j N i ξ z hz)).2

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
