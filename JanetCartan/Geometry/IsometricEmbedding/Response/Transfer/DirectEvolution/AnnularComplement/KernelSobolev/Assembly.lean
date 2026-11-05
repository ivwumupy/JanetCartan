module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.ParameterIntegration
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.CompactOutput

/-!
# Annular kernel profiles imply actual vector Sobolev precision

The independent frequency-integration implication for
`app:ch_response:lem:energy-carrier-jets` and the complementary part of
`app:ch_response:eq:direct-envelope-profile` / `app:ch_response:eq:fixed-factor-transfer`.

`AnnularComplement.SourceBounds` must supply the hypotheses for the literal
inner source integrals in `elapsedGraph_annularComplement_kernel` and
`adjointElapsedGraph_annularComplement_kernel`, with their physical Fourier
normalization included. Apply the theorem separately to the physical kernels
and to kernels multiplied by the actual output demodulator. Thus no derivative
of the output carrier is omitted. The parameter set here is an open box on
which the displayed profiles hold; the conclusion also holds on any smaller
closed parameter box.

The parent construction retains identification with the same uncut graph
difference and instantiation of every source-kernel hypothesis. This module
proves an implication, not unconditional existence of those literal kernels'
profiles or the manuscript's embedding theorem.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open Complement.ParameterDerivatives.Hilbert Pseudodifferential

variable {n r : ℕ} {P I : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Full-frequency integration, actual external and L² parameter derivatives,
and arbitrary vector Fourier Sobolev precision, from the literal annular
source-kernel profile in `app:ch_response:lem:energy-carrier-jets`.

The losses `dLoss`, `s`, `ell`, `b` are fixed before `N`; `C j N` precedes the
family index and retains separate coefficient/envelope scales `L`, `K`.
Only the original kernel's frequency measurability and output support are
assumed. All jet measurability, integrability, derivative interchange, L²
realization, membership and Sobolev estimates are conclusions. -/
theorem annularKernel_sobolev_realization
    {U : Set P} (hU : IsOpen U) {S : Set E} (hS : IsCompact S) [CompactSpace S]
    (κ : I → E → P × E → F)
    (hκ : ∀ i ξ, ContDiffOn ℝ ∞ (κ i ξ) (U ×ˢ univ))
    (hm : ∀ i z, z ∈ U ×ˢ univ → AEStronglyMeasurable (fun ξ ↦ κ i ξ z) volume)
    (hs : ∀ i ξ c, c ∈ U → ∀ x ∉ S, κ i ξ (c, x) = 0)
    (dLoss : ℕ → ℝ) (s ell b : ℕ → ℕ) (C : ℕ → ℕ → ℝ)
    (hC : ∀ j N, 0 ≤ C j N) {ν : ℝ} (hν : 0 < ν) (hνlt : ν < 1)
    (lam L K A : I → ℝ) (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i)
    (hLK : ∀ i, L i ≤ K i) (hK : ∀ i, K i ≤ lam i ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i)
    (hb : ∀ j N i ξ z, z ∈ U ×ˢ univ → ∀ v : Fin j → P × E,
      (∀ a, ‖v a‖ ≤ 1) → ‖iteratedFDeriv ℝ j (κ i ξ) z v‖ ≤
      C j N * A i * lam i ^ dLoss j * L i ^ ell j * K i ^ b j *
        (lam i + ‖ξ‖) ^ s j * (K i / (lam i + ‖ξ‖)) ^ N) :
    (∀ i z, z ∈ U ×ˢ univ → Integrable (fun ξ ↦ κ i ξ z)) ∧
    (∀ i, ContDiffOn ℝ ∞ (fun z ↦ ∫ ξ, κ i ξ z) (U ×ˢ univ)) ∧
    (∀ i j z, z ∈ U ×ˢ univ →
      Integrable (fun ξ ↦ iteratedFDeriv ℝ j (κ i ξ) z) ∧
      iteratedFDeriv ℝ j (fun y ↦ ∫ ξ, κ i ξ y) z =
        ∫ ξ, iteratedFDeriv ℝ j (κ i ξ) z) ∧
    (∀ i, ContDiffOn ℝ ∞
      (compactVectorL2Family hS (fun c x ↦ ∫ ξ, κ i ξ (c, x))) U) ∧
    (∀ i c, c ∈ U →
      compactVectorL2Family hS (fun a x ↦ ∫ ξ, κ i ξ (a, x)) c =ᵐ[volume]
        fun x ↦ ∫ ξ, κ i ξ (c, x)) ∧
    (∀ i k (v : Fin k → P) c, c ∈ U →
      iteratedFDeriv ℝ k (compactVectorL2Family hS (fun a x ↦ ∫ ξ, κ i ξ (a, x))) c v =ᵐ[volume]
        fun x ↦ ∫ ξ, iteratedFDeriv ℝ k (fun a ↦ κ i ξ (a, x)) c v) ∧
    ∀ (t : ℝ) (k : ℕ) (Q : ℝ), ∃ D : ℝ, 0 ≤ D ∧
      ∀ i c, c ∈ U → ∀ v : Fin k → P, (∀ a, ‖v a‖ ≤ 1) →
      MemVectorFourierSobolev t (iteratedFDeriv ℝ k
        (compactVectorL2Family hS (fun a x ↦ ∫ ξ, κ i ξ (a, x))) c v) ∧
      vectorFourierSobolevNorm t (iteratedFDeriv ℝ k
        (compactVectorL2Family hS (fun a x ↦ ∫ ξ, κ i ξ (a, x))) c v) ≤
        D * A i * lam i ^ (-Q) := by
  have hmj (i : I) (j : ℕ) (z : P × E) (hz : z ∈ U ×ˢ univ) :
      AEStronglyMeasurable (fun ξ ↦ iteratedFDeriv ℝ j (κ i ξ) z) volume :=
    aestronglyMeasurable_annularKernel_jet (hU.prod isOpen_univ) (hm i) (hκ i) j hz
  have hbop (j N : ℕ) (i : I) (ξ : E) (z : P × E) (hz : z ∈ U ×ˢ univ) :
      ‖iteratedFDeriv ℝ j (κ i ξ) z‖ ≤
        C j N * A i * lam i ^ dLoss j * L i ^ ell j * K i ^ b j *
          (lam i + ‖ξ‖) ^ s j * (K i / (lam i + ‖ξ‖)) ^ N := by
    have hlam0 : 0 ≤ lam i := zero_le_one.trans (hlam i)
    have hL₀ : 0 ≤ L i := zero_le_one.trans (hL i)
    have hK₀ : 0 ≤ K i := hL₀.trans (hLK i)
    have hC0 := hC j N
    have hA0 := hA i
    exact annularJet_norm_le_of_unit_directions _ (by positivity) (hb j N i ξ z hz)
  obtain ⟨hg, hjets, hprecision⟩ := exists_annular_integral_jet_precision
    (hU.prod isOpen_univ) hκ hmj dLoss s ell b C hC hν hνlt
    lam L K A hlam hL hLK hK hA hbop
  have hsint (i : I) (c : P) (hc : c ∈ U) (x : E) (hx : x ∉ S) :
      (∫ ξ, κ i ξ (c, x)) = 0 := by
    simp only [hs i _ c hc x hx, integral_zero]
  obtain ⟨hL2, hSob⟩ := exists_annularL2Family_sobolev_precision hU hS
    (fun i z ↦ ∫ ξ, κ i ξ z) hg hsint lam A hlam hA hprecision
  refine ⟨?_, hg, hjets, hL2, ?_, ?_, hSob⟩
  · intro i z hz
    have h0 := (hjets i 0 z hz).1
    simpa only [ContinuousMultilinearMap.apply_apply, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ P × E) F
        (fun a ↦ Fin.elim0 a)).integrable_comp h0
  · intro i c hc
    exact compactVectorL2Family_ae hS (g := fun a x ↦ ∫ ξ, κ i ξ (a, x))
      (hg i) (hsint i) hc
  · intro i k v c hc
    obtain ⟨B, hi, hbound⟩ := exists_annular_jet_majorants dLoss s ell b C
      hν hνlt (hlam i) (hL i) (hLK i) (hK i) (fun j N ξ z hz ↦ hbop j N i ξ z hz)
    apply (iteratedFDeriv_compactVectorL2Family_ae hS
      (g := fun a x ↦ ∫ ξ, κ i ξ (a, x)) hU (hg i) (hsint i) k v hc).trans
    exact ae_of_all _ (fun x ↦ (annularIntegral_parameter_derivative hU
      (hκ i) (hm i) B hi hbound k v hc x).2)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
