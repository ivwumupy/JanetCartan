module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.GraphDecay

/-!
# Primitive grades for the same complementary graph branches

The consumers are `forward_normalizedCarrierJet_rapidDecay` and
`reverse_normalizedCarrierJet_rapidDecay`, in the parameter paragraph of
`app:ch_response:thm:response-literal-transfer`. All grades below are proved
from the original amplitude and joint carrier phase. The normalization costs
exactly `ρ^(2*k)` independently of the number of integrations by parts.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral NormalComparison Pseudodifferential ArbitraryAccuracy MixedGrades
variable {n r : ℕ} {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- Fixing an interior parameter in the proved joint jet construction gives
the global smooth amplitude required by GraphDecay. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiff_normalizedComplementaryCarrierJet
    {A : FullAmplitude n r} {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ}
    {U : Set P} (hU : IsOpen U) (hζ : ContDiffOn ℝ ∞ ζ U) (hq : ContDiff ℝ ∞ q)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2)
      (U ×ˢ Set.univ))
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ U) :
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v c p.1.1 p.1.2 p.2) := by
  exact contDiffOn_univ.mp
    ((contDiffOn_normalizedComplementaryCarrierJet hU hζ hq hψ hA hρ k v).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ ↦ ⟨hc, Set.mem_univ _⟩))

/-- A common mixed graph profile on the compact parameter box, obtained from
the ORIGINAL full amplitude and joint phase grades. In particular no bound
on a differentiated amplitude is an input. All physical and frequency cutoffs
are still contained in `A`. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem exists_normalizedComplementaryCarrierJet_graph_grades
    {q : E → ℂ} {ζ : P → E} {U B : Set P}
    (hU : IsOpen U) (hB : IsCompact B) (hBU : B ⊆ U)
    (hζ : ContDiffOn ℝ ∞ ζ U) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    {g : ℝ} (hg : 0 < g) (hqone : ∀ δ, ‖δ‖ < g → q δ = 1)
    (H R : ℕ → ℝ) (hH : ∀ j, 0 ≤ H j) (hR : ∀ j, 0 ≤ R j)
    (b k : ℕ) (v : Fin k → P)
    (A : ι → ℕ → FullAmplitude n r) (ψ : ι → P → E → E → ℝ)
    (ρ L : ι → ℝ) (c : ι → P) (hc : ∀ i, c i ∈ B)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    {W : Set (E × E)} (hW : IsClosed W)
    (hA : ∀ i a, ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A i a p.1.1 p.1.2 p.2))
    (hψ : ∀ i, ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ i p.1 p.2.1 p.2.2)
      (U ×ˢ Set.univ))
    (hs : ∀ i a x y η, (x, y) ∉ W → A i a x y η = 0)
    (hψj : ∀ i j c, c ∈ B → ∀ w ∈ W, ‖iteratedFDeriv ℝ j
      (fun p : P × (E × E) ↦ ψ i p.1 p.2.1 p.2.2) (c, w)‖ ≤ H j * L i ^ j)
    (hAj : ∀ i a j η w, w ∈ W →
      ‖iteratedFDeriv ℝ j (fun z : E × E ↦ A i a z.1 z.2 η) w‖ ≤ R j * L i ^ (b + j)) :
    ∃ G : ℕ → ℕ → ℝ, (∀ t j, 0 ≤ G t j) ∧
      ∀ i a η (β : List (Fin n)) j x y,
      ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β (fun z ↦
        normalizedComplementaryCarrierJet (A i a) q ζ (ψ i) (ρ i) k v (c i) z w η) x) y‖ ≤
        G β.length j * L i ^ (b + β.length + j) := by
  obtain ⟨G, hG, hb⟩ := exists_complementaryCarrierJet_graph_mixed_profile
    hU hB hBU hζ hq hqc hg hqone H R hH hR b k v
  refine ⟨G, hG, fun i a η β j x y ↦ ?_⟩
  have h := hb (ρ i) (L i) (hρ i) (hL i) (hLρ i) (A i a) (ψ i) W hW
    (hA i a) (hψ i) (hs i a) (hψj i) (hAj i a) (c i) (hc i) η β j x y
  rwa [complementaryAmplitude_auxiliarySelector_normalizedJet (A i a) q ζ (ψ i)
    (ρ i) hg hqone (hζ.contDiffAt (hU.mem_nhds (hBU (hc i)))).continuousAt k v] at h

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
