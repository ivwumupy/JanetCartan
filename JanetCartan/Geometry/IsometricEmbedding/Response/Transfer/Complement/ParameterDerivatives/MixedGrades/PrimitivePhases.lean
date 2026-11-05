module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.GraphBounds

/-!
# Both original carrier phases on compact parameter boxes

The primitive phase inputs to the mixed-grade theorem are available for both
actual carrier signs from the original joint phase and carrier smoothness.
Compactness supplies uniform finite profiles on the entire physical supports.
Source: `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- Joint smoothness of the literal forward carrier phase from the original
phase and carrier. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_forwardCarrierPhase_joint
    {ζ : P → E} {φ : P → E → ℝ} {C : Set P}
    (hζ : ContDiffOn ℝ ∞ ζ C)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ forwardCarrierPhase ζ φ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ) := by
  exact (contDiffOn_snd.snd.inner ℝ (hζ.comp contDiffOn_fst (fun _ hp ↦ hp.1))).sub
    (hφ.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩))

/-- Joint smoothness of the literal reverse carrier phase, with its positions
in the actual reverse order. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_reverseCarrierPhase_joint
    {ζ : P → E} {φ : P → E → ℝ} {C : Set P}
    (hζ : ContDiffOn ℝ ∞ ζ C)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ reverseCarrierPhase ζ φ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ) := by
  exact (hφ.comp (contDiffOn_fst.prodMk contDiffOn_snd.snd)
    (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩)).sub
    (contDiffOn_snd.fst.inner ℝ (hζ.comp contDiffOn_fst (fun _ hp ↦ hp.1)))

/-- Compactness supplies a single nonnegative primitive profile for both
carrier signs, uniformly on the fixed parameter box and the full physical
support. The constants precede every frequency and scale. At each prescribed
mixed order only finitely many entries are consumed by the full-jet budget.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem exists_forward_reverse_carrierPhase_profile
    {ζ : P → E} {φ : P → E → ℝ} {C K : Set P} {B : Set (E × E)}
    (hC : IsOpen C) (hK : IsCompact K) (hKC : K ⊆ C) (hB : IsCompact B)
    (hζ : ContDiffOn ℝ ∞ ζ C)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ Set.univ)) :
    ∃ H : ℕ → ℝ, (∀ j, 0 ≤ H j) ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ j c, c ∈ K → ∀ w ∈ B,
      ‖iteratedFDeriv ℝ j (fun p : P × (E × E) ↦
        forwardCarrierPhase ζ φ p.1 p.2.1 p.2.2) (c, w)‖ ≤ H j * L ^ j ∧
      ‖iteratedFDeriv ℝ j (fun p : P × (E × E) ↦
        reverseCarrierPhase ζ φ p.1 p.2.1 p.2.2) (c, w)‖ ≤ H j * L ^ j := by
  have hsub : K ×ˢ B ⊆ C ×ˢ Set.univ := fun _ hp ↦ ⟨hKC hp.1, Set.mem_univ _⟩
  obtain ⟨Hf, hHf, hf⟩ := exists_carrierJet_profile_on_compact
    (hC.prod isOpen_univ) (hK.prod hB) hsub (contDiffOn_forwardCarrierPhase_joint hζ hφ)
  obtain ⟨Hr, hHr, hr⟩ := exists_carrierJet_profile_on_compact
    (hC.prod isOpen_univ) (hK.prod hB) hsub (contDiffOn_reverseCarrierPhase_joint hζ hφ)
  refine ⟨fun j ↦ Hf j + Hr j, fun j ↦ add_nonneg (hHf j) (hHr j), ?_⟩
  intro L hL j c hc w hw
  have hpow : 1 ≤ L ^ j := one_le_pow₀ hL
  have hf' := (hf j (c, w) ⟨hc, hw⟩).trans
    (le_add_of_nonneg_right (hHr j))
  have hr' := (hr j (c, w) ⟨hc, hw⟩).trans
    (le_add_of_nonneg_left (hHf j))
  exact ⟨hf'.trans (le_mul_of_one_le_right (add_nonneg (hHf j) (hHr j)) hpow),
    hr'.trans (le_mul_of_one_le_right (add_nonneg (hHf j) (hHr j)) hpow)⟩

/-- Both actual carrier signs satisfy GraphDecay's mixed-amplitude input on
the fixed compact parameter box. All scalar analytic inputs are constructed
from the original `φ`, `ζ`, and compact smooth selector. Only grades for the
original full matrix amplitude remain as quantitative hypotheses. These are
the original-symbol inputs supplied by the finite FIO calculus, including the
literal reverse weight. The same `G` works in both directions; the fixed
frequency factor reconstructed by
`frequency_smul_normalizedComplementaryCarrierJet` is `ρ^(2*k)`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem exists_forward_reverse_complementary_mixed_profile {r : ℕ}
    {q : E → ℂ} {ζ : P → E} {φ : P → E → ℝ} {C K : Set P} {B : Set (E × E)}
    (hC : IsOpen C) (hK : IsCompact K) (hKC : K ⊆ C) (hB : IsCompact B)
    (hζ : ContDiffOn ℝ ∞ ζ C)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (C ×ˢ Set.univ))
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    {g : ℝ} (hg : 0 < g) (hqone : ∀ δ, ‖δ‖ < g → q δ = 1)
    (R : ℕ → ℝ) (hR : ∀ i, 0 ≤ R i) (b k : ℕ) (v : Fin k → P) :
    ∃ G : ℕ → ℕ → ℝ, (∀ t j, 0 ≤ G t j) ∧
      ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L → L ≤ ρ →
      ∀ (A : FourierIntegral.FullAmplitude n r),
      ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) →
      (∀ x y η, (x, y) ∉ B → A x y η = 0) →
      (∀ i η w, w ∈ B →
        ‖iteratedFDeriv ℝ i (fun z : E × E ↦ A z.1 z.2 η) w‖ ≤ R i * L ^ (b + i)) →
      ∀ c, c ∈ K → ∀ (reverse : Bool) η (β : List (Fin n)) j x y,
      ‖iteratedFDeriv ℝ j (fun w ↦ NormalComparison.normalMatrixDerivList β (fun z ↦
        complementaryAmplitude (normalizedComplementaryCarrierJet A q ζ
          (if reverse then reverseCarrierPhase ζ φ else forwardCarrierPhase ζ φ) ρ k v c)
          (ζ c) ρ (fun δ ↦ auxiliaryComplementSelector n g hg (ρ⁻¹ • δ)) z w η) x) y‖ ≤
        G β.length j * L ^ (b + β.length + j) := by
  obtain ⟨H, hH, hphase⟩ := exists_forward_reverse_carrierPhase_profile hC hK hKC hB hζ hφ
  obtain ⟨G, hG, hgrade⟩ := exists_complementaryCarrierJet_graph_mixed_profile (r := r)
    hC hK hKC hζ hq hqc hg hqone H R hH hR b k v
  refine ⟨G, hG, ?_⟩
  intro ρ L hρ hL hLρ A hA hAsupport hAjet c hc reverse η β j x y
  have hs : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦
      (if reverse then reverseCarrierPhase ζ φ else forwardCarrierPhase ζ φ) p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ) := by
    cases reverse with
    | false => exact contDiffOn_forwardCarrierPhase_joint hζ hφ
    | true => exact contDiffOn_reverseCarrierPhase_joint hζ hφ
  apply hgrade ρ L hρ hL hLρ A _ B hB.isClosed hA hs hAsupport ?_ hAjet c hc η β j x y
  intro i d hd w hw
  cases reverse with
  | false => exact (hphase L hL i d hd w hw).1
  | true => exact (hphase L hL i d hd w hw).2

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
