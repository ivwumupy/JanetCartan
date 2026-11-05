module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.FullAmplitude

/-!
# The mixed amplitude input for graph decay

This module supplies the actual `hAj` estimate of the complete complement,
after extracting the fixed frequency power `ρ^(2*k)`. Primitive phase bounds
are needed only on the original physical supports. Source:
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

open FourierIntegral NormalComparison

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- The ordered target/source grade for the normalized actual amplitude.
Original supports allow the primitive phase grades to be local to a closed
physical support; all original cutoffs remain in `A`. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_mixed_normalizedComplementaryCarrierJet_le
    {A : FullAmplitude n r} {q : E → ℂ} {ζ : P → E} {ψ : P → E → E → ℝ}
    {C : Set P} (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2)
      (C ×ˢ Set.univ))
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    {B : Set (E × E)} (hB : IsClosed B)
    (hAsupport : ∀ x y η, (x, y) ∉ B → A x y η = 0)
    (H Q Z R : ℕ → ℝ) (hH : ∀ i, 0 ≤ H i) (hR : ∀ i, 0 ≤ R i)
    {L ρ : ℝ} (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (hLρ : L ≤ ρ)
    (b k : ℕ) (v : Fin k → P) (β : List (Fin n)) (j : ℕ)
    {c : P} (hc : c ∈ C) (x y η : E)
    (hψjet : ∀ i ≤ j + β.length + k, ∀ w ∈ B, ‖iteratedFDeriv ℝ i
      (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2) (c, w)‖ ≤ H i * L ^ i)
    (hqjet : ∀ i ≤ j + β.length + k, ∀ δ, ‖iteratedFDeriv ℝ i q δ‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ j + β.length + k →
      ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z i * L ^ i)
    (hAjet : ∀ i ≤ j + β.length, ∀ w ∈ B,
      ‖iteratedFDeriv ℝ i (fun z : E × E ↦ A z.1 z.2 η) w‖ ≤ R i * L ^ (b + i)) :
    ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β
      (fun v' ↦ normalizedComplementaryCarrierJet A q ζ ψ ρ k v c v' w η) x) y‖ ≤
      complementaryFullJetBudget H Q Z R k v (j + β.length) * L ^ (b + β.length + j) := by
  have hρ0 : ρ ≠ 0 := ne_of_gt (zero_lt_one.trans_le hρ)
  have hf := contDiffOn_normalizedComplementaryCarrierJet hC hζ hq hψ hA hρ0 k v
  have hfixed : ContDiff ℝ ∞ (fun w : E × E ↦
      normalizedComplementaryCarrierJet A q ζ ψ ρ k v c w.1 w.2 η) :=
    contDiffOn_univ.mp (hf.comp
      (contDiffOn_const.prodMk (contDiffOn_id.prodMk contDiffOn_const))
      (fun _ _ ↦ ⟨hc, Set.mem_univ _⟩))
  apply (norm_sourceJet_normalMatrixDerivList_le_joint hfixed β j x y).trans
  by_cases hw : (x, y) ∈ B
  · have hjoint : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦
        normalizedComplementaryCarrierJet A q ζ ψ ρ k v p.1 p.2.1 p.2.2 η)
        (C ×ˢ Set.univ) :=
      hf.comp (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
        (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩)
    apply (norm_iteratedFDeriv_fixed_parameter_le hC hjoint hc (x, y) (j + β.length)).trans
    have hb := norm_iteratedFDeriv_normalizedComplementaryCarrierJet_joint_le hC hζ hq hψ
      (fun η ↦ hA.comp (contDiff_id.prodMk contDiff_const)) H Q Z R hH hL hρ hLρ
      b k v (j + β.length) hc x y η
      (fun i hi ↦ hψjet i hi (x, y) hw) hqjet hζjet (fun i hi ↦ hAjet i hi (x, y) hw)
    convert hb using 1
    congr 2
    omega
  · have he : (fun w : E × E ↦
        normalizedComplementaryCarrierJet A q ζ ψ ρ k v c w.1 w.2 η) =ᶠ[𝓝 (x, y)]
        (fun _ ↦ 0) := by
      filter_upwards [hB.isOpen_compl.mem_nhds hw] with w hw'
      exact normalizedComplementaryCarrierJet_eq_zero_of_amplitude_eq_zero
        A q ζ ψ ρ k v c w.1 w.2 η (hAsupport w.1 w.2 η hw')
    rw [(he.iteratedFDeriv ℝ (j + β.length)).eq_of_nhds]
    change ‖iteratedFDeriv ℝ (j + β.length) (0 : (E × E) → Matrix (Fin r) (Fin r) ℂ) (x, y)‖ ≤ _
    rw [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (complementaryFullJetBudget_nonneg hH hR k v _) (by positivity)

/-- Uniform GraphDecay mixed grades for the actual complementary parameter
jet. The constants are chosen before the frequency, original full amplitude,
phase realization, and compact parameter. Carrier and selector profiles are
produced by compactness; the only remaining quantitative inputs are the
primitive joint phase and original full-amplitude grades. The auxiliary selector
is used by exact multiplication, with no division by the original mask.
The frequency normalization extracts `ρ^(2*k)`, independent of `β` and `j`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem exists_complementaryCarrierJet_graph_mixed_profile
    {q : E → ℂ} {ζ : P → E} {C K : Set P}
    (hC : IsOpen C) (hK : IsCompact K) (hKC : K ⊆ C)
    (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    {g : ℝ} (hg : 0 < g) (hqone : ∀ δ, ‖δ‖ < g → q δ = 1)
    (H R : ℕ → ℝ) (hH : ∀ i, 0 ≤ H i) (hR : ∀ i, 0 ≤ R i)
    (b k : ℕ) (v : Fin k → P) :
    ∃ G : ℕ → ℕ → ℝ, (∀ t j, 0 ≤ G t j) ∧
      ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L → L ≤ ρ →
      ∀ (A : FullAmplitude n r) (ψ : P → E → E → ℝ) (B : Set (E × E)),
      IsClosed B →
      ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) →
      ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2) (C ×ˢ Set.univ) →
      (∀ x y η, (x, y) ∉ B → A x y η = 0) →
      (∀ i c, c ∈ K → ∀ w ∈ B, ‖iteratedFDeriv ℝ i
        (fun p : P × (E × E) ↦ ψ p.1 p.2.1 p.2.2) (c, w)‖ ≤ H i * L ^ i) →
      (∀ i η w, w ∈ B →
        ‖iteratedFDeriv ℝ i (fun z : E × E ↦ A z.1 z.2 η) w‖ ≤ R i * L ^ (b + i)) →
      ∀ c, c ∈ K → ∀ η (β : List (Fin n)) j x y,
      ‖iteratedFDeriv ℝ j (fun w ↦ normalMatrixDerivList β (fun z ↦
        complementaryAmplitude (normalizedComplementaryCarrierJet A q ζ ψ ρ k v c)
          (ζ c) ρ (fun δ ↦ auxiliaryComplementSelector n g hg (ρ⁻¹ • δ)) z w η) x) y‖ ≤
        G β.length j * L ^ (b + β.length + j) := by
  obtain ⟨Q, _, hQ⟩ := exists_selectorJet_profile hq hqc
  obtain ⟨Z, hZ0, hZ⟩ := exists_carrierJet_profile_on_compact hC hK hKC hζ
  refine ⟨fun t j ↦ complementaryFullJetBudget H Q Z R k v (j + t),
    fun _ _ ↦ complementaryFullJetBudget_nonneg hH hR k v _, ?_⟩
  intro ρ L hρ hL hLρ A ψ B hB hA hψ hAsupport hψjet hAjet c hc η β j x y
  rw [complementaryAmplitude_auxiliarySelector_normalizedJet A q ζ ψ ρ hg hqone
    ((hζ.contDiffAt (hC.mem_nhds (hKC hc))).continuousAt) k v]
  apply norm_mixed_normalizedComplementaryCarrierJet_le hC hζ hq hψ hA hB hAsupport
    H Q Z R hH hR hL hρ hLρ b k v β j (hKC hc) x y η
  · exact fun i _ w hw ↦ hψjet i c hc w hw
  · exact fun i _ δ ↦ hQ i δ
  · intro i _ _
    exact (hZ i c hc).trans (le_mul_of_one_le_right (hZ0 i) (one_le_pow₀ hL))
  · exact fun i _ w hw ↦ hAjet i η w hw

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
