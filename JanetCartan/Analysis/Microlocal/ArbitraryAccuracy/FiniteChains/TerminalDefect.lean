module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Localizers

/-!
# The prescribed terminal mask on the actual full chain

The supported terminal source estimate is applied to the actual measured word.
The near chain need not retain physical support. The identity below moves the
terminal mask to the full word, paying the proved chain and terminal leakage
errors (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
namespace JanetCartan.ArbitraryAccuracy
open ResponseTransfer
variable {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem terminalDecay_add (G : GradedScale X) (s : ℕ)
    {ρ A : ι → ℝ} {u v : ι → X}
    (hu : RapidDecayAt G s ρ A u) (hv : RapidDecayAt G s ρ A v) :
    RapidDecayAt G s ρ A (fun i ↦ u i + v i) := by
  intro Q
  obtain ⟨C, hC, hc⟩ := hu Q
  obtain ⟨D, hD, hd⟩ := hv Q
  refine ⟨C+D, add_nonneg hC hD, fun i ↦
    ⟨(G.level s).add_mem (hc i).1 (hd i).1, (gradeNorm_add_le G (hc i).1 (hd i).1).trans ?_⟩⟩
  exact (add_le_add (hc i).2 (hd i).2).trans_eq (by ring)

private theorem terminalDecay_sub (G : GradedScale X) (s : ℕ)
    {ρ A : ι → ℝ} {u v : ι → X}
    (hu : RapidDecayAt G s ρ A u) (hv : RapidDecayAt G s ρ A v) :
    RapidDecayAt G s ρ A (fun i ↦ u i - v i) := by
  intro Q
  obtain ⟨C, hC, hc⟩ := hu Q
  obtain ⟨D, hD, hd⟩ := hv Q
  refine ⟨C+D, add_nonneg hC hD, fun i ↦
    ⟨(G.level s).sub_mem (hc i).1 (hd i).1, (G.gradeNorm_sub_le (hc i).1 (hd i).1).trans ?_⟩⟩
  exact (add_le_add (hc i).2 (hd i).2).trans_eq (by ring)

variable {E : ℕ → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]

/-- Move the prescribed terminal RIGHT localizer onto the actual full word.
The final near chain is used only in the individual terminal leakage estimate;
no physical-support assertion about it is required. Consumer: the normalized
supported terminal source estimate (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem finiteChain_terminal_defect_rapidDecayAt
    (G : ∀ j, GradedScale (E j)) (n : ℕ)
    (T : ∀ j, ι → E j →ₗ[ℝ] E (j+1))
    (M : ∀ j, ι → E j →ₗ[ℝ] E j) (Mt : ι → E n →ₗ[ℝ] E n)
    (f : ι → E 0) (ρ L A : ι → ℝ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 0 ≤ L i) (hσ : 0 < σ)
    (hscale : ∀ i, L i ≤ (ρ i)^(1-σ)) (hA : ∀ i, 0 ≤ A i)
    (hf : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖f i‖ ≤ D*A i*(ρ i)^a)
    (hsource : ∀ s, RapidDecayAt (G 0) s ρ A (fun i ↦ f i-M 0 i (f i)))
    (hlow : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i (M j i v)‖ ≤ D*(ρ i)^c*‖v‖)
    (hcost : ∀ j < n, HasPolynomialSobolevCost (G j) (G (j+1)) ρ (T j))
    (hleak : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-M (j+1) i) (T j i (M j i v)) ∈ (G (j+1)).level s ∧
        (G (j+1)).gradeNorm s ((1-M (j+1) i) (T j i (M j i v))) ≤
          C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖)
    (htcost : HasPolynomialSobolevCost (G n) (G n) ρ Mt)
    (htleak : ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-Mt i) (M n i v) ∈ (G n).level s ∧
        (G n).gradeNorm s ((1-Mt i) (M n i v)) ≤
          C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖) :
    ∀ s, RapidDecayAt (G n) s ρ A
      (fun i ↦ factorChain T f n i-Mt i (factorChain T f n i)) := by
  let P j i := (T j i).comp (M j i)
  let near := factorChain P f n
  let err i := factorChain T f n i-M n i (near i)
  have he : ∀ s, RapidDecayAt (G n) s ρ A err :=
    finiteChain_sub_localized_rapidDecayAt G T M f ρ L A n σ
      hρ hL hσ hscale hA hf hsource hlow hcost hleak
  have hte := rapidDecayAt_polynomial_factor hρ hA htcost he
  have hnear := factorChain_polynomial_norm P f ρ A n hρ hf hlow n le_rfl
  intro s
  obtain ⟨c, b, hb⟩ := htleak s
  have htn := rapidDecayAt_localized_factor (G n) s ρ L A
    (fun i ↦ (1-Mt i).comp (M n i)) near σ c b hρ hL hσ hscale hA hnear hb
  have hsum := terminalDecay_add (G n) s (terminalDecay_sub (G n) s (he s) (hte s)) htn
  convert hsum using 1
  funext i
  simp only [err, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  abel

end JanetCartan.ArbitraryAccuracy
