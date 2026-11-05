module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Localizers

/-!
# Observing the full finite chain

The final physical observation in `app:ch_regular:lem:finite-chain` has a
polynomial Sobolev cost on discarded output and arbitrary accuracy on the
last localized part. The latter is an individual factor estimate, including
its low-frequency discrepancy, not an exact annihilation assumption. This
module combines these inputs without replacing any actual factor or cutoff.
-/

@[expose] public noncomputable section

namespace JanetCartan.ArbitraryAccuracy

open Finset ResponseTransfer

variable {ι : Type*} {E : ℕ → Type*} {F : Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The final observation of the complete chain is rapidly decaying. All
intermediate leakage and the propagated source tail are deduced internally.
The last factor's estimate retains the full `AΓ-I`, so its identity and
bounded-frequency discrepancy cannot be dropped
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem finiteChain_observation_rapidDecayAt
    (G : ∀ j, GradedScale (E j)) (H : GradedScale F) (d : ℕ)
    (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : ∀ j, ι → E j →ₗ[ℝ] E j) (B : ι → E d →ₗ[ℝ] F)
    (f : ι → E 0) (ρ L A : ι → ℝ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 0 ≤ L i) (hσ : 0 < σ)
    (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - σ)) (hA : ∀ i, 0 ≤ A i)
    (hf : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖f i‖ ≤ D * A i * (ρ i) ^ a)
    (hsource : ∀ s, RapidDecayAt (G 0) s ρ A (fun i ↦ f i - M 0 i (f i)))
    (hlow : ∀ j < d, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i (M j i v)‖ ≤ D * (ρ i) ^ c * ‖v‖)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hleak : ∀ j < d, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        ((1 - M (j + 1) i) (T j i (M j i v))) ∈ (G (j + 1)).level s ∧
        (G (j + 1)).gradeNorm s ((1 - M (j + 1) i) (T j i (M j i v))) ≤
          C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖v‖)
    (hBcost : HasPolynomialSobolevCost (G d) H ρ B)
    (hBnear : ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        B i (M d i v) ∈ H.level s ∧
        H.gradeNorm s (B i (M d i v)) ≤
          C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖v‖) :
    ∀ s, RapidDecayAt H s ρ A (fun i ↦ B i (factorChain T f d i)) := by
  let P j i := (T j i).comp (M j i)
  have hu := factorChain_polynomial_norm P f ρ A d hρ hf hlow d le_rfl
  have herr := rapidDecayAt_polynomial_factor hρ hA hBcost
    (finiteChain_sub_localized_rapidDecayAt G T M f ρ L A d σ
      hρ hL hσ hscale hA hf hsource hlow hcost hleak)
  intro s
  obtain ⟨c, b, hbound⟩ := hBnear s
  have hnear := rapidDecayAt_localized_factor H s ρ L A
    (fun i ↦ (B i).comp (M d i)) (factorChain P f d) σ c b
    hρ hL hσ hscale hA hu hbound
  let v : Bool → ι → F := fun b i ↦ if b then
    B i (M d i (factorChain P f d i)) else
    B i (factorChain T f d i - M d i (factorChain P f d i))
  have hv : ∀ b ∈ (univ : Finset Bool), RapidDecayAt H s ρ A (v b) := by
    intro b _
    cases b
    · exact herr s
    · exact hnear
  simpa [v, map_sub, add_comm] using rapidDecayAt_chain_sum univ s hv

end JanetCartan.ArbitraryAccuracy
