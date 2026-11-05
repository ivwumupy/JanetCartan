module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Accuracy
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Chains

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Finite chains with literal proof localizers

The analytic induction in `app:ch_regular:lem:finite-chain`. Each stage retains
its own space, scale, full factor and two adjacent proof masks. The masks need
not be projections. The single-factor leakage bounds, low operator bounds,
and full downstream Sobolev costs imply the chain estimate. In particular the
source tail is propagated through the original full factors, and no source
estimate is imposed again on the residual outputs.

Actual masks and individual estimates are produced by `FiniteChain.Graph`,
`FiniteChain.Retarded`, and `EvolutionIntegratedLocalization`. Matching them to
the complete residual and the initialized protected family remains a separate
construction; this module does not assume or assert that construction.
-/

@[expose] public noncomputable section

namespace JanetCartan.ArbitraryAccuracy

open Finset ResponseTransfer

variable {ι : Type*} {E : ℕ → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]

/-- Moving each proof mask to the preceding output keeps exactly the same
near chain. No idempotence or projection property is used
(`app:ch_regular:lem:finite-chain`). -/
theorem factorChain_output_localizers
    (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : ∀ j, ι → E j →ₗ[ℝ] E j) (f : ι → E 0) (n : ℕ) (i : ι) :
    factorChain (fun j i ↦ (M (j + 1) i).comp (T j i))
        (fun i ↦ M 0 i (f i)) n i =
      M n i (factorChain (fun j i ↦ (T j i).comp (M j i)) f n i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [factorChain, LinearMap.comp_apply]
    rw [ih]

/-- Only the L² norm of the original source is needed for the near prefixes.
All constants are chosen before the family index; finite depth may enlarge
the polynomial cost (`app:ch_regular:lem:finite-chain`). -/
theorem factorChain_polynomial_norm
    (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i)
    (hf : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖f i‖ ≤ D * A i * (ρ i) ^ a)
    (hT : ∀ j < d, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i v‖ ≤ D * (ρ i) ^ c * ‖v‖) :
    ∀ n ≤ d, ∃ D a : ℝ, 0 ≤ D ∧ ∀ i,
      ‖factorChain T f n i‖ ≤ D * A i * (ρ i) ^ a := by
  intro n hn
  induction n with
  | zero => exact hf
  | succ n ih =>
    obtain ⟨D, a, hD, hu⟩ := ih (by omega)
    obtain ⟨C, c, hC, hT⟩ := hT n (by omega)
    refine ⟨C * D, c + a, mul_nonneg hC hD, fun i ↦ ?_⟩
    have hρpos : 0 < ρ i := lt_of_lt_of_le zero_lt_one (hρ i)
    calc
      ‖factorChain T f (n + 1) i‖ ≤ C * (ρ i) ^ c * ‖factorChain T f n i‖ :=
        hT i _
      _ ≤ C * (ρ i) ^ c * (D * A i * (ρ i) ^ a) :=
        mul_le_mul_of_nonneg_left (hu i) (by positivity)
      _ = (C * D) * A i * (ρ i) ^ (c + a) := by
        rw [Real.rpow_add hρpos]
        ring

/-- Apply the chain telescoping theorem to the actual localizer split.
The intermediate complementary estimates are proved from the individual
`L² → Hˢ` bounds and low bounds, rather than assumed on the near prefixes.
The source here is its literal first localized part
(`app:ch_regular:eq:chain-tail`). -/
theorem finiteChain_localized_source_sub_near_rapidDecayAt
    (G : ∀ j, GradedScale (E j))
    (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : ∀ j, ι → E j →ₗ[ℝ] E j)
    (f : ι → E 0) (ρ L A : ι → ℝ) (d : ℕ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 0 ≤ L i) (hσ : 0 < σ)
    (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - σ)) (hA : ∀ i, 0 ≤ A i)
    (hf : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖f i‖ ≤ D * A i * (ρ i) ^ a)
    (hlow : ∀ j < d, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i (M j i v)‖ ≤ D * (ρ i) ^ c * ‖v‖)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hleak : ∀ j < d, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        ((1 - M (j + 1) i) (T j i (M j i v))) ∈ (G (j + 1)).level s ∧
        (G (j + 1)).gradeNorm s ((1 - M (j + 1) i) (T j i (M j i v))) ≤
          C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖v‖) :
    ∀ s, RapidDecayAt (G d) s ρ A (fun i ↦
      factorChain T (fun i ↦ M 0 i (f i)) d i -
        M d i (factorChain (fun j i ↦ (T j i).comp (M j i)) f d i)) := by
  let N j i := (M (j + 1) i).comp (T j i)
  let C j i := (1 - M (j + 1) i).comp (T j i)
  let P j i := (T j i).comp (M j i)
  have hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i := by
    intro j _ i
    ext v
    simp only [N, C, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, Module.End.one_apply]
    abel
  have hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N (fun i ↦ M 0 i (f i)) j i)) := by
    intro j hj s
    obtain ⟨c, b, hbound⟩ := hleak j hj s
    have hu := factorChain_polynomial_norm P f ρ A d hρ hf hlow j hj.le
    have hdec := rapidDecayAt_localized_factor (G (j + 1)) s ρ L A
      (fun i ↦ (C j i).comp (M j i)) (factorChain P f j) σ c b
      hρ hL hσ hscale hA hu hbound
    simpa only [N, factorChain_output_localizers, P, LinearMap.comp_apply] using hdec
  intro s
  simpa only [N, factorChain_output_localizers] using
    factorChain_sub_near_rapidDecayAt G T N C (fun i ↦ M 0 i (f i)) ρ A d
      hρ hA hsplit hcost hcomp s

/-- Localize a complete finite chain, including its original source tail.
The only rapid-decay input is that original tail. All subsequent leakage is
derived from individual factor bounds; all remaining full factors pay their
Sobolev costs. Proof masks and actual operators are fixed before accuracy
(`app:ch_regular:lem:finite-chain`). -/
theorem finiteChain_sub_localized_rapidDecayAt
    (G : ∀ j, GradedScale (E j))
    (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : ∀ j, ι → E j →ₗ[ℝ] E j)
    (f : ι → E 0) (ρ L A : ι → ℝ) (d : ℕ) (σ : ℝ)
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
          C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖v‖) :
    ∀ s, RapidDecayAt (G d) s ρ A (fun i ↦ factorChain T f d i -
      M d i (factorChain (fun j i ↦ (T j i).comp (M j i)) f d i)) := by
  have hs := factorChain_rapidDecayAt G T (fun i ↦ f i - M 0 i (f i)) ρ A d
    hρ hA hsource hcost d le_rfl
  have hl := finiteChain_localized_source_sub_near_rapidDecayAt G T M f ρ L A d σ
    hρ hL hσ hscale hA hf hlow hcost hleak
  have hsub : ∀ n i, factorChain T (fun i ↦ f i - M 0 i (f i)) n i =
      factorChain T f n i - factorChain T (fun i ↦ M 0 i (f i)) n i := by
    intro n i
    induction n with
    | zero => rfl
    | succ n ih => simp only [factorChain, ih, map_sub]
  intro s
  let v : Bool → ι → E d := fun b i ↦ if b then
    factorChain T (fun i ↦ f i - M 0 i (f i)) d i else
    factorChain T (fun i ↦ M 0 i (f i)) d i -
      M d i (factorChain (fun j i ↦ (T j i).comp (M j i)) f d i)
  have hv : ∀ b ∈ (univ : Finset Bool), RapidDecayAt (G d) s ρ A (v b) := by
    intro b _
    cases b
    · exact hl s
    · exact hs s
  have heq : (fun i ↦ ∑ b ∈ (univ : Finset Bool), v b i) =
      fun i ↦ factorChain T f d i -
        M d i (factorChain (fun j i ↦ (T j i).comp (M j i)) f d i) := by
    funext i
    simp only [Fintype.sum_bool, v, Bool.false_eq_true, ↓reduceIte, hsub]
    abel
  rw [← heq]
  exact rapidDecayAt_chain_sum univ s hv

end JanetCartan.ArbitraryAccuracy
