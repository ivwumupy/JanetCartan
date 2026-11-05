module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Observation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Algebra

/-!
# Alternating residual factors and changes of quantization

Insert an identity after each actual factor. Even stages carry the original
right input localizers; odd stages carry the left output localizers. The two
primitive leakage estimates therefore match the existing finite-chain theorem,
while the unlocalized product is exactly the original ordered product.
-/

@[expose] public noncomputable section
namespace JanetCartan.ArbitraryAccuracy
open ResponseTransfer
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Insert an identity after each original factor, preserving its order.
Consumer: the left/right quantization join in `app:ch_regular:lem:finite-chain`. -/
def alternatingChainFactor (T : ℕ → ι → E →ₗ[ℝ] E) (j : ℕ) (i : ι) : E →ₗ[ℝ] E :=
  if j % 2 = 0 then T (j / 2) i else LinearMap.id

/-- Right input and left output localizers occupy different stages; they
are not identified (`app:ch_regular:eq:chain-tail`). -/
def alternatingChainLocalizer (R L : ℕ → ι → E →ₗ[ℝ] E) (j : ℕ) (i : ι) : E →ₗ[ℝ] E :=
  if j % 2 = 0 then R (j / 2) i else L (j / 2) i

/-- The inserted identities leave the complete original chain unchanged
(`app:ch_regular:lem:finite-chain`). -/
theorem factorChain_alternatingChainFactor
    (T : ℕ → ι → E →ₗ[ℝ] E) (f : ι → E) (n : ℕ) (i : ι) :
    factorChain (alternatingChainFactor T) f (2*n) i = factorChain T f n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [factorChain, alternatingChainFactor,
      show (2*n+1)%2 ≠ 0 by omega, ite_false, LinearMap.id_apply,
      show (2*n)%2 = 0 by omega, ite_true, show (2*n)/2 = n by omega]
    exact congrArg (T n i) ih

/-- Assemble the two proved primitive leakage estimates into the exact
`finiteChain_observation_rapidDecayAt.hleak` signature. The factor estimate is
produced by the supported characteristic/elliptic construction; the identity
estimate is produced by selected cross quantization. Losses precede accuracy
and the varying family index (`app:ch_regular:eq:chain-tail`). -/
theorem alternatingChain_leakage_bounds
    (G : GradedScale E) (T R L : ℕ → ι → E →ₗ[ℝ] E)
    (ρ slowScale : ι → ℝ) (n : ℕ)
    (hfactor : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1 - L j i) (T j i (R j i v)) ∈ G.level s ∧
        G.gradeNorm s ((1 - L j i) (T j i (R j i v))) ≤
          C * (ρ i)^c * slowScale i^b * (slowScale i/ρ i)^q * ‖v‖)
    (hcross : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1 - R (j+1) i) (L j i v) ∈ G.level s ∧
        G.gradeNorm s ((1 - R (j+1) i) (L j i v)) ≤
          C * (ρ i)^c * slowScale i^b * (slowScale i/ρ i)^q * ‖v‖) :
    ∀ j < 2*n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1 - alternatingChainLocalizer R L (j+1) i)
          (alternatingChainFactor T j i (alternatingChainLocalizer R L j i v)) ∈ G.level s ∧
        G.gradeNorm s ((1 - alternatingChainLocalizer R L (j+1) i)
          (alternatingChainFactor T j i (alternatingChainLocalizer R L j i v))) ≤
          C * (ρ i)^c * slowScale i^b * (slowScale i/ρ i)^q * ‖v‖ := by
  intro j hj s
  have hdiv : j/2 < n := by omega
  by_cases he : j%2 = 0
  · simpa only [alternatingChainLocalizer, alternatingChainFactor, he, ite_true,
      show (j+1)%2 ≠ 0 by omega, ite_false, show (j+1)/2 = j/2 by omega]
      using hfactor (j/2) hdiv s
  · simpa only [alternatingChainLocalizer, alternatingChainFactor, he, ite_false,
      show (j+1)%2 = 0 by omega, ite_true, show (j+1)/2 = j/2+1 by omega,
      LinearMap.id_apply] using hcross (j/2) hdiv s

/-- Apply the existing observation theorem with the literal change of
quantization between factors. Only individual factor and cross-quantization
bounds enter; the complete chain estimate is deduced. Actual source, low/cost
and terminal inputs retain their original producers and scale contract
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem finiteChain_observation_rapidDecayAt_of_cross_quantizations
    (G : GradedScale E) (H : GradedScale F) (n : ℕ)
    (T R L : ℕ → ι → E →ₗ[ℝ] E) (B : ι → E →ₗ[ℝ] F)
    (f : ι → E) (ρ slowScale A : ι → ℝ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 0 ≤ slowScale i) (hσ : 0 < σ)
    (hscale : ∀ i, slowScale i ≤ (ρ i)^(1-σ)) (hA : ∀ i, 0 ≤ A i)
    (hf : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖f i‖ ≤ D*A i*(ρ i)^a)
    (hsource : ∀ s, RapidDecayAt G s ρ A (fun i ↦ f i - R 0 i (f i)))
    (hlow : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i (R j i v)‖ ≤ D*(ρ i)^c*‖v‖)
    (hleft : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖L j i v‖ ≤ D*(ρ i)^c*‖v‖)
    (hcost : ∀ j < n, HasPolynomialSobolevCost G G ρ (T j))
    (hfactor : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-L j i) (T j i (R j i v)) ∈ G.level s ∧
        G.gradeNorm s ((1-L j i) (T j i (R j i v))) ≤
          C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖)
    (hcross : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-R (j+1) i) (L j i v) ∈ G.level s ∧
        G.gradeNorm s ((1-R (j+1) i) (L j i v)) ≤
          C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖)
    (hBcost : HasPolynomialSobolevCost G H ρ B)
    (hBnear : ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        B i (R n i v) ∈ H.level s ∧ H.gradeNorm s (B i (R n i v)) ≤
          C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖) :
    ∀ s, RapidDecayAt H s ρ A (fun i ↦ B i (factorChain T f n i)) := by
  have halow : ∀ j < 2*n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖alternatingChainFactor T j i (alternatingChainLocalizer R L j i v)‖ ≤
        D*(ρ i)^c*‖v‖ := by
    intro j hj
    by_cases he : j%2 = 0
    · simpa only [alternatingChainFactor, alternatingChainLocalizer, he, ite_true]
        using hlow (j/2) (by omega)
    · simpa only [alternatingChainFactor, alternatingChainLocalizer, he, ite_false,
        LinearMap.id_apply] using hleft (j/2) (by omega)
  have hacost : ∀ j < 2*n, HasPolynomialSobolevCost G G ρ (alternatingChainFactor T j) := by
    intro j hj
    by_cases he : j%2 = 0
    · have heq : alternatingChainFactor T j = T (j/2) := funext fun _ ↦ ite_eq_left he
      rw [heq]
      exact hcost (j/2) (by omega)
    · have heq : alternatingChainFactor T j = fun _ ↦ LinearMap.id := funext fun _ ↦ ite_eq_right he
      rw [heq]
      exact ResidualLocalization.polynomialCost_identity G ρ
  have h := finiteChain_observation_rapidDecayAt (fun _ ↦ G) H (2*n)
    (alternatingChainFactor T) (alternatingChainLocalizer R L) B f ρ slowScale A σ
    hρ hL hσ hscale hA hf (by simpa [alternatingChainLocalizer] using hsource)
    halow hacost (alternatingChain_leakage_bounds G T R L ρ slowScale n hfactor hcross)
    hBcost (by simpa [alternatingChainLocalizer] using hBnear)
  simpa only [factorChain_alternatingChainFactor] using h

end JanetCartan.ArbitraryAccuracy
