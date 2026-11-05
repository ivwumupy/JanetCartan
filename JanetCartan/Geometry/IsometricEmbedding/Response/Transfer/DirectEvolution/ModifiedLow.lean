module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.ModifiedLow.SymbolBudget
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds

/-!
# Low bounds for modified graphs with the original elapsed phase

The consumer is `app:ch_response:eq:direct-envelope-profile`, after restoring
its carrier as in `paper-v2.tex`, `new:eq:carrier-ibp`. The full phase is
literally `EvolutionIntegral.elapsedPhase Ψ t`. Only the amplitude is changed;
normalization evaluates the differential expression at `ξ = lam • θ`.

`EvolutionIntegral.Geometry`, `EvolutionIntegral.SymbolBudgets` and the actual
sector supply the original phase/chart/inverse/Jacobian/support inputs, with
exactly the signatures of `FullLowBounds` below. `jc-direct-evolution-coefficient-jets`
supplies primitive expression-field budgets, and
`jc-direct-evolution-compact-transfer` identifies
the actual differentiated amplitudes using `modifiedAmplitude_eq_of_normalized`.
Neither producer is a scheduler prerequisite for this implication. The parent
must instantiate them on the same sector, including every mask and beta/high-pass
transition; this theorem does not construct those geometric or coefficient data.

The full low calculus constructs the literal physical Lebesgue operators with
normalization `(2π)^(-n)`, Frobenius matrix norms, both positions, the literal
Hilbert adjoint, both strong regularized limits and both distributional
realizations. Its uniqueness API identifies the published `fullGraphOperator`.
The fixed low reserve is `3*n+4`; neither the derivative count, parameter order
nor chain depth increases it. Sobolev assembly, tails and elapsed-time
integration remain with the direct-evolution parent.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.ModifiedLow
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds
open FourierIntegral.SourceExpansion NormalComparison FrequencyCutoff AmplitudeBound
open FullAmplitudePrimitiveBudget.Local
open IsometricEmbedding.Response.NearCarrier
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Construct the actual modified elapsed graph from primitive finite jets and
unchanged original-phase geometric inputs. The constant precedes `lam`, `L`,
all varying primitive fields and even the amplitude order `p`. In particular
`p = 0` gives `C * L^k` and `p = -1` gives `C * lam⁻¹ * L^k`, for the SAME
published graph and its literal adjoint. Supports describe the complete
normalized expression on the fixed annular localization; no amplitude bound,
operator bound, high Sobolev estimate or limit is assumed. The regularized
test identities retain the conjugated cutoff on the adjoint. Source:
`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-coefficient`. -/
theorem exists_modifiedElapsedGraph_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    {ι : Type*} (e : AmplitudeExpression (Point (d + 1)) Mat ι)
    (Pj : ι → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j)
    (Rstar k : ℕ) (hRstar : fullLowReserve (d + 1) + 2 < Rstar)
    (hcost : e.derivativeCost ≤ k) {b : ℝ} (hb : 0 ≤ b) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∃ χ : ℕ → E → ℂ,
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ (∀ j, HasCompactSupport (χ j)) ∧
      (∀ j, (0 : E) ∉ tsupport (χ j)) ∧
      (∀ (A : FullAmplitude (d + 1) r), (∀ x y ξ, ξ ∉ F₀ → A x y ξ = 0) →
        ∀ j, frequencyCutFullAmplitude (χ j) A =
          frequencyCutFullAmplitude (complexPhysicalCutoff j) A) ∧
    ∀ (Ψ : TwoTimePhase d) (t : ℝ)
    (_hS : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)))
    {X D : Set E} {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables (d + 1))}
    (_chart : AveragedGradientChart (elapsedPhase Ψ t) X D η J δ)
    (_hopen : IsOpen (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hηinput : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hmapinput : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)) W)
    (_hJinput : ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J q.1 q.2.1 q.2.2) W)
    (_hgapinput : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (_hrightInverse : ∀ q ∈ bufferedNormalDomain X D (elapsedPhase Ψ t),
      normalForwardCoordinates (elapsedPhase Ψ t) (normalInverseCoordinates η q) = q)
    (_hcarrier : ∀ q ∈ W, q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ → q ∈ K)
    (_hclosed : IsClosed (normalForwardCoordinates (elapsedPhase Ψ t) '' K))
    (_hbuffer : normalForwardCoordinates (elapsedPhase Ψ t) '' K ⊆ bufferedNormalDomain X D (elapsedPhase Ψ t))
    (_hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (_hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient (elapsedPhase Ψ t) x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℕ → Set (NormalVariables (d + 1)))
    (_hUopen : ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hVopen : ∀ l, IsOpen (V l))
    (_hη : ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hmap : ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l) (V l))
    (_hJ : ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) (V l))
    (_hgap : ∀ l z, z ∈ V l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) J z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ l z, z ∈ V l → ∀ i ≤ primitiveNormalReserve (d + 1),
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve (d + 1) →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) η)) z‖ ≤ G)
    (_hscale : ∀ l z, z ∈ V l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    (_hX₀ : X₀ ⊆ X) (_hF₀ : F₀ ⊆ D),
    ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam → ∀ (p : ℤ)
    (a : ι → Point (d + 1) → Mat) (_ha : ∀ i, ContDiff ℝ ∞ (a i))
    (_hj : ∀ i j, j ≤ fullLowReserve (d + 1) + k → ∀ q,
      ‖iteratedFDeriv ℝ j (a i) q‖ ≤ Pj i j * L ^ (j + 2 - Rstar))
    (_hs : ∀ q ∈ tsupport (e.evaluate a),
      q.1.1 ∈ X₀ ∧ q.1.2 ∈ Y₀ ∧ lam • q.2 ∈ F₀)
    (_hsfreq : ∀ q ∈ tsupport (e.evaluate a), ‖q.2‖ ≤ b),
    let A := modifiedAmplitude lam p (e.evaluate a)
        ∃ Treg : ℕ → H →L[ℂ] H,
          ‖fullGraphOperator (elapsedPhase Ψ t) A‖ ≤ C * lam ^ p * L ^ k ∧ ‖(fullGraphOperator (elapsedPhase Ψ t) A).adjoint‖ ≤ C * lam ^ p * L ^ k ∧
          (∀ j, ‖Treg j‖ ≤ C * lam ^ p * L ^ k) ∧
          (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
            graphTestOutput (elapsedPhase Ψ t) (frequencyCutFullAmplitude (χ j) A) u) ∧
          (∀ j (u : graphTestSpace (d + 1) r), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
            fun y ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ t)
              (frequencyCutFullAmplitude (fun η ↦ star (χ j η))
                (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (u.val x).ofLp) y)) ∧
          (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (fullGraphOperator (elapsedPhase Ψ t) A u))) ∧
          (∀ u, Tendsto (fun j ↦ (Treg j).adjoint u) atTop
            (𝓝 ((fullGraphOperator (elapsedPhase Ψ t) A).adjoint u))) ∧
          (∀ u, fullGraphOperator (elapsedPhase Ψ t) A (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ t) A u) ∧
          GraphDistributionalRealization (graphOperator (elapsedPhase Ψ t)) χ A (fullGraphOperator (elapsedPhase Ψ t) A) ∧
          GraphDistributionalRealization (reverseGraphOperator (elapsedPhase Ψ t)) (fun j η ↦ star (χ j η))
            (fun x y η ↦ (A x y η).conjTranspose) (fullGraphOperator (elapsedPhase Ψ t) A).adjoint ∧
          (∀ U : H →L[ℂ] H,
            (∀ u, U (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ t) A u) →
            U = fullGraphOperator (elapsedPhase Ψ t) A) := by
  have hconstructor := exists_fullGraphFamily_of_primitive_inputs
    (n := d + 1) (r := r) (Nat.zero_lt_succ d) R ℓ M G c hℓ hRcell hδ hF hc
  obtain ⟨C₀, hC₀, hbuild⟩ := hconstructor
  let N := fullLowReserve (d + 1)
  let B := (1 + b) ^ N * e.lowJetConstant Pj N
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg (by linarith) _)
    (e.lowJetConstant_nonneg Pj hPj N)
  refine ⟨C₀ * B, mul_nonneg hC₀.le hB, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  have hcutoffs := hbuild X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  obtain ⟨χ, hχ, hχcompact, hχzero, hχpreserve, hfamily⟩ := hcutoffs
  refine ⟨χ, hχ, hχcompact, hχzero, hχpreserve, ?_⟩
  intro Ψ t hS X D η J W K chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ L lam hL hlam p a ha hj hs hsfreq
  let A := modifiedAmplitude lam p (e.evaluate a)
  have hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A :=
    admissible_modifiedAmplitude (zero_lt_one.trans_le hlam).ne' p
      (e.contDiff_evaluate a ha) hs
  have hsymbol : HasFullSourceSymbolBound A N (B * lam ^ p * L ^ k) :=
    hasFullSourceSymbolBound_modifiedAmplitude a ha e Pj hPj N Rstar k hRstar hcost
      hL hlam hb p hj hsfreq
  have hgeometry := hfamily (elapsedPhase Ψ t) hS chart hopen hηinput hmapinput hJinput hgapinput
      hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
      hgap hJjet hηjet hscale hX₀ hF₀
  obtain ⟨hforward, _hweighted, _hreverse⟩ := hgeometry
  have hoperator := hforward A hA (B * lam ^ p * L ^ k) hsymbol
  obtain ⟨Treg, hT, hTa, hTr, hreg, hareg, hlim, halim, hfull, hreal, hareal⟩ := hoperator
  refine ⟨Treg, ?_, ?_, ?_, hreg, hareg, hlim, halim, hfull, hreal, hareal, ?_⟩
  · simpa only [mul_assoc] using hT
  · simpa only [mul_assoc] using hTa
  · simpa only [mul_assoc] using hTr
  · intro U hU
    exact (fullGraphOperator_eq_of_realizes (elapsedPhase Ψ t) A U hU).symm

end JanetCartan.ResponseTransfer.DirectEvolution.ModifiedLow
