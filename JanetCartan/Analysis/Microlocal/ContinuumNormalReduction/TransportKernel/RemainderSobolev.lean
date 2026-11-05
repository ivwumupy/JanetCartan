module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev.Operator

/-!
# Sobolev gains for the original reflected Taylor remainder

The error following `app:ch_background:eq:bg-real-symbol` maps every integer
Hˢ datum to Hˢ⁺¹, as does its literal Hilbert adjoint. The amplitude is exactly
the original reflected amplitude with `k = 2πξ`, localized by fixed physical
cutoffs. Both frequency regimes and all physical derivative budgets are
constructed from primitive finite norms. The operator uses Euclidean Lebesgue
L² and the existing `IntegerBounds` realization.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol Pseudodifferential
open AmplitudeBound ContinuumNormal
variable {n N : ℕ}

set_option maxHeartbeats 800000 in
/-- The original reflected Taylor remainder and its literal Hilbert adjoint
gain one Sobolev derivative, including the L²-to-H¹ endpoint. Constants are
chosen before coefficients, geometry and the high norm `H`. The fixed low
coefficient/geometry orders are `2*(n+1)+3` and `2*(n+1)+5`; at input order
`s`, the corresponding high orders are `2*(n+1)+s+3` and `2*(n+1)+s+5`.
All three fixed cutoff jet bounds are explicit. `Mlow` constructs the L²
operator; `G` multiplies the single high norm only in the input L² term.
The geometric chart, conic and support premises remain the responsibility of
the normal-kernel assembly. Source: the paragraph following
`app:ch_background:eq:bg-real-symbol`. -/
theorem exists_localized_reflectedRemainder_integer_gain_of_primitiveNorms
    (hn : 0 < n) (c : TransportSliceCoordinates n) (a : InputVariables n)
    (b : Variables n × Euclidean 2) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {O : Set (Variables n × Euclidean 2)} (hO : IsOpen O)
    (houtput : closedBall b τ ⊆ O)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {M M₀ B₀ δ ε B : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hB₀ : 1 ≤ B₀)
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hη : ∀ p ∈ closedBall a ρ, ε ≤ ‖p.2.2‖)
    (D : CoefficientNormCharts n)
    (hfoot : ∀ p ∈ closedBall a ρ, D.Contains p)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β)
    {Bβ : ℝ} (hBβ : 0 ≤ Bβ)
    (hβBound : ∀ k ≤ (2 * (n + 1) + (s + 1)) + 1, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ)
    (i j : Fin n) (α γ : Euclidean n → ℝ)
    (hα : ContDiff ℝ ∞ α) (hγ : ContDiff ℝ ∞ γ)
    {Bα Bγ : ℝ} (hBα : 0 ≤ Bα) (hBγ : 0 ≤ Bγ)
    (hαb : ∀ k ≤ (2 * (n + 1) + (s + 1)), ∀ x, ‖iteratedFDeriv ℝ k α x‖ ≤ Bα)
    (hγb : ∀ k ≤ (2 * (n + 1) + (s + 1)), ∀ y, ‖iteratedFDeriv ℝ k γ y‖ ≤ Bγ)
    (Rcut : ℝ)
    (hαs : ∀ x, α x ≠ 0 → ∀ j, |x j| ≤ Rcut)
    (hγs : ∀ y, γ y ≠ 0 → ∀ j, |y j| ≤ Rcut) :
    ∃ Mlow : ℝ, 0 ≤ Mlow ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ G : ℝ, 0 ≤ G ∧ ∀ (d : Coefficients n N)
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (Ω : Set (Variables n × Euclidean 2))
      (U Z : Set (InputVariables n)) (X R : Set (Variables n)) (H : ℝ),
      ContDiffOn ℝ ∞ Y V → cNorm L 3 Y ≤ M →
      IsOpen Ω → O ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) (closedBall b τ) (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      EqOn J (transportAbsoluteJacobian c Y) W → (∀ p ∈ W, J p ≠ 0) →
      (∀ q ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y q) →
      1 + cNorm L ((2 * (n + 1) + 1) + 4) Y ≤ B →
      D.Controls ((2 * (n + 1) + 1) + 2) M₀ B₀ 1 d →
      1 ≤ H → 1 + cNorm L ((2 * (n + 1) + (s + 1)) + 4) Y ≤ B * H →
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls ((2 * (n + 1) + (s + 1)) + 2) M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (closure (augmentedTransportGradient Y '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ p : Variables n, ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      let brem := localizedRemainderAmplitude
        (freezingOutputProjection.prod freezingSourceProjection)
        (diagonalRemainderAmplitude basis
          (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
            (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) α γ
      ∃ (hbrem : ContDiff ℝ ∞ (Function.uncurry brem))
        (hsrem : ∀ ξ, SupportedInCenteredBox Rcut (brem ξ))
        (hMrem : HasAmplitudeDerivativeBound brem (2 * (n + 1)) Mlow),
        ∀ f : Lp ℂ 2 (volume : Measure (Euclidean n)), MemFourierSobolev (s : ℝ) f →
        let T := twoPositionL2Operator hn Rcut brem hbrem hsrem Mlow hMrem
        (MemFourierSobolev ((s : ℝ) + 1) (T f) ∧
          fourierSobolevNorm ((s : ℝ) + 1) (T f) ≤
            C * (fourierSobolevNorm (s : ℝ) f + max 1 (G * H) * ‖f‖)) ∧
        (MemFourierSobolev ((s : ℝ) + 1) (T.adjoint f) ∧
          fourierSobolevNorm ((s : ℝ) + 1) (T.adjoint f) ≤
            C * (fourierSobolevNorm (s : ℝ) f + max 1 (G * H) * ‖f‖)) := by
  let r₀ := 2 * (n + 1) + 1
  let r := 2 * (n + 1) + (s + 1)
  have hr : r₀ ≤ r := by dsimp [r₀, r]; omega
  have hβlow : ∀ k ≤ r₀ + 1, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ :=
    fun k hk y ↦ hβBound k (by dsimp [r₀, r] at *; omega) y
  obtain ⟨C₀, hC₀, low⟩ := exists_reflectedEntry_diagonalRemainder_joint_bounds_of_primitiveNorms
    (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
    r₀ hh hzero htail basis β hβ hBβ hβlow i j
  obtain ⟨C₁, hC₁, high⟩ := exists_reflectedEntry_diagonalRemainder_joint_bounds_of_primitiveNorms
    (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
    r hh hzero htail basis β hβ hBβ hβBound i j
  let Lpos := (freezingOutputProjection (d := n)).prod freezingSourceProjection
  let Mlow := remainderLocalizationConstant Lpos r₀ Bα Bγ * C₀
  let G := remainderLocalizationConstant Lpos r Bα Bγ * C₁
  have hMlow : 0 ≤ Mlow := by dsimp [Mlow, remainderLocalizationConstant]; positivity
  have hG : 0 ≤ G := by dsimp [G, remainderLocalizationConstant]; positivity
  obtain ⟨C, hC, hgain⟩ := exists_remainder_integer_gain_and_adjoint_constant hn Rcut s Mlow
  refine ⟨Mlow, hMlow, C, hC, G, hG, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hlowY hlowCoeff hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  obtain ⟨hc, hs₀, hj₀⟩ := low d Y u J Ω U Z X R 1 hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    le_rfl (by simpa only [mul_one] using hlowY) hreg hmap hsupp hR hXR hbuffer hshell
    hlowCoeff hscale huScale hJScale hupper hpunctured hnormalize
  obtain ⟨_, hs₁, hj₁⟩ := high d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  let rem := diagonalRemainderAmplitude basis
    (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
      (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β
  let brem := localizedRemainderAmplitude Lpos rem α γ
  have hbrem : ContDiff ℝ ∞ (Function.uncurry brem) :=
    contDiff_localizedRemainderAmplitude Lpos rem α γ hc hα hγ
  have hsrem : ∀ ξ, SupportedInCenteredBox Rcut (brem ξ) :=
    supportedInCenteredBox_localizedRemainderAmplitude rem α γ Rcut hαs hγs
  have hMweighted : ∀ ξ is, is.length ≤ r₀ → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (brem ξ) z‖ ≤ Mlow := by
    have he := weighted_coordinate_budget_localizedRemainderAmplitude Lpos rem α γ hc hα hγ
      r₀ hBα hBγ (fun k hk ↦ hαb k (hk.trans hr)) (fun k hk ↦ hγb k (hk.trans hr))
      (by positivity : 0 ≤ C₀ * 1) (by positivity : 0 ≤ C₀ * 1) hs₀
      (fun p _ k hk ↦ hj₀ p k hk)
    simpa only [max_self, mul_one] using he
  have hHweighted : ∀ ξ is, is.length ≤ r → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (brem ξ) z‖ ≤ G * H := by
    have he := weighted_coordinate_budget_localizedRemainderAmplitude Lpos rem α γ hc hα hγ
      r hBα hBγ hαb hγb (by positivity : 0 ≤ C₁ * H) (by positivity : 0 ≤ C₁ * H) hs₁
      (fun p _ k hk ↦ hj₁ p k hk)
    simpa only [max_self, G, mul_assoc] using he
  refine ⟨hbrem, hsrem,
    amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hMweighted)
      (Nat.le_succ _), ?_⟩
  intro f hf
  exact hgain brem hbrem hsrem (G * H) hMweighted hHweighted f hf

end JanetCartan.ContinuumRow.TransportKernel
