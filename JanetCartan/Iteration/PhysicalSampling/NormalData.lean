module

public import JanetCartan.Iteration.PhysicalSampling.Support

/-!
# Insert the actual scalar cutoff into the original full phase geometry

Every amplitude field of `UniformNormalData` is proved for the literal scalar
auxiliary row. The phase, parameter interval, inverse charts, buffers and
Jacobian gap remain those of the supplied original phase data. Their actual
producer is `FullNormalGeometry.exists_uniform_literalFullPhaseNormalData`;
this local deduction does not replace its original-data instantiation.

Consumer: the scalar continuum mean bound in `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts NormalComparison
open Sampling Sampling.MeasuredAmplitude Sampling.FullNormalGeometry
open Sampling.FullNormalGeometry.PhaseJets
open PhysicalMean ContinuumRow ContinuumRow.CanonicalConic

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Construct all scalar-amplitude normal data with one budget before the
current immersion, phase family, band labels and samples. The primitive
support premises are those of the SAME fixed physical/carrier/angular masks;
no scalar operator bound or successful realization is assumed. -/
theorem exists_scalarNormalData
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH : ContDiff ℝ ∞ H) (hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1)
    (G : UniformNormalGeometry (m + 1) (m + 1)) (Cphase : ℕ → ℝ)
    {V : Set (Euclidean 2)} (hV : IsCompact V)
    {z₀ : Euclidean 3} {ηb : Euclidean m} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 →
      NormedSpace.normalize θ ∈ closedDirections (n := m + 1) ηb radius)
    (hχ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ G.X₀)
    (hψs : ∀ v ∈ V, ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      s ∈ closedBall (z₀ 0) radius)
    (hD : G.D₀ = radialSamplingSupport T z₀ ηb radius amin amax) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ v ∈ V, ∀ j (N₀ : UniformNormalData G Cphase) (M : ℝ),
        N₀.extensionDomain = fullPhaseExtensionDomain T v M →
        ∃ N : UniformNormalData G (fun k ↦ Cphase k + B k),
          N.phase = N₀.phase ∧ N.parameterDomain = N₀.parameterDomain ∧
          N.extensionDomain = N₀.extensionDomain ∧
          N.amplitude = (fun ε x u ↦
            (scalarNormalizedAmplitude T χ ψ angular H j (ε, v, x, u)).ofLp) := by
  let S := Icc (0 : ℝ) G.ε₀ ×ˢ (V ×ˢ (closure G.X ×ˢ closure G.D))
  have hS : IsCompact S := isCompact_Icc.prod (hV.prod
    (G.bounded_X.isCompact_closure.prod G.bounded_D.isCompact_closure))
  obtain ⟨A, hA, hjet⟩ := exists_scalarNormalizedAmplitude_budgets T χ ψ hψ
    angular H ha hah hH hH₁ hS
  let B (k : ℕ) := 1 + ‖measuredOutputCoordinates (m + 1)‖ * (A k + A (k + 1))
  have hB (k : ℕ) : 0 < B k := by
    have := hA k
    have := hA (k + 1)
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro v hv j N₀ M hW
  let amp := scalarNormalizedAmplitude T χ ψ angular H j
  have hs : ContDiff ℝ ∞ amp :=
    contDiff_scalarNormalizedAmplitude T χ ψ hψ angular H ha hH j
  have hampSmooth : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
        (amp (q.1, v, q.2)).ofLp) (N₀.parameterDomain ×ˢ N₀.extensionDomain) :=
    (PiLp.contDiff_ofLp.comp (hs.comp (by fun_prop))).contDiffOn
  have hampSupport (ε : ℝ) (_hε : ε ∈ Icc 0 G.ε₀) :
      Function.support (fun w : Euclidean (m + 1) × Euclidean (m + 1) ↦
        (amp (ε, v, w)).ofLp) ⊆ G.X₀ ×ˢ G.D₀ := by
    have hh := support_scalarNormalizedAmplitude_subset T χ ψ angular H hah
      hηb hradius hlo hhi hangle hχ v (hψs v hv) j ε
    rw [hD]
    intro w hw
    apply hh
    change amp (ε, v, w) ≠ 0
    intro hz
    apply hw
    change (amp (ε, v, w)).ofLp = 0
    rw [hz]
    rfl
  have hampJets (ε : ℝ) (hε : ε ∈ Icc 0 G.ε₀)
      (w : Euclidean (m + 1) × Euclidean (m + 1)) (hw : w ∈ G.X ×ˢ G.D) (k : ℕ) :
      ‖iteratedFDeriv ℝ k (fun y ↦ (amp (ε, v, y)).ofLp) w‖ +
        ‖deriv (fun t ↦ iteratedFDeriv ℝ k (fun y ↦ (amp (t, v, y)).ofLp) w) ε‖ ≤ B k := by
    have hwc : w ∈ closure G.X ×ˢ closure G.D :=
      ⟨subset_closure hw.1, subset_closure hw.2⟩
    have hw' : w ∈ fullPhaseExtensionDomain T v M := by
      simpa only [hW] using N₀.spatial_subset hwc
    have hmem : (ε, v, w) ∈ S := ⟨hε, hv, hwc⟩
    have hb := (measured_inputJets_le_joint T hs.contDiffOn ε hw' k).trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (hjet j (ε, v, w) hmem k) (hjet j (ε, v, w) hmem (k + 1)))
        (norm_nonneg _))
    exact hb.trans (le_add_of_nonneg_left zero_le_one)
  let N : UniformNormalData G (fun k ↦ Cphase k + B k) := {
    N₀ with
    amplitude := fun ε x u ↦ (amp (ε, v, x, u)).ofLp
    amplitude_smooth := hampSmooth
    amplitude_support := hampSupport
    input_jets := by
      intro ε hε w hw k hk
      have hp := N₀.input_jets ε hε w hw k hk
      have ha := hampJets ε hε w hw k
      have hz₁ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude ε)) w)
      have hz₂ := norm_nonneg (deriv (fun t ↦
        iteratedFDeriv ℝ k (Function.uncurry (N₀.amplitude t)) w) ε)
      simp only [Function.uncurry_def, Prod.mk.eta] at hp ha hz₁ hz₂ ⊢
      linarith }
  exact ⟨N, rfl, rfl, rfl, rfl⟩

end JanetCartan.PhysicalSampling
