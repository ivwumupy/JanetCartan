module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.GraphMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.AlgebraicExtension

/-!
# The original kernels after removing auxiliary extensions

These equalities preserve every masked PDO symbol and both finite retarded
kernels, including the reversed kernel. The complete residual assembly uses
them to consume regularizations of the ORIGINAL conic phase and amplitudes.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

/-- All four physical PDO kernels retain the original masks and multiplier
when the auxiliary transport and frequency masks are removed. In particular,
the derivative acts on the entire unchanged algebraic symbol.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem maskedDirectPDOAmplitude_eq_of_auxiliary_masks
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    {V : Set T} (hV : IsOpen V) (κ : ℝ → ℝ)
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (W₁ : TwoTimeAmplitude d (d + 1))
    (bm : E → E → Mat) (σ : RootState (Euclidean d) → ℝ)
    (χout χsource β : E → ℂ)
    (hchart : ∀ x ∈ tsupport χout, ∀ ξ, β ξ ≠ 0 →
      ConicPhase.normalize ℓ (x 0, (x 0, (spatialPart x, spatialPart ξ))) ∈ V)
    (hκ : ∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] fun _ ↦ 1)
    (hρ : ∀ ξ, β ξ ≠ 0 → ρ (spatialPart ξ) = 1) (k : Fin 4) :
    let F₁ := fun p : T ↦ bufferedAmplitude V κ W₁ p.1 p.2.1 p.2.2.1 p.2.2.2
    let f₁ := fun p : T ↦ W₁ p.1 p.2.1 p.2.2.1 p.2.2.2
    (fun x z ξ ↦ (χout x * χsource z) • directPDOSymbols A B
      (curryCharacteristicMatrix (supportedConicMatrix ℓ 1 ρ F₁))
      bm (conicSourceSymbol ℓ ρ σ) β k x ξ) =
    fun x z ξ ↦ (χout x * χsource z) • directPDOSymbols A B
      (curryCharacteristicMatrix (ConicAmplitude.extend ℓ 1 f₁))
      bm (fun x η ↦ sourceSymbol σ x ((ℓ η)⁻¹ • η)) β k x ξ := by
  dsimp only
  have hc := conicAlgebraicSymbol_eq_on_frequency_plateau ℓ ρ σ β bm hρ
  fin_cases k
  · simp [directPDOSymbols, hc]
  · funext x z ξ
    simp [directPDOSymbols, conicSourceSymbol_mul_right_multiplier ℓ ρ σ β hρ]
  · funext x z ξ
    by_cases hx : χout x = 0
    · simp [hx]
    by_cases hξ : β ξ = 0
    · simp [directPDOSymbols, hξ]
    have he := supportedConicMatrix_slice_eq_of_masks ℓ 1 ρ hV κ W₁ (x 0)
      (spatialPart ξ) (hchart x (subset_tsupport χout hx) ξ hξ)
      (hκ x (subset_tsupport χout hx)) (hρ ξ hξ)
    simpa [directPDOSymbols] using
      congrArg (fun M : Mat ↦ (χout x * χsource z) • (β ξ • (A x 0 * M))) he.eq_of_nhds
  · simp [directPDOSymbols, hc]

/-- The supported smooth phase preserves the finite forward AND reversed
kernels for both complete retarded amplitudes, with the conjugated cutoff
in the literal adjoint. Consumer: `completeResidual_of_selected_physical_chart`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem directRetarded_regularizations_eq_of_supported_phase
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (F₀ F₁ : T → Mat) (Ψ G : T → ℝ)
    (hG : ∀ p ∈ tsupport F₀ ∪ tsupport F₁, G =ᶠ[𝓝 p] Ψ)
    (χout χsource β θ : E → ℂ) (r : ℝ) (k : Bool) :
    let b := directRetardedAmplitudes A B (curryCharacteristicMatrix F₀)
      (curryCharacteristicMatrix F₁) k
    let K := elapsedAmplitude b χout χsource β r
    let ψ := elapsedPhase (fun t s y η ↦ Ψ (t, (s, (y, η)))) r
    let g := elapsedPhase (fun t s y η ↦ G (t, (s, (y, η)))) r
    FourierIntegral.graphTestOutput g
        (FourierIntegral.frequencyCutFullAmplitude θ K) =
      FourierIntegral.graphTestOutput ψ
        (FourierIntegral.frequencyCutFullAmplitude θ K) ∧
    ∀ v : E → Fin (d + 1) → ℂ,
      FourierIntegral.reverseGraphOperator g
        (FourierIntegral.frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x z ξ ↦ (K x z ξ).conjTranspose)) v =
      FourierIntegral.reverseGraphOperator ψ
        (FourierIntegral.frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x z ξ ↦ (K x z ξ).conjTranspose)) v := by
  dsimp only
  have hz (t s : ℝ) (y η : Euclidean d)
      (hp : (t, (s, (y, η))) ∉ tsupport F₀ ∪ tsupport F₁) :
      directRetardedAmplitudes A B (curryCharacteristicMatrix F₀)
        (curryCharacteristicMatrix F₁) k t s y η = 0 := by
    cases k
    · have h₀ : F₀ (t, (s, (y, η))) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hp (Or.inl h))
      have h₁ : F₁ (t, (s, (y, η))) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hp (Or.inr h))
      simp only [directRetardedAmplitudes, Pi.add_apply, curryCharacteristicMatrix, h₀, h₁, add_zero]
    · exact twoTimePhysicalApply_eq_zero_off_support A B F₁ t s y η (fun h ↦ hp (Or.inr h))
  have he (x z ξ : E)
      (hK : elapsedAmplitude (directRetardedAmplitudes A B (curryCharacteristicMatrix F₀)
        (curryCharacteristicMatrix F₁) k) χout χsource β r x z ξ ≠ 0) :
      elapsedPhase (fun t s y η ↦ G (t, (s, (y, η)))) r x ξ =
        elapsedPhase (fun t s y η ↦ Ψ (t, (s, (y, η)))) r x ξ := by
    have hp : (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ tsupport F₀ ∪ tsupport F₁ := by
      by_contra hn
      exact hK (by simp [elapsedAmplitude, hz _ _ _ _ hn])
    exact congrArg (fun a ↦ (x 0 - r) * ξ 0 + a) ((hG _ hp).eq_of_nhds)
  constructor
  · apply FourierIntegral.graphTestOutput_phase_congr
    intro x z ξ hK
    exact he x z ξ (fun hz ↦ hK (by
      simp [FourierIntegral.frequencyCutFullAmplitude, hz]))
  · intro v
    apply FourierIntegral.reverseGraphOperator_phase_congr
    intro x z ξ hK
    exact he x z ξ (fun hz ↦ hK (by
      simp [FourierIntegral.frequencyCutFullAmplitude, hz]))

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates

