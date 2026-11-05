module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.AlgebraicExtension
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual

/-!
# Localizing the physical coefficients without changing their action

Construct globally smooth coefficients agreeing near the closed output carrier.
Both the principal coefficients and `B` are localized with one scalar cutoff.
Physical actions and tested actions on that carrier agree exactly. Since the
paper's operator is in nondivergence form, no coefficient-cutoff derivative
enters its pointwise action; the formal test derivatives agree as germs.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open ActualCarriers
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d n : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- The coordinate-pulled coefficients admit one smooth extension near any
closed physical carrier contained in the original coefficient domain. This
constructs the global regularity required by the residual consumer from the
local smoothness in `exists_physical_pencil_kernel`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_smooth_coordinate_coefficients
    (i : Fin (d + 1)) {Ω : Set E} (hΩ : IsOpen Ω)
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    {K : Set E} (hK : IsClosed K) (hKΩ : ∀ x ∈ K, physicalCoordinates i x ∈ Ω) :
    ∃ A : E → Fin (d + 1) → Mat, ∃ B' : E → Mat,
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ B' ∧
      ∀ x ∈ K, A =ᶠ[𝓝 x] coefficient i Q ∧ B' =ᶠ[𝓝 x] zeroth i B := by
  let O := physicalCoordinates i ⁻¹' Ω
  have hO : IsOpen O := hΩ.preimage (physicalCoordinates i).continuous
  obtain ⟨U, hU, hKU, hUO⟩ := normal_exists_closure_subset hK hO hKΩ
  obtain ⟨V, hV, hUV, hVO⟩ := normal_exists_closure_subset isClosed_closure hO hUO
  obtain ⟨χ, hχ, _, hsχ, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  have hs : tsupport χ ⊆ O := by simpa only [tsupport, hsχ] using hVO
  have hQp := hQ.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hx ↦ hx)
  have hAp : ContDiffOn ℝ ∞ (coefficient i Q) O :=
    contDiffOn_pi.mpr fun a ↦ contDiff_pencil.comp_contDiffOn (hQp.prodMk contDiffOn_const)
  have hBp : ContDiffOn ℝ ∞ (zeroth i B) O :=
    hB.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hx ↦ hx)
  have ha : ContDiff ℝ ∞ (fun x ↦ χ x • coefficient i Q x) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      (hχ.contDiffOn.smul hAp) ((tsupport_smul_subset_left _ _).trans hs)
  have hb : ContDiff ℝ ∞ (fun x ↦ χ x • zeroth i B x) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      (hχ.contDiffOn.smul hBp) ((tsupport_smul_subset_left _ _).trans hs)
  refine ⟨_, _, ha, hb, ?_⟩
  intro x hx
  have he : χ =ᶠ[𝓝 x] fun _ ↦ 1 := by
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    exact (hχone y).mp (subset_closure hy)
  constructor <;> filter_upwards [he] with y hy <;> simp [hy]

/-- Coefficient equality at the physical point suffices for the full
nondivergence operator, including `B`.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem firstOrderApply_eq_of_coefficients
    (A A' : E → Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ)
    (B B' : E → Matrix (Fin n) (Fin n) ℂ) (u : E → Fin n → ℂ)
    {x : E} (hA : A x = A' x) (hB : B x = B' x) :
    WKB.firstOrderApply (fun y a ↦ (A y a).mulVecLin) (fun y ↦ (B y).mulVecLin) u x =
      WKB.firstOrderApply (fun y a ↦ (A' y a).mulVecLin) (fun y ↦ (B' y).mulVecLin) u x := by
  simp only [WKB.firstOrderApply, hA, hB]

/-- Equality of the differentiated matrix under coefficient localization.
The complete matrix derivative, including all source-symbol derivatives,
is retained. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem twoTimePhysicalApply_eq_of_coefficients
    (A A' : E → Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ)
    (B B' : E → Matrix (Fin n) (Fin n) ℂ) (W : TwoTimeAmplitude d n)
    {x : E} (hA : A x = A' x) (hB : B x = B' x) (s : ℝ) (η : Euclidean d) :
    twoTimePhysicalApply A B W (x 0) s (spatialPart x) η =
      twoTimePhysicalApply A' B' W (x 0) s (spatialPart x) η := by
  have hx : timeSpacePoint (x 0) (spatialPart x) = x :=
    timeSpaceMeasurableEquiv.symm_apply_apply x
  simp only [twoTimePhysicalApply, physicalSymbolApply, hx, hA, hB]

/-- Localization also preserves the exact distributional test action. The
derivatives are of the full test/coefficient products, which agree globally
because the test is supported on the coefficient-agreement carrier.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalTestAction_eq_of_coefficients_on_support
    (A A' : E → Fin (d + 1) → Matrix (Fin n) (Fin n) ℝ)
    (B B' : E → Matrix (Fin n) (Fin n) ℝ) (u : E → Fin n → ℂ)
    (φ : E → ℝ) (hA : ∀ x ∈ tsupport φ, A x = A' x)
    (hB : ∀ x ∈ tsupport φ, B x = B' x) (j : Fin n) :
    physicalTestAction A B u φ j = physicalTestAction A' B' u φ j := by
  have ha (a : Fin (d + 1)) (k : Fin n) :
      (fun x ↦ φ x * A x a j k) = fun x ↦ φ x * A' x a j k := by
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · rw [hA x (subset_tsupport φ hx)]
  have hb (k : Fin n) : (fun x ↦ φ x * B x j k) = fun x ↦ φ x * B' x j k := by
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · rw [hB x (subset_tsupport φ hx)]
  simp only [physicalTestAction, ha, funext_iff.mp (hb _) _]

/-- Both literal retarded amplitudes, with both physical masks, are unchanged
by coefficient localization on the output carrier. This also identifies all
frequency regularizations and their reverse kernels.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem elapsedDirectAmplitude_eq_of_coefficients
    (A A' : E → Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ)
    (B B' : E → Matrix (Fin n) (Fin n) ℂ) (W₀ W₁ : TwoTimeAmplitude d n)
    (χout χsource β : E → ℂ)
    (hA : ∀ x ∈ tsupport χout, A x = A' x)
    (hB : ∀ x ∈ tsupport χout, B x = B' x) (k : Bool) (r : ℝ) :
    elapsedAmplitude (directRetardedAmplitudes A B W₀ W₁ k) χout χsource β r =
      elapsedAmplitude (directRetardedAmplitudes A' B' W₀ W₁ k) χout χsource β r := by
  funext x z ξ
  by_cases hx : χout x = 0
  · simp [elapsedAmplitude, hx]
  · cases k
    · rfl
    · simp only [directRetardedAmplitudes, elapsedAmplitude]
      rw [twoTimePhysicalApply_eq_of_coefficients A A' B B' W₁
        (hA x (subset_tsupport χout hx)) (hB x (subset_tsupport χout hx))]

/-- All four masked PDO amplitudes, including the derivative of the entire
algebraic symbol, agree with the ORIGINAL coefficients. Thus localization
does not change their operators, cutoffs or literal adjoints.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem maskedDirectPDOAmplitude_eq_of_coefficients
    (A A' : E → Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ)
    (B B' : E → Matrix (Fin n) (Fin n) ℂ) (W₁ : TwoTimeAmplitude d n)
    (bminus : E → E → Matrix (Fin n) (Fin n) ℂ) (σ : E → Euclidean d → ℂ)
    (χout χsource β : E → ℂ)
    (hA : ∀ x ∈ tsupport χout, A x = A' x)
    (hB : ∀ x ∈ tsupport χout, B x = B' x) (k : Fin 4) :
    (fun x z ξ ↦ (χout x * χsource z) • directPDOSymbols A B W₁ bminus σ β k x ξ) =
      fun x z ξ ↦ (χout x * χsource z) • directPDOSymbols A' B' W₁ bminus σ β k x ξ := by
  funext x z ξ
  by_cases hx : χout x = 0
  · simp [hx]
  · have ha := hA x (subset_tsupport χout hx)
    have hb := hB x (subset_tsupport χout hx)
    fin_cases k <;> simp [directPDOSymbols, physicalSymbolApply, ha, hb]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
