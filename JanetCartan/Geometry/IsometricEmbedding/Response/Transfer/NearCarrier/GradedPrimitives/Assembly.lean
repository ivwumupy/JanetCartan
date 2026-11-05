module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Assembly.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Extension

/-!
# Global selected primitive profiles

The consumer is `NearCarrierSymbol.hasFullSourceSymbolBound_of_expression`
and `BranchRealization.exists_modifiedFullGraphL2_of_primitive_jets`.
For `app:ch_response:eq:direct-envelope-profile`, all five actual primitive
fields are assembled before multiplication by a single fixed smooth cutoff.
The cutoff equals one on an open neighborhood of the complete selected support.
The global jet constant is chosen before scale, frequency, and the fields.

The geometry producer supplies the compact complete support inside the open
joint buffer, raw phase jets through `N+2`, annular unshifted amplitude jets
through `N`, fixed selector jets through `N`, carrier jets through `N+1`,
and the primitive central inverse gap/Lipschitz data. These are conditional
analytic deductions, not the construction of the response geometry.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives
open FourierIntegral

/-- Values of the actual selected amplitude and four phase primitives of
`app:ch_response:eq:direct-envelope-profile`. -/
abbrev SelectedPrimitiveValues (n r p : ℕ) :=
  Matrix (Fin r) (Fin r) ℂ × PhasePrimitiveValues n p

/-- All five literal primitives; both physical positions and the carrier
parameter remain in the common derivative domain
(`app:ch_response:eq:direct-envelope-profile`). -/
def selectedPrimitives {n r p : ℕ} (a : FullAmplitude n r)
    (q : Euclidean p × Euclidean n → ℂ) (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean p → Euclidean n) (ρ : ℝ)
    (w : ParameterAmplitudePoint n (Euclidean p)) : SelectedPrimitiveValues n r p :=
  (normalizedParameterAmplitude a q ζ ρ w, phasePrimitives S ζ w)

/-- Explicit local profile, chosen before scale, frequency and coefficient
fields in `app:ch_response:eq:direct-envelope-profile`. -/
def selectedPrimitiveConstant (n p : ℕ) (A P Q : ℕ → ℝ) (Z M : ℝ) (j : ℕ) : ℝ :=
  selectedAmplitudeConstant P Q Z j + phasePrimitiveConstant n p A Z M j

/-- Nonnegativity for the global primitive expression budget
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem selectedPrimitiveConstant_nonneg (n p : ℕ) {A P Q : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hP : ∀ j, 0 ≤ P j) (hQ : ∀ j, 0 ≤ Q j)
    {Z : ℝ} (hZ : 0 ≤ Z) (M : ℝ) (j : ℕ) :
    0 ≤ selectedPrimitiveConstant n p A P Q Z M j :=
  add_nonneg (selectedAmplitudeConstant_nonneg hP hQ hZ j)
    (phasePrimitiveConstant_nonneg n p hA hZ M j)

/-- The actual selected amplitude is unchanged globally by a cutoff whose
plateau contains its complete support. Thus no shoulder is discarded in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem cutoffExtension_eq_of_support_subset {E F : Type*}
    [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : E → ℝ} {f : E → F} {K : Set E}
    (hs : tsupport f ⊆ K) (hp : EqOn χ (fun _ ↦ 1) K) :
    (fun x ↦ χ x • f x) = f := by
  funext x
  by_cases hx : x ∈ tsupport f
  · simp [hp (hs hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Global smooth representatives of all five literal primitives, with the
exact natural-subtraction exponent consumed by `DerivativeBounds`.

The compact set `Ksel` must contain the **entire** selected support, including
all mask shoulders and the compact parameter set. Its open buffer is fixed
before scale/frequency. All local analytic estimates are derived below from
raw phase/amplitude jets, fixed selector/carrier jets and the central gap.
In particular, neither inverse jets nor `C`/`-C B⁻¹` jets are hypotheses.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_global_selected_primitives {n r p : ℕ}
    {X V : Set (Euclidean n)} {C : Set (Euclidean p)}
    (hX : IsOpen X) (hV : IsOpen V) (hC : IsOpen C)
    {Ksel : Set (ParameterAmplitudePoint n (Euclidean p))}
    (hKsel : IsCompact Ksel) (hKU : Ksel ⊆ (X ×ˢ X ×ˢ V) ×ˢ C)
    (A P Q : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hP : ∀ j, 0 ≤ P j)
    (hQ : ∀ j, 0 ≤ Q j) (Z M : ℝ) (hZ : 0 ≤ Z) :
    ∃ (χ : ParameterAmplitudePoint n (Euclidean p) → ℝ)
      (Ω : Set (ParameterAmplitudePoint n (Euclidean p))) (G : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      IsOpen Ω ∧ Ksel ⊆ Ω ∧ Ω ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      EqOn χ (fun _ ↦ 1) Ω ∧ (∀ j, 0 ≤ G j) ∧
      ∀ (L ρ : ℝ) (N Rstar : ℕ), 1 ≤ L → 2 ≤ Rstar →
      ∀ (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
        (a : FullAmplitude n r) (q : Euclidean p × Euclidean n → ℂ)
        (D : Set (Euclidean n)),
      IsOpen D → Convex ℝ D →
      (∀ c ∈ C, ζ c ∈ D) → (∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) → ContDiffOn ℝ ∞ ζ C →
      ContDiffOn ℝ ∞ (normalizedFullAmplitude a ρ) (X ×ˢ X ×ˢ D) →
      ContDiffOn ℝ ∞ q (C ×ˢ V) →
      ∀ (b K : ℝ), 0 < b → (∀ c ∈ C, Metric.closedBall (ζ c) b ⊆ D) →
      (∀ x ∈ X, ∀ c ∈ C, IsUnit (mixedPhaseOperator S x (ζ c))) →
      (∀ x ∈ X, ∀ c ∈ C, ‖Ring.inverse (mixedPhaseOperator S x (ζ c))‖ ≤ M) →
      0 ≤ K → (∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K) →
      (∀ ε ∈ V, ‖ε‖ ≤ averagedMixedSelectorRadius b M K) →
      (∀ j ≤ N + 2, ∀ w ∈ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry S) w‖ ≤ A j * L ^ (j - Rstar)) →
      (∀ j ≤ N, ∀ w ∈ X ×ˢ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (normalizedFullAmplitude a ρ) w‖ ≤ P j * L ^ (j - (Rstar - 2))) →
      (∀ j ≤ N, ∀ w ∈ C ×ˢ V, ‖iteratedFDeriv ℝ j q w‖ ≤ Q j) →
      (∀ j, 1 ≤ j → j ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z) →
      tsupport (normalizedParameterAmplitude a q ζ ρ) ⊆ Ksel →
      ContDiff ℝ ∞ (cutoffExtension χ (selectedPrimitives a q S ζ ρ)) ∧
      HasCompactSupport (cutoffExtension χ (selectedPrimitives a q S ζ ρ)) ∧
      tsupport (cutoffExtension χ (selectedPrimitives a q S ζ ρ)) ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      tsupport (normalizedParameterAmplitude a q ζ ρ) ⊆ Ω ∧
      (fun w ↦ (cutoffExtension χ (selectedPrimitives a q S ζ ρ) w).1) =
        normalizedParameterAmplitude a q ζ ρ ∧
      (∀ w ∈ Ω, cutoffExtension χ (selectedPrimitives a q S ζ ρ) =ᶠ[𝓝 w]
        selectedPrimitives a q S ζ ρ) ∧
      (∀ j w, w ∈ Ω → iteratedFDeriv ℝ j (cutoffExtension χ (selectedPrimitives a q S ζ ρ))
        =ᶠ[𝓝 w] iteratedFDeriv ℝ j (selectedPrimitives a q S ζ ρ)) ∧
      ∀ j ≤ N, ∀ w, ‖iteratedFDeriv ℝ j
        (cutoffExtension χ (selectedPrimitives a q S ζ ρ)) w‖ ≤ G j * L ^ (j + 2 - Rstar) := by
  have hU := (hX.prod (hX.prod hV)).prod hC
  obtain ⟨χ, Ω, H, hχ, hrange, hc, hs, hΩ, hKΩ, hΩU, hp, hH, hχj, hext⟩ :=
    exists_reserve_preserving_cutoff_extension
      (E := SelectedPrimitiveValues n r p) hKsel hU hKU
  obtain ⟨G, hG, hglobal⟩ := hext (selectedPrimitiveConstant n p A P Q Z M)
    (selectedPrimitiveConstant_nonneg n p hA hP hQ hZ M)
  refine ⟨χ, Ω, G, hχ, hc, hs, hΩ, hKΩ, hΩU, hp, hG, ?_⟩
  intro L ρ N Rstar hL hR S ζ a q D hD hcD hζD hbuffer hS hζ ha hq
    b K hb hball hu hM hK hd hε hSjet hajet hqjet hζjet hsupport
  have hshift : MapsTo (carrierAmplitudeShift ζ) ((X ×ˢ X ×ˢ V) ×ˢ C) (X ×ˢ X ×ˢ D) :=
    fun _ hw ↦ ⟨hw.1.1, hw.1.2.1, hbuffer _ hw.2 _ hw.1.2.2⟩
  have hsel : ∀ w ∈ (X ×ˢ X ×ˢ V) ×ˢ C, (w.2, w.1.2.2) ∈ C ×ˢ V :=
    fun _ hw ↦ ⟨hw.2, hw.1.2.2⟩
  have hpar : ∀ w ∈ (X ×ˢ X ×ˢ V) ×ˢ C, w.2 ∈ C := fun _ hw ↦ hw.2
  have has : ContDiffOn ℝ ∞ (normalizedParameterAmplitude a q ζ ρ) ((X ×ˢ X ×ˢ V) ×ˢ C) := by
    apply contDiffOn_infty.mpr
    intro k
    exact normalizedParameterAmplitude_contDiffOn (ha.of_le (by simp)) (hq.of_le (by simp))
      (hζ.of_le (by simp)) hshift hsel hpar
  have hps := phasePrimitives_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ
    hb hball hu hM hK hd hε
  have hlocal : ContDiffOn ℝ ∞ (selectedPrimitives a q S ζ ρ) ((X ×ˢ X ×ˢ V) ×ˢ C) :=
    has.prodMk hps
  have hjlocal : ∀ j ≤ N, ∀ w ∈ (X ×ˢ X ×ˢ V) ×ˢ C,
      ‖iteratedFDeriv ℝ j (selectedPrimitives a q S ζ ρ) w‖ ≤
        selectedPrimitiveConstant n p A P Q Z M j * L ^ (j - (Rstar - 2)) := by
    intro j hj w hw
    apply norm_jet_pair_le_sum (has.contDiffAt (hU.mem_nhds hw))
      (hps.contDiffAt (hU.mem_nhds hw))
      (selectedAmplitudeConstant_nonneg hP hQ hZ j)
      (phasePrimitiveConstant_nonneg n p hA hZ M j) (pow_nonneg (zero_le_one.trans hL) _)
    · exact norm_jet_normalizedParameterAmplitude_le hU (hX.prod (hX.prod hD)) (hC.prod hV) hC
        (ha.of_le (by simp)) (hq.of_le (by simp)) (hζ.of_le (by simp)) hshift hsel hpar
        hP hQ hZ hL hajet hqjet (fun k hk hkN ↦ hζjet k hk (by omega)) hj hw
    · exact norm_jet_phasePrimitives_le hX hD hV hC hcD hζD hbuffer hS hζ
        hb hball hu hM hK hd hε hA hZ hL hR hSjet hζjet hj hw
  obtain ⟨hec, hecompact, hesupport, heagree, hejets, _, heprofile⟩ :=
    hglobal L hL (Rstar - 2) N _ hlocal hjlocal
  refine ⟨hec, hecompact, hesupport, hsupport.trans hKΩ, ?_, heagree, hejets, ?_⟩
  · exact cutoffExtension_eq_of_support_subset (hsupport.trans hKΩ) hp
  · intro j hj w
    simpa only [reserve_exponent hR] using heprofile j hj w

end JanetCartan.ResponseTransfer.GradedPrimitives
