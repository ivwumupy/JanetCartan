module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Accuracy
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources

/-!
# Initial localization of the original reduced signed sources

Apply the primitive estimate to the full plus/minus tensors, their original
half stress contraction and BOTH physical cutoffs. The existing reduced jet
producer supplies the amplitude profile with zero additional slow-scale
loss. One constant works for both signs and the same right proof mask.
The normalized phase and its true beat frequency remain the parent's actual
signed-phase application, as does inclusion of its graph in the common source
compact selected by terminal protection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Metric MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization LocalSobolev SignedProductEstimates
open ResponseSourceExtension ResponseTransfer.SourceNegative Sampling.BackgroundModulation
open RegularSector.Characteristic.RetardedLocalization

variable {d N : ℕ}
local notation "n" => (d + 1 : ℕ)
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Actual initial localization of both reduced signed amplitudes, including
the whole tensor, the original stress row, the factor one half and both
cutoffs. The constant is chosen before sources, frequencies and varying
proof masks. No reduced-amplitude jet or source-tail bound is a premise;
the published Leibniz producer supplies those jets
(`app:ch_pairs:prop:pairs-lag-sum`, `app:ch_regular:eq:source-tail`). -/
theorem exists_reducedSigned_initialSource_accuracy_constants
    (K : Set E) (hK : IsCompact K) (δ G : ℝ) (hδ : 0 < δ)
    (P D X Y CQ C : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hD : ∀ j, 0 ≤ D j)
    (hX : ∀ j, 0 ≤ X j) (hY : ∀ j, 0 ≤ Y j)
    (hCQ : ∀ j, 0 ≤ CQ j) (hC : ∀ j, 0 ≤ C j)
    (s : ℕ) {σ : ℝ} (hσ : 0 < σ) (accuracy : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (m : LocalizerSymbol n), ContDiff ℝ ∞ m → HasCompactSupport m →
    (∀ j p, ‖iteratedFDeriv ℝ j m p‖ ≤ D j) →
    ∀ (S : Set (E × E)), cthickening δ S ⊆ interior {p | m p = 1} →
    ∀ (U : Set E), IsOpen U → K ⊆ U →
    ∀ (χ ψ : E → ℝ) (Q : E → Fin n → MetricTensor n)
      (A₁ A₂ : E → Matrix (Fin N) (Fin n) ℂ),
    ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
    ContDiffOn ℝ ∞ A₁ U → ContDiffOn ℝ ∞ A₂ U → tsupport χ ⊆ K →
    ∀ (L : ℝ), 1 ≤ L →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j χ y‖ ≤ X j * L ^ j) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j ψ y‖ ≤ Y j * L ^ j) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j Q y‖ ≤ CQ j * L ^ j) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j A₁ y‖ ≤ C j * L ^ j) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j A₂ y‖ ≤ C j * L ^ j) →
    ∀ (φ : Bool → E → ℝ) (ρ : Bool → ℝ),
    (∀ sign, ContDiffOn ℝ ∞ (φ sign) U) →
    (∀ sign, 1 ≤ ρ sign) → (∀ sign, L ≤ (ρ sign) ^ (1 - σ)) →
    (∀ sign y, y ∈ tsupport χ → (y, gradient (φ sign) y) ∈ S) →
    (∀ sign y, y ∈ U → ‖fderiv ℝ (φ sign) y‖ ≤ G) →
    (∀ sign y, y ∈ tsupport χ → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j+1) (φ sign) y‖ ≤ P j * L ^ j) →
    ∀ sign : Bool,
    let a := fun y ↦ ψ y • ((1 / 2 : ℝ) • complexStressContraction (Q y)
      (if sign then symmetricBilinearTensor (A₁ y) ((A₂ y).map conj)
        else symmetricBilinearTensor (A₁ y) (A₂ y)))
    let f := modulatedSource χ (φ sign) a (ρ sign)
    ∃ hf : MemLp f 2 volume,
    ∀ (M : H →L[ℂ] H),
    (∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer (ρ sign) m (fun y ↦ (v y).ofLp) x)) →
    ∀ (W : Set E) (hW : MeasurableSet W),
      restrictL2 W (hf.toLp f - M (hf.toLp f)) ∈
        (restrictionSobolevScale W V hW).level s ∧
      (restrictionSobolevScale W V hW).gradeNorm s
        (restrictL2 W (hf.toLp f - M (hf.toLp f))) ≤ B * (ρ sign) ^ (-accuracy) := by
  obtain ⟨J, hJ, hj⟩ := exists_cutoff_reduced_signed_jet_constants («n» := n) (N := N)
    X Y CQ C hX hY hCQ hC
  obtain ⟨B, hB, hb⟩ := exists_initialSource_restriction_accuracy_constant (r := n)
    K hK δ G hδ P D J hP hD hJ 0 s hσ accuracy
  refine ⟨B, hB, ?_⟩
  intro m hm hmc hmjet S hplateau U hU hKU χ ψ Q A₁ A₂ hχ hψ hQ hA₁ hA₂ hχK
    L hL hχjet hψjet hQjet hA₁jet hA₂jet φ ρ hφ hρ hscale hgraph hupper hphase sign a f
  obtain ⟨hap, ham⟩ := contDiffOn_reduced_signed_amplitudes hQ hψ hA₁ hA₂
  have ha : ContDiffOn ℝ ∞ a U := by
    cases sign
    · exact hap
    · exact ham
  let aχ := fun y ↦ χ y • a y
  have haχ : ContDiffOn ℝ ∞ aχ U := hχ.smul ha
  have hsχ : tsupport aχ ⊆ tsupport χ := tsupport_smul_subset_left _ _
  have hajet y (hy : y ∈ tsupport aχ) j :
      ‖iteratedFDeriv ℝ j aχ y‖ ≤ J j * (((1 : ℝ) * L ^ (0 : ℕ)) * L ^ j) := by
    have h := hj U hU L hL χ ψ Q A₁ A₂ hχ hψ hQ hA₁ hA₂
      hχjet hψjet hQjet hA₁jet hA₂jet y (hKU (hχK (hsχ hy))) j
    cases sign
    · simpa only [aχ, a, Bool.false_eq_true, ↓reduceIte, pow_zero, mul_one, one_mul] using h.1
    · simpa only [aχ, a, ↓reduceIte, pow_zero, mul_one, one_mul] using h.2
  have heq : f = fun y ↦ phaseOscillation (fun z ↦ ρ sign * φ sign z) y • aχ y := by
    funext y
    exact smul_comm _ _ _
      |>.trans (by rw [carrier_eq_phaseOscillation])
  have hfsmooth : ContDiff ℝ ∞ f := by
    rw [heq]
    have he : ContDiffOn ℝ ∞ (fun y ↦
        phaseOscillation (fun z ↦ ρ sign * φ sign z) y • aχ y) U :=
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((hφ sign).const_smul (ρ sign))).mul contDiffOn_const).cexp.smul haχ
    exact contDiff_of_contDiffOn_support_neighborhood hU he
      ((tsupport_smul_subset_right _ _).trans (hsχ.trans (hχK.trans hKU)))
  have hfc : HasCompactSupport f := by
    rw [heq]
    have hac : HasCompactSupport aχ :=
      hK.of_isClosed_subset (isClosed_tsupport _) (hsχ.trans hχK)
    exact hac.smul_left (f := phaseOscillation (fun z ↦ ρ sign * φ sign z))
  have hf : MemLp f 2 volume := hfsmooth.continuous.memLp_of_hasCompactSupport hfc
  refine ⟨hf, fun M hM W hW ↦ ?_⟩
  have hu : hf.toLp f =ᵐ[volume]
      fun y ↦ phaseOscillation (fun z ↦ ρ sign * φ sign z) y • aχ y :=
    hf.coeFn_toLp.trans (Filter.Eventually.of_forall (congrFun heq))
  simpa only [mul_one] using hb m hm hmc (φ sign) aχ hU hKU (hφ sign) haχ
    (hsχ.trans hχK) zero_le_one hL (hρ sign) (hscale sign)
    (fun y hy ↦ hgraph sign y (hsχ hy)) hplateau (hupper sign) hmjet
    (fun y hy ↦ hphase sign y (hsχ hy)) hajet M hM (hf.toLp f) hu W hW

end JanetCartan.InitialSourceLocalization
