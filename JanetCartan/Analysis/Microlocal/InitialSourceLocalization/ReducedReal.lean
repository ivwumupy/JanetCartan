module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.ReducedSigned
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.LocalQuadratures

/-!
# Initial localization of the actual local reduced signed source

The full stress contraction and both physical cutoffs form the same reduced
modulated source. The restriction and zero extension are the ones used by the
measured inverse. The first even right mask acts by `localRealCompression`;
the estimate applies to its single identity subtraction on both quadratures.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization LocalSobolev SignedProductEstimates
open ResponseSourceExtension ResponseTransfer.SourceNegative Sampling.BackgroundModulation
open ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic.RetardedLocalization

variable {d N : ℕ}
local notation "n" => (d + 1 : ℕ)
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "RV" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Both literal reduced signed quadratures have arbitrary initial accuracy
under the SAME first even proof mask. The published full-amplitude producer
and the proved nonstationary kernel estimate discharge their analytic bounds;
the original source cutoff discharges zero-extension admission
(`app:ch_pairs:prop:pairs-lag-sum`, `app:ch_regular:eq:source-tail`). -/
theorem exists_reducedSigned_local_initialSource_accuracy_constants
    (K : Set E) (hK : IsCompact K) (δ G : ℝ) (hδ : 0 < δ)
    (P D X Y CQ C : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hD : ∀ j, 0 ≤ D j)
    (hX : ∀ j, 0 ≤ X j) (hY : ∀ j, 0 ≤ Y j)
    (hCQ : ∀ j, 0 ≤ CQ j) (hC : ∀ j, 0 ≤ C j)
    (s : ℕ) {σ : ℝ} (hσ : 0 < σ) (accuracy : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (m : LocalizerSymbol n), ContDiff ℝ ∞ m → HasCompactSupport m →
    (∀ j p, ‖iteratedFDeriv ℝ j m p‖ ≤ D j) →
    (∀ y ξ, m (y, -ξ) = m (y, ξ)) →
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
    ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W →
    ∀ c : ℂ, ‖c‖ = 1 →
    let h := l2RealPart (volume.restrict W) (c • restrictL2 W (hf.toLp f))
    let e := h - localRealCompression hW W M h
    e ∈ (restrictionSobolevScale W RV hW).level s ∧
      (restrictionSobolevScale W RV hW).gradeNorm s e ≤ B * (ρ sign) ^ (-accuracy) := by
  obtain ⟨B, hB, hb⟩ := exists_reducedSigned_initialSource_accuracy_constants (N := N)
    K hK δ G hδ P D X Y CQ C hP hD hX hY hCQ hC s hσ accuracy
  refine ⟨2*B, by positivity, ?_⟩
  intro m hm hmc hmjet heven S hplateau U hU hKU χ ψ Q A₁ A₂ hχ hψ hQ hA₁ hA₂ hχK
    L hL hχjet hψjet hQjet hA₁jet hA₂jet φ ρ hφ hρ hscale hgraph hupper hphase sign a f
  obtain ⟨hf, hbound⟩ := hb m hm hmc hmjet S hplateau U hU hKU χ ψ Q A₁ A₂
    hχ hψ hQ hA₁ hA₂ hχK L hL hχjet hψjet hQjet hA₁jet hA₂jet φ ρ
    hφ hρ hscale hgraph hupper hphase sign
  refine ⟨hf, fun M hM W hW hχW c hc ↦ ?_⟩
  dsimp only
  rw [local_initialSource_modulated_quadrature_defect (ρ sign) m heven M hM
    χ (φ sign) a hf hW hχW c]
  obtain ⟨hmemb, hnorm⟩ := hbound M hM W hW
  obtain ⟨hrmem, hrnorm⟩ := initial_quadrature_restriction_scale_bound W hW s _ hmemb c hc
  refine ⟨hrmem, hrnorm.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

end JanetCartan.InitialSourceLocalization
