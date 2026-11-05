module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Parameter
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.PhaseJets

/-!
# Assembly of the four literal phase primitives

For `app:ch_response:eq:direct-envelope-profile`, this module assembles the
actual `B`, `B⁻¹`, `C`, and `-C B⁻¹` from raw joint phase jets through `N+2`.
The two physical positions and all carrier parameters remain independent.
The consumer is the global cutoff assembly in `GradedPrimitives.Assembly`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

local instance phaseAssemblyMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- The actual four phase coefficients in the forward/reverse transfer formulas
of `app:ch_response:thm:response-literal-transfer`. This is a product of values,
not a record of assumed estimates. -/
abbrev PhasePrimitiveValues (n p : ℕ) :=
  Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
    (Euclidean n →L[ℝ] Euclidean p →L[ℝ] ℝ) ×
    (Euclidean n →L[ℝ] Euclidean p →L[ℝ] ℝ)

/-- Literal phase coefficients on both physical positions. Reverse coefficients
use the second position, including the sign and order `-C B⁻¹` in
`app:ch_response:thm:response-literal-transfer`. -/
def phasePrimitives {n p : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean p → Euclidean n) (q : ParameterAmplitudePoint n (Euclidean p)) :
    PhasePrimitiveValues n p :=
  (averagedMixedMatrix S (ζ q.2) 1 q.1.1 q.1.2.2,
    (averagedMixedMatrix S (ζ q.2) 1 q.1.2.1 q.1.2.2)⁻¹,
    parameterPhaseCoefficient S ζ q.1.1 q.1.2.2 q.2,
    signedReverseParameterCoefficient S ζ (reverseParameterAmplitudeProjection n p q))

/-- Pairing primitive fields costs only the sum of their constants, with no
extra derivative or scale power (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_pair_le_sum {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    {j : ℕ} {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hfj : ‖iteratedFDeriv ℝ j f x‖ ≤ A * t)
    (hgj : ‖iteratedFDeriv ℝ j g x‖ ≤ B * t) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (f y, g y)) x‖ ≤ (A + B) * t := by
  rw [iteratedFDeriv_prodMk hf hg (by simp), ContinuousMultilinearMap.opNorm_prod,
    add_mul]
  exact max_le (hfj.trans (le_add_of_nonneg_right (mul_nonneg hB ht)))
    (hgj.trans (le_add_of_nonneg_left (mul_nonneg hA ht)))

/-- Fixed joint profile of all four phase coefficients, derived from the raw
phase profile `A`. The two Hessian contractions cost exactly two derivatives
(`app:ch_response:eq:direct-envelope-profile`). -/
def phasePrimitiveConstant (n p : ℕ) (A : ℕ → ℝ) (Z M : ℝ) (j : ℕ) : ℝ :=
  segmentConstant (fun k ↦ (n : ℝ) * A (k + 2)) Z j +
    (‖(mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap‖ *
      inverseConstant (2 * M) (mixedConstant n (fun k ↦ (n : ℝ) * A (k + 2)) Z) j +
    (parameterConstant n p (fun k ↦ A (k + 2)) Z j +
      signedReverseParameterConstant n p (fun k ↦ (n : ℝ) * A (k + 2))
        (fun k ↦ A (k + 2)) Z M j))

private theorem inverse_profile_nonneg {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    (M : ℝ) (j : ℕ) : 0 ≤ inverseConstant M A j :=
  compositionConstant_nonneg
    (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
    hA j

/-- The assembled phase profile is nonnegative, as required by the primitive
expression interface (`app:ch_response:eq:direct-envelope-profile`). -/
theorem phasePrimitiveConstant_nonneg (n p : ℕ) {A : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) {Z : ℝ} (hZ : 0 ≤ Z) (M : ℝ) (j : ℕ) :
    0 ≤ phasePrimitiveConstant n p A Z M j := by
  have hB := fun k ↦ mul_nonneg (Nat.cast_nonneg n) (hA (k + 2))
  exact add_nonneg (segmentConstant_nonneg hB hZ j)
    (add_nonneg (mul_nonneg (norm_nonneg (mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap)
      (inverse_profile_nonneg (mixedConstant_nonneg n hB hZ) _ _))
      (add_nonneg (parameterConstant_nonneg n p (fun k ↦ hA (k + 2)) hZ j)
        (signedReverseParameterConstant_nonneg n p hB (fun k ↦ hA (k + 2)) hZ M j)))

section
variable {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)} {C : Set (Euclidean p)}
  (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
  (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
  (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
  (hζ : ContDiffOn ℝ ∞ ζ C)
  {b M K : ℝ} (hb : 0 < b) (hball : ∀ c ∈ C, Metric.closedBall (ζ c) b ⊆ D)
  (hu : ∀ x ∈ X, ∀ c ∈ C, IsUnit (mixedPhaseOperator S x (ζ c)))
  (hM : ∀ x ∈ X, ∀ c ∈ C, ‖Ring.inverse (mixedPhaseOperator S x (ζ c))‖ ≤ M)
  (hK : 0 ≤ K)
  (hd : ∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K)
  (hε : ∀ ε ∈ V, ‖ε‖ ≤ averagedMixedSelectorRadius b M K)

include hX hD hV hC hcD hζD hbuffer hS hζ hb hball hu hM hK hd hε

/-- All phase primitives are smooth on the joint buffer, from raw phase
smoothness and the central inverse gap alone
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem phasePrimitives_contDiffOn :
    ContDiffOn ℝ ∞ (phasePrimitives S ζ) ((X ×ˢ X ×ˢ V) ×ˢ C) := by
  have hs := mixedPhaseMatrix_contDiffOn_of_phase hX hD hS
  have hh := covectorHessian_contDiffOn_of_phase hX hD hS
  have hB := averagedMixedMatrix_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hs hζ
  have hI := averagedMixedInverse_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hs hζ
    hb hball hu hM hK hd hε
  have hIm : ContDiffOn ℝ ∞ (fun q : ParameterCoefficientSpace n p ↦
      (averagedMixedMatrix S (ζ q.2.2) 1 q.1 q.2.1)⁻¹) (X ×ˢ V ×ˢ C) := by
    convert (mixedMatrixOperatorEquiv n).symm.contDiff.comp_contDiffOn hI using 1
    funext q
    exact (mixedMatrixOperatorEquiv_symm_inverse _).symm
  exact (parameterAmplitude_pullback_contDiffOn hB).prodMk
    ((reverseParameterAmplitude_pullback_contDiffOn hIm).prodMk
      ((parameterAmplitude_pullback_contDiffOn
        (parameterPhaseCoefficient_contDiffOn hX hD hV hC hcD hζD hbuffer hh hζ)).prodMk
        (reverseParameterAmplitude_pullback_contDiffOn
          (signedReverseParameterCoefficient_contDiffOn hX hD hV hC hcD hζD hbuffer hs hζ
            hb hball hu hM hK hd hε hh))))

/-- The assembled reserve-graded phase profile from raw phase jets through
`N+2`, carrier jets through `N+1`, and the primitive central gap. No Hessian,
coefficient or positive-order inverse jets are premises. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_phasePrimitives_le {N j Rstar : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ k, 0 ≤ A k) (hZ : 0 ≤ Z) (hL : 1 ≤ L) (hR : 2 ≤ Rstar)
    (hSjet : ∀ k ≤ N + 2, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ k (Function.uncurry S) w‖ ≤ A k * L ^ (k - Rstar))
    (hζjet : ∀ k, 1 ≤ k → k ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ k ζ c‖ ≤ Z)
    (hj : j ≤ N) {q : ParameterAmplitudePoint n (Euclidean p)}
    (hq : q ∈ (X ×ˢ X ×ˢ V) ×ˢ C) :
    ‖iteratedFDeriv ℝ j (phasePrimitives S ζ) q‖ ≤
      phasePrimitiveConstant n p A Z M j * L ^ (j - (Rstar - 2)) := by
  have hs := mixedPhaseMatrix_contDiffOn_of_phase hX hD hS
  have hh := covectorHessian_contDiffOn_of_phase hX hD hS
  have hB := averagedMixedMatrix_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hs hζ
  have hI := averagedMixedInverse_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hs hζ
    hb hball hu hM hK hd hε
  have hIm : ContDiffOn ℝ ∞ (fun w : ParameterCoefficientSpace n p ↦
      (averagedMixedMatrix S (ζ w.2.2) 1 w.1 w.2.1)⁻¹) (X ×ˢ V ×ˢ C) := by
    convert (mixedMatrixOperatorEquiv n).symm.contDiff.comp_contDiffOn hI using 1
    funext w
    exact (mixedMatrixOperatorEquiv_symm_inverse _).symm
  have hAj := fun k ↦ mul_nonneg (Nat.cast_nonneg n) (hA (k + 2))
  have hBj := fun k hk w hw ↦ norm_jet_mixedPhaseMatrix_reserve_le hX hD hS hR hSjet
    (N := N) (j := k) hk (q := w) hw
  have hHj := fun k hk w hw ↦ norm_jet_covectorHessian_reserve_le hX hD hS hR hSjet
    (N := N) (j := k) hk (q := w) hw
  have hZj := fun k hk (hkN : k ≤ N) ↦ hζjet k hk (show k ≤ N + 1 by omega)
  have hparam := parameterCoefficients_graded_on_amplitude (Y := X) hX hD hV hC hcD hζD hbuffer hs hh hζ
    hb hball hu hM hK hd hε hAj (fun k ↦ hA (k + 2)) hZ hL hBj hHj hζjet
  have hbs := parameterAmplitude_pullback_contDiffOn (Y := X) hB
  have his := reverseParameterAmplitude_pullback_contDiffOn (Y := X) hIm
  have hcs := hparam.1
  have hrs := hparam.2.1
  have hbjet := (norm_jet_parameterAmplitude_pullback_le hX hV hC hB hq j).trans
    (norm_jet_averagedMixedMatrix_le hX hD hV hC hcD hζD hbuffer hs hζ hAj hZ hL
      hBj hZj hj ⟨hq.1.1, hq.1.2.2, hq.2⟩)
  have hival := norm_jet_averagedMixed_inverse_le
    (N := N) (k := j) (R := Rstar - 2) (A := fun k ↦ (n : ℝ) * A (k + 2))
    (Z := Z) (L := L) (q := (q.1.2.1, q.1.2.2, q.2))
    hX hD hV hC hcD hζD hbuffer hs hζ hAj hZ hL
    hBj hZj hj ⟨hq.1.2.1, hq.1.2.2, hq.2⟩ hb (hball _ hq.2)
    (hu _ hq.1.2.1 _ hq.2) (hM _ hq.1.2.1 _ hq.2) hK (hd _ hq.1.2.1)
    (hε _ hq.1.2.2)
  have hijet := (norm_jet_reverseParameterAmplitude_pullback_le hX hV hC hIm hq j).trans
    hival.2.2.2
  have hnh := ((hX.prod (hX.prod hV)).prod hC).mem_nhds hq
  have hpos := pow_nonneg (zero_le_one.trans hL) (j - (Rstar - 2))
  have hcpos := parameterConstant_nonneg n p (fun k ↦ hA (k + 2)) hZ j
  have hrpos := signedReverseParameterConstant_nonneg n p hAj (fun k ↦ hA (k + 2)) hZ M j
  have hipos := mul_nonneg (norm_nonneg (mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap)
    (inverse_profile_nonneg (mixedConstant_nonneg n hAj hZ) (2 * M) j)
  have hcr := norm_jet_pair_le_sum (hcs.contDiffAt hnh) (hrs.contDiffAt hnh)
    hcpos hrpos hpos (hparam.2.2.1 j hj q hq) (hparam.2.2.2 j hj q hq)
  have hicr := norm_jet_pair_le_sum (his.contDiffAt hnh) ((hcs.prodMk hrs).contDiffAt hnh)
    hipos (add_nonneg hcpos hrpos) hpos hijet hcr
  exact norm_jet_pair_le_sum (hbs.contDiffAt hnh) ((his.prodMk (hcs.prodMk hrs)).contDiffAt hnh)
    (segmentConstant_nonneg hAj hZ j) (add_nonneg hipos (add_nonneg hcpos hrpos))
    hpos hbjet hicr

end
end JanetCartan.ResponseTransfer.GradedPrimitives
