module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity.InverseEvaluations

/-!
# The complete primitive array after inverse substitution

The consumer is the literal density estimate of
`app:ch_background:eq:bg-full-complex-amplitude`. Both inverse points and
both coefficient sets remain present. Only the reference Jacobian is fixed
before the comparison constant; in particular, the high masks may vary.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity
open ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Every entry of the inverse-substituted primitive array is controlled by
the five primitive differences, the Jacobian difference, and the inverse
coordinate difference. There are no assumptions on composed coefficients.
The last two differences are supplied by
`CarrierVariation.exists_transportForwardJacobian_sub_le`; the reference
Jacobian's next jets enter only the fixed constant. Both high masks are
quantified after the constant, so uniform primitive bounds also cover
`high := fun r ↦ high (t * r)`. Source:
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_shellPrimitiveValues_inverse_sub_le_of_norms
    (D : CoefficientNormCharts n) {K : Set (InputVariables n)}
    {Q : Set (Variables n × Euclidean 2)} (hK : IsCompact K) (hQ : IsCompact Q)
    (hη : ∀ p ∈ K, p.2.2 ≠ 0) (hrange : ∀ p ∈ K, D.Contains p)
    {J₀ : InputVariables n → ℝ} (hJ₀ : ∀ p ∈ K, ContDiffAt ℝ ∞ J₀ p)
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (a a₀ : Coefficients n N) (J : InputVariables n → ℝ)
      (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (d : ℝ),
      0 ≤ d → D.Controls s M (M + 1) 1 a →
      D.Controls (s + 1) M (M + 1) 1 a₀ →
      (∀ p ∈ K, ContDiffAt ℝ ∞ J p) →
      cNorm K s J ≤ M → cNorm K s J₀ ≤ M →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates u) p) →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates u₀) p) →
      MapsTo (inverseCoordinates u) Q K → MapsTo (inverseCoordinates u₀) Q K →
      cNorm Q s (inverseCoordinates u) ≤ M → cNorm Q s (inverseCoordinates u₀) ≤ M →
      cNorm D.measurement.carrier s (a.measurement - a₀.measurement) ≤ d →
      cNorm D.angular.carrier s (a.angular - a₀.angular) ≤ d →
      cNorm D.high.carrier s (a.high - a₀.high) ≤ d →
      cNorm D.field.carrier s (a.normal - a₀.normal) ≤ d →
      cNorm D.field.carrier s (a.reduced - a₀.reduced) ≤ d →
      cNorm K s (J - J₀) ≤ d →
      cNorm Q s (inverseCoordinates u - inverseCoordinates u₀) ≤ d →
      (∀ p ∈ Q, ContDiffAt ℝ ∞ (shellPrimitiveValues a J ∘ inverseCoordinates u) p ∧
        ContDiffAt ℝ ∞ (shellPrimitiveValues a₀ J₀ ∘ inverseCoordinates u₀) p) ∧
      cNorm Q s (shellPrimitiveValues a J ∘ inverseCoordinates u) ≤ C ∧
      cNorm Q s (shellPrimitiveValues a₀ J₀ ∘ inverseCoordinates u₀) ≤ C ∧
      cNorm Q s (shellPrimitiveValues a J ∘ inverseCoordinates u -
        shellPrimitiveValues a₀ J₀ ∘ inverseCoordinates u₀) ≤ C * d := by
  have hc : ∀ p ∈ K, ContDiffAt ℝ ∞ (@shellEvaluationCoordinates n) p :=
    fun p hp ↦ shellEvaluationCoordinates_contDiffAt (hη p hp)
  obtain ⟨C₁, h₁, hb₁⟩ := exists_moving_primitive_evaluation_bounds (H := ℝ) D.measurement hQ hK
    (e := fun p : InputVariables n ↦ p.1.1) (fun p hp ↦ (hc p hp).fst.fst)
    (fun p hp ↦ (hrange p hp).1) s hM
  obtain ⟨C₂, h₂, hb₂⟩ := exists_moving_primitive_evaluation_bounds (H := ℝ) D.measurement hQ hK
    (e := fun p : InputVariables n ↦ p.1.2) (fun p hp ↦ (hc p hp).fst.snd.fst)
    (fun p hp ↦ (hrange p hp).2.1) s hM
  obtain ⟨C₃, h₃, hb₃⟩ := exists_moving_primitive_evaluation_bounds (H := ℝ) D.angular hQ hK
    (e := fun p : InputVariables n ↦ (p.2.1, ‖p.2.2‖⁻¹ • p.2.2))
    (fun p hp ↦ (hc p hp).fst.snd.snd.fst) (fun p hp ↦ (hrange p hp).2.2.1) s hM
  obtain ⟨C₄, h₄, hb₄⟩ := exists_moving_primitive_evaluation_bounds (H := ℝ) D.high hQ hK
    (e := fun p : InputVariables n ↦ ‖p.2.2‖)
    (fun p hp ↦ (hc p hp).fst.snd.snd.snd) (fun p hp ↦ (hrange p hp).2.2.2.1) s hM
  obtain ⟨C₅, h₅, hb₅⟩ := exists_moving_primitive_evaluation_bounds (H := Euclidean N) D.field hQ hK
    (e := fun p : InputVariables n ↦ (p.1.1, p.2.1))
    (fun p hp ↦ (hc p hp).snd.fst) (fun p hp ↦ (hrange p hp).2.2.2.2.1) s hM
  obtain ⟨C₆, h₆, hb₆⟩ := exists_moving_primitive_evaluation_bounds (H := Euclidean N) D.field hQ hK
    (e := fun p : InputVariables n ↦ (p.1.2, p.2.1))
    (fun p hp ↦ (hc p hp).snd.snd.fst) (fun p hp ↦ (hrange p hp).2.2.2.2.2) s hM
  obtain ⟨C₇, h₇, hb₇⟩ := exists_moving_primitive_evaluation_bounds (H := Fin n → ℝ) D.field hQ hK
    (e := fun p : InputVariables n ↦ (p.1.1, p.2.1))
    (fun p hp ↦ (hc p hp).snd.fst) (fun p hp ↦ (hrange p hp).2.2.2.2.1) s hM
  obtain ⟨C₈, h₈, hb₈⟩ := exists_moving_primitive_evaluation_bounds (H := Fin n → ℝ) D.field hQ hK
    (e := fun p : InputVariables n ↦ (p.1.2, p.2.1))
    (fun p hp ↦ (hc p hp).snd.snd.fst) (fun p hp ↦ (hrange p hp).2.2.2.2.2) s hM
  obtain ⟨R, hR, hjdiff⟩ := exists_cNorm_comp_sub_le_fixed_reference hQ hK hJ₀ s hM
  let P := compositionMultiplicity s * M * (1 + M) ^ s
  have hP : 0 ≤ P := by dsimp [P, compositionMultiplicity]; positivity
  obtain ⟨Cη, hCη, hηeval⟩ := exists_fixed_evaluation_bounds hQ hK
    (e := fun p : InputVariables n ↦ p.2.2) (fun p hp ↦ (hc p hp).snd.snd.snd) s hM
  refine ⟨(C₁ + (C₂ + (C₃ + (C₄ + (1 + R + P))))) +
    (Cη + (C₅ + (C₆ + (C₇ + C₈)))), by positivity, ?_⟩
  intro a a₀ J u u₀ d hd ha ha₀ hJ hJM hJ₀M hu hu₀ hr hr₀ hUM hU₀M hm ha' hh hn hq hj hi
  have hm₁ := hb₁ _ _ _ _ d hd ha.measurement ha₀.measurement hu hu₀ hr hr₀ hUM hU₀M hm hi
  have hm₂ := hb₂ _ _ _ _ d hd ha.measurement ha₀.measurement hu hu₀ hr hr₀ hUM hU₀M hm hi
  have hang := hb₃ _ _ _ _ d hd ha.angular ha₀.angular hu hu₀ hr hr₀ hUM hU₀M ha' hi
  have hhigh := hb₄ _ _ _ _ d hd ha.high ha₀.high hu hu₀ hr hr₀ hUM hU₀M hh hi
  have hn₁ := hb₅ _ _ _ _ d hd ha.normal ha₀.normal hu hu₀ hr hr₀ hUM hU₀M hn hi
  have hn₂ := hb₆ _ _ _ _ d hd ha.normal ha₀.normal hu hu₀ hr hr₀ hUM hU₀M hn hi
  have hq₁ := hb₇ _ _ _ _ d hd ha.reduced ha₀.reduced hu hu₀ hr hr₀ hUM hU₀M hq hi
  have hq₂ := hb₈ _ _ _ _ d hd ha.reduced ha₀.reduced hu hu₀ hr hr₀ hUM hU₀M hq hi
  have hj' : (∀ p ∈ Q, ContDiffAt ℝ ∞ (J ∘ inverseCoordinates u) p ∧
      ContDiffAt ℝ ∞ (J₀ ∘ inverseCoordinates u₀) p) ∧
      cNorm Q s (J ∘ inverseCoordinates u) ≤ 1 + R + P ∧
      cNorm Q s (J₀ ∘ inverseCoordinates u₀) ≤ 1 + R + P ∧
      cNorm Q s (J ∘ inverseCoordinates u - J₀ ∘ inverseCoordinates u₀) ≤ (1 + R + P) * d := by
    refine ⟨fun p hp ↦ ⟨(hJ _ (hr hp)).comp p (hu p hp),
      (hJ₀ _ (hr₀ hp)).comp p (hu₀ p hp)⟩, ?_, ?_, ?_⟩
    · exact (cNorm_comp_le_from_bounds hQ hK s hJ hu hr hM hJM hUM).trans
        (by change P ≤ _; linarith)
    · exact (cNorm_comp_le_from_bounds hQ hK s hJ₀ hu₀ hr₀ hM hJ₀M hU₀M).trans
        (by change P ≤ _; linarith)
    · exact (hjdiff J _ _ d hd hJ hu hu₀ hr hr₀ hUM hU₀M hj hi).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd)
  have he := hηeval _ _ d hd hu hu₀ hr hr₀ hUM hU₀M hi
  exact pair_evaluation_bounds hQ s
    (pair_evaluation_bounds hQ s hm₁ (pair_evaluation_bounds hQ s hm₂
      (pair_evaluation_bounds hQ s hang (pair_evaluation_bounds hQ s hhigh hj'))))
    (pair_evaluation_bounds hQ s he (pair_evaluation_bounds hQ s hn₁
      (pair_evaluation_bounds hQ s hn₂ (pair_evaluation_bounds hQ s hq₁ hq₂))))

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity
