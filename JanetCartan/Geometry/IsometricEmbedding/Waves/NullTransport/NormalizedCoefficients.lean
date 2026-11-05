module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.NormalizedCoefficients.Differential
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth normalized null transport coefficients

Conditional deductions for `app:ch_waves:eq:reduced-symbol` and
`app:ch_waves:thm:leading`. The actual-carrier construction must supply the
smooth symmetric frame, smooth characteristic covector, fixed adjugate entry gap,
and positive time-root derivative gap on the common patch. These inputs imply
regularity of the selected nullvectors and normalized transport coefficients;
neither a transport solution nor a carrier-menu existence theorem is assumed.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport

variable {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {m : ℕ∞ω}

/-- Literal symbol compatibility in `app:ch_waves:eq:reduced-symbol`. -/
theorem reducedSymbol_eq_pencil (Q : Fin n → MetricTensor n) (ξ : Euclidean n) :
    reducedSymbol Q ξ = ActualCarriers.pencil Q ξ := rfl

/-- Literal determinant compatibility in `app:ch_waves:eq:reduced-symbol`. -/
theorem reducedDeterminant_eq_determinant (Q : Fin n → MetricTensor n) :
    reducedDeterminant Q = ActualCarriers.determinant Q := rfl

/-- Joint smoothness of the actual symbol entries (`app:ch_waves:eq:reduced-symbol`). -/
theorem contDiffOn_reducedSymbol_entry {Q : E → Fin n → MetricTensor n}
    {ξ : E → Euclidean n} (hQ : ∀ i j a, ContDiffOn ℝ m (fun z ↦ Q z i j a) s)
    (hξ : ContDiffOn ℝ m ξ s) (i j : Fin n) :
    ContDiffOn ℝ m (fun z ↦ reducedSymbol (Q z) (ξ z) i j) s := by
  unfold reducedSymbol
  exact ContDiffOn.sum fun a _ ↦ (hQ i j a).mul ((contDiffOn_piLp 2).mp hξ a)

/-- Joint regularity of the selected right nullvector in `app:ch_waves:thm:leading`. -/
theorem contDiffOn_rightNullvector_reducedSymbol {Q : E → Fin n → MetricTensor n}
    {ξ : E → Euclidean n} (hQ : ∀ i j a, ContDiffOn ℝ m (fun z ↦ Q z i j a) s)
    (hξ : ContDiffOn ℝ m ξ s) (c : Fin n) :
    ContDiffOn ℝ m (fun z ↦ rightNullvector (reducedSymbol (Q z) (ξ z)) c) s :=
  contDiffOn_rightNullvector (contDiffOn_reducedSymbol_entry hQ hξ) c

/-- Joint regularity of the selected left nullvector in `app:ch_waves:thm:leading`. -/
theorem contDiffOn_leftNullvector_reducedSymbol {Q : E → Fin n → MetricTensor n}
    {ξ : E → Euclidean n} (hQ : ∀ i j a, ContDiffOn ℝ m (fun z ↦ Q z i j a) s)
    (hξ : ContDiffOn ℝ m ξ s) (r : Fin n) :
    ContDiffOn ℝ m (fun z ↦ leftNullvector (reducedSymbol (Q z) (ξ z)) r) s :=
  contDiffOn_leftNullvector (contDiffOn_reducedSymbol_entry hQ hξ) r

/-- Smoothness of the actual principal contraction (`app:ch_waves:thm:leading`). -/
theorem contDiffOn_transportField {Q : E → Fin n → MetricTensor n}
    {l k : E → Fin n → ℝ} (hQ : ∀ i j a, ContDiffOn ℝ m (fun z ↦ Q z i j a) s)
    (hl : ContDiffOn ℝ m l s) (hk : ContDiffOn ℝ m k s) (a : Fin n) :
    ContDiffOn ℝ m (fun z ↦ transportField (Q z) (l z) (k z) a) s := by
  simp only [transportField, principalCoefficient, Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun i _ ↦ (contDiffOn_pi.mp hl i).mul
    (ContDiffOn.sum fun j _ ↦ (hQ i a j).mul (contDiffOn_pi.mp hk j))

/-- The time-normalized principal coefficient of `app:ch_waves:thm:leading`,
using precisely the published fixed-column and fixed-row choices. -/
def normalizedPrincipalCoefficient (Q : Fin n → MetricTensor n) (ξ : Euclidean n)
    (r c t a : Fin n) : ℝ :=
  transportField Q (leftNullvector (reducedSymbol Q ξ) r)
      (rightNullvector (reducedSymbol Q ξ) c) a /
    transportField Q (leftNullvector (reducedSymbol Q ξ) r)
      (rightNullvector (reducedSymbol Q ξ) c) t

/-- The two actual-carrier gaps give both the time denominator gap and its
reciprocal bound (`app:ch_waves:thm:leading`). -/
theorem transportField_time_bounds (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : ActualCarriers.determinant Q ξ = 0) {r c t : Fin n}
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hminor : δ ≤ |(ActualCarriers.pencil Q ξ).adjugate r c|)
    (hroot : ε ≤ |partialDeriv (ActualCarriers.determinant Q) ξ t|) :
    let V := transportField Q (leftNullvector (reducedSymbol Q ξ) r)
      (rightNullvector (reducedSymbol Q ξ) c)
    δ * ε ≤ |V t| ∧ V t ≠ 0 ∧ |(V t)⁻¹| ≤ (δ * ε)⁻¹ := by
  refine ⟨transportField_time_gap Q hQ ξ hchar hδ hε.le hminor hroot,
    transportField_time_ne_zero Q hQ ξ hchar
      (abs_pos.mp (hδ.trans_le hminor)) (abs_pos.mp (hε.trans_le hroot)), ?_⟩
  apply transportCoefficient_inverse_bound hchar hδ hε hminor
  change ε ≤ |fderiv ℝ Matrix.det (reducedSymbol Q ξ) (principalCoefficient Q t)|
  rwa [← partialDeriv_reducedDeterminant Q hQ]

/-- Normalization cancels the fixed minor and gives the derivatives of the
actual-carrier determinant, with its literal convention (`app:ch_waves:thm:leading`). -/
theorem normalizedPrincipalCoefficient_eq_determinant_ratio
    (Q : Fin n → MetricTensor n) (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : ActualCarriers.determinant Q ξ = 0) {r c : Fin n}
    (hminor : (ActualCarriers.pencil Q ξ).adjugate r c ≠ 0) (t a : Fin n) :
    normalizedPrincipalCoefficient Q ξ r c t a =
      partialDeriv (ActualCarriers.determinant Q) ξ a /
        partialDeriv (ActualCarriers.determinant Q) ξ t :=
  transportField_ratio Q hQ ξ hchar hminor a t

/-- On the actual characteristic patch the selected smooth row and column
are nonzero nullvectors (`app:ch_waves:thm:leading`). -/
theorem selected_nullvectors_of_actual_gaps (Q : Fin n → MetricTensor n)
    (ξ : Euclidean n) (hchar : ActualCarriers.determinant Q ξ = 0)
    {r c : Fin n} {δ : ℝ} (hδ : 0 < δ)
    (hminor : δ ≤ |(ActualCarriers.pencil Q ξ).adjugate r c|) :
    let A := reducedSymbol Q ξ
    A *ᵥ rightNullvector A c = 0 ∧ leftNullvector A r ᵥ* A = 0 ∧
      rightNullvector A c ≠ 0 ∧ leftNullvector A r ≠ 0 := by
  have hm := abs_pos.mp (hδ.trans_le hminor)
  exact ⟨mulVec_rightNullvector hchar c, leftNullvector_vecMul hchar r,
    rightNullvector_ne_zero hm, leftNullvector_ne_zero hm⟩

/-- Joint smoothness of the normalized principal coefficients follows from
the characteristic equation and the two gaps (`app:ch_waves:thm:leading`). -/
theorem contDiffOn_normalizedPrincipalCoefficient {Q : E → Fin n → MetricTensor n}
    {ξ : E → Euclidean n} (hQ : ∀ i j a, ContDiffOn ℝ m (fun z ↦ Q z i j a) s)
    (hξ : ContDiffOn ℝ m ξ s) (hsymm : ∀ z ∈ s, ∀ i, (Q z i).IsSymm)
    (hchar : ∀ z ∈ s, ActualCarriers.determinant (Q z) (ξ z) = 0)
    {r c t : Fin n} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hminor : ∀ z ∈ s, δ ≤ |(ActualCarriers.pencil (Q z) (ξ z)).adjugate r c|)
    (hroot : ∀ z ∈ s, ε ≤ |partialDeriv (ActualCarriers.determinant (Q z)) (ξ z) t|)
    (a : Fin n) :
    ContDiffOn ℝ m (fun z ↦ normalizedPrincipalCoefficient (Q z) (ξ z) r c t a) s := by
  have hl := contDiffOn_leftNullvector_reducedSymbol hQ hξ r
  have hk := contDiffOn_rightNullvector_reducedSymbol hQ hξ c
  exact (contDiffOn_transportField hQ hl hk a).div
    (contDiffOn_transportField hQ hl hk t) fun z hz ↦
      (transportField_time_bounds (Q z) (hsymm z hz) (ξ z) (hchar z hz)
        hδ hε (hminor z hz) (hroot z hz)).2.1

/-- The normalized time component is one, as required for the scalar evolution
in `app:ch_waves:thm:leading`. -/
theorem normalizedPrincipalCoefficient_time (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : ActualCarriers.determinant Q ξ = 0) {r c t : Fin n}
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hminor : δ ≤ |(ActualCarriers.pencil Q ξ).adjugate r c|)
    (hroot : ε ≤ |partialDeriv (ActualCarriers.determinant Q) ξ t|) :
    normalizedPrincipalCoefficient Q ξ r c t t = 1 :=
  div_self (transportField_time_bounds Q hQ ξ hchar hδ hε hminor hroot).2.1

/-- The actual normalized zeroth-order coefficient `lᵀ P_G k / V_t` from
`app:ch_waves:thm:leading`. Physical derivatives hold the second parameter fixed;
the right nullvector is viewed in the shared Euclidean space for `P_G`. -/
def normalizedZerothCoefficient (F : Euclidean n × E → Euclidean N)
    (Q : Euclidean n × E → Fin n → MetricTensor n)
    (ξ : Euclidean n × E → Euclidean n) (r c t : Fin n) (p : Euclidean n × E) : ℝ :=
  (leftNullvector (reducedSymbol (Q p) (ξ p)) r ⬝ᵥ
    reducedOperator (fun x ↦ F (x, p.2)) (fun x ↦ Q (x, p.2))
      (fun x ↦ WithLp.toLp 2
        (rightNullvector (reducedSymbol (Q (x, p.2)) (ξ (x, p.2))) c)) p.1) /
    transportField (Q p) (leftNullvector (reducedSymbol (Q p) (ξ p)) r)
      (rightNullvector (reducedSymbol (Q p) (ξ p)) c) t

/-- Joint smoothness of the entire normalized zeroth-order coefficient,
including all Christoffel terms (`app:ch_waves:thm:leading`). The assumptions
are smooth geometric fields, immersion, characteristicity and the two gaps;
regularity of the connection, `P_G k`, and the denominator are derived. -/
theorem contDiffOn_normalizedZerothCoefficient
    {s : Set (Euclidean n × E)} {F : Euclidean n × E → Euclidean N}
    {Q : Euclidean n × E → Fin n → MetricTensor n}
    {ξ : Euclidean n × E → Euclidean n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : ∀ p ∈ s, Function.Injective (fderiv ℝ (fun x ↦ F (x, p.2)) p.1))
    (hQ : ∀ i j a, ContDiffOn ℝ ∞ (fun p ↦ Q p i j a) s)
    (hξ : ContDiffOn ℝ ∞ ξ s) (hsymm : ∀ p ∈ s, ∀ i, (Q p i).IsSymm)
    (hchar : ∀ p ∈ s, ActualCarriers.determinant (Q p) (ξ p) = 0)
    {r c t : Fin n} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hminor : ∀ p ∈ s, δ ≤ |(ActualCarriers.pencil (Q p) (ξ p)).adjugate r c|)
    (hroot : ∀ p ∈ s, ε ≤ |partialDeriv (ActualCarriers.determinant (Q p)) (ξ p) t|) :
    ContDiffOn ℝ ∞ (normalizedZerothCoefficient F Q ξ r c t) s := by
  have hl := contDiffOn_leftNullvector_reducedSymbol hQ hξ r
  have hk := contDiffOn_rightNullvector_reducedSymbol hQ hξ c
  have hke : ContDiffOn ℝ ∞ (fun p ↦ WithLp.toLp 2
      (rightNullvector (reducedSymbol (Q p) (ξ p)) c)) s :=
    (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp hk)
  unfold normalizedZerothCoefficient
  apply ContDiffOn.div
  · simp only [dotProduct]
    exact ContDiffOn.sum fun i _ ↦ (contDiffOn_pi.mp hl i).mul
      (contDiffOn_reducedOperator_joint hs hF himm hQ hke i)
  · exact contDiffOn_transportField hQ hl hk t
  · intro p hp
    exact (transportField_time_bounds (Q p) (hsymm p hp) (ξ p) (hchar p hp)
      hδ hε (hminor p hp) (hroot p hp)).2.1

end JanetCartan.NullTransport
