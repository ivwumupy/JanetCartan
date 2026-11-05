module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.ParameterTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.TransferredSobolev

/-!
# Finite mixed datum jets and actual parameter derivatives

The finite parameter induction for `app:ch_response:eq:direct-envelope-profile`.
The datum interface contains only actual first derivative identities, locally on
an open parameter domain. Constructing these jets from the manuscript's smooth
family and pure parameter Sobolev profiles remains a consumer obligation.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open JanetCartan.Pseudodifferential
open scoped Topology

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier
namespace ParameterAssembly

variable {d m : ℕ} {X E ι Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Actual mixed datum derivatives through order `N`, for
`app:ch_response:eq:direct-envelope-profile`. The head of a word is the
outermost derivative; `inl` denotes a parameter derivative and `inr` a spatial
weak derivative. No output norm or operator estimate is asserted. -/
def HasMixedDatumJets (U : Set Y) (w : Fin m → Y) (N : ℕ)
    (F : List (Fin m ⊕ Fin d) → Y → L2) : Prop :=
  ∀ z, z.length < N → ∀ t ∈ U,
    (∀ i, HasLineDerivAt ℝ (F z) (F (.inl i :: z) t) t (w i)) ∧
    (∀ j, HasEuclideanL2CoordinateDerivative j (F z t) (F (.inr j :: z) t))

variable (v : Fin m → X) (qs : Fin m → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
  (B : Fin m → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin m → Fin d → ι)

/-- Finite application of the literal three-term parameter transfer identity in
`app:ch_response:eq:direct-envelope-profile`. The first listed parameter acts
first. The theorem `orderedLineDeriv_eq_value` identifies this expression with
actual ordered derivatives, without assuming any higher operator identities.
This recursion performs the analytic induction; it is not a new enumeration
of the existing spatial transfer branches. -/
def value (a : ι → X → E) (T : Y → (X → E) → L2 →L[ℂ] L2)
    (F : List (Fin m ⊕ Fin d) → Y → L2) :
    List (Fin m) → AmplitudeExpression X E ι → List (Fin m ⊕ Fin d) → Y → L2
  | [], e, z, t => T t (e.evaluate a) (F z t)
  | i :: is, e, z, t =>
      value a T F is (e.divergenceTransfer (v i) (qs i)) z t +
        ∑ j, value a T F is (e.coefficientProduct (B i j) (idx i j)) (.inr j :: z) t +
        value a T F is e (.inl i :: z) t

variable {v qs B idx}

/-- Differentiating the finite transfer expression really appends a parameter
derivative (`app:ch_response:eq:direct-envelope-profile`). Only datum identities
strictly below the indicated finite total order are used. -/
theorem hasLineDerivAt_value
    {U : Set Y} {w : Fin m → Y} {N : ℕ}
    {a : ι → X → E} {T : Y → (X → E) → L2 →L[ℂ] L2}
    {F : List (Fin m ⊕ Fin d) → Y → L2} {P : (X → E) → Prop}
    (hF : HasMixedDatumJets U w N F)
    (hT : HasParameterAmplitudeTransfer U w v qs B idx a T P)
    (hr : ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
      ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (hc : ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
      ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a))
    (is : List (Fin m)) (e : AmplitudeExpression X E ι)
    (z : List (Fin m ⊕ Fin d)) (horder : z.length + is.length < N)
    (he : P (e.evaluate a)) (i : Fin m) (t : Y) (ht : t ∈ U) :
    HasLineDerivAt ℝ (value v qs B idx a T F is e z)
      (value v qs B idx a T F (is ++ [i]) e z t) t (w i) := by
  induction is generalizing e z with
  | nil =>
    exact hT e he (F z) (fun j => F (.inr j :: z)) (F (.inl i :: z)) i t ht
      (hF z (by simpa using horder) t ht).2
      ((hF z (by simpa using horder) t ht).1 i)
  | cons j js ih =>
    have h₁ := ih (e.divergenceTransfer (v j) (qs j)) z (by simp_all; omega) (hr e he j)
    have h₂ (k : Fin d) := ih (e.coefficientProduct (B j k) (idx j k))
      (.inr k :: z) (by simp only [List.length_cons] at *; omega) (hc e he j k)
    have h₃ := ih e (.inl j :: z) (by simp only [List.length_cons] at *; omega) he
    unfold HasLineDerivAt at *
    convert (h₁.add (HasDerivAt.sum (u := Finset.univ) fun k _ => h₂ k)).add h₃ using 1
    · ext r
      simp [value, Finset.sum_apply]
    · rfl

/-- The output's genuine ordered directional derivative on the open domain in
`app:ch_response:eq:direct-envelope-profile`. `is.reverse` follows the existing
`orderedTransferAction` convention (outermost derivative listed first).
No extension of the parameter family outside `U` is required. -/
theorem orderedLineDeriv_eq_value
    {U : Set Y} (hU : IsOpen U) {w : Fin m → Y} {N : ℕ}
    {a : ι → X → E} {T : Y → (X → E) → L2 →L[ℂ] L2}
    {F : List (Fin m ⊕ Fin d) → Y → L2} {P : (X → E) → Prop}
    (hF : HasMixedDatumJets U w N F)
    (hT : HasParameterAmplitudeTransfer U w v qs B idx a T P)
    (hr : ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
      ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (hc : ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
      ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a))
    (is : List (Fin m)) (e : AmplitudeExpression X E ι)
    (z : List (Fin m ⊕ Fin d)) (horder : z.length + is.length ≤ N)
    (he : P (e.evaluate a)) (t : Y) (ht : t ∈ U) :
    orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
      (fun t => T t (e.evaluate a) (F z t)) t = value v qs B idx a T F is e z t := by
  induction is using List.reverseRecOn generalizing t with
  | nil => rfl
  | @append_singleton is i ih =>
    have hn : z.length + is.length < N := by
      simp only [List.length_append, List.length_singleton] at horder
      omega
    have heq : (orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
        (fun t => T t (e.evaluate a) (F z t))) =ᶠ[𝓝 t] value v qs B idx a T F is e z := by
      filter_upwards [hU.mem_nhds ht] with u hu
      exact ih (by omega) u hu
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      orderedTransferAction] using
      (heq.lineDeriv_eq (v := w i)).trans
        (hasLineDerivAt_value hF hT hr hc is e z hn he i t ht).lineDeriv

/-- Existence of each successive actual ordered parameter derivative in
`app:ch_response:eq:direct-envelope-profile`. This prevents the numerical
`lineDeriv` expression from relying on its default value at a nondifferentiable
point. Only the finite first-derivative datum interface is required. -/
theorem hasLineDerivAt_ordered
    {U : Set Y} (hU : IsOpen U) {w : Fin m → Y} {N : ℕ}
    {a : ι → X → E} {T : Y → (X → E) → L2 →L[ℂ] L2}
    {F : List (Fin m ⊕ Fin d) → Y → L2} {P : (X → E) → Prop}
    (hF : HasMixedDatumJets U w N F)
    (hT : HasParameterAmplitudeTransfer U w v qs B idx a T P)
    (hr : ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
      ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (hc : ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
      ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a))
    (is : List (Fin m)) (e : AmplitudeExpression X E ι)
    (z : List (Fin m ⊕ Fin d)) (horder : z.length + is.length < N)
    (he : P (e.evaluate a)) (i : Fin m) (t : Y) (ht : t ∈ U) :
    HasLineDerivAt ℝ
      (orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
        (fun t => T t (e.evaluate a) (F z t)))
      (value v qs B idx a T F (is ++ [i]) e z t) t (w i) := by
  apply (hasLineDerivAt_value hF hT hr hc is e z horder he i t ht).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds ht] with u hu
  exact orderedLineDeriv_eq_value hU hF hT hr hc is e z (by omega) he u hu

end ParameterAssembly
end JanetCartan.IsometricEmbedding.Response.NearCarrier
