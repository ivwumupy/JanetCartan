module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.ParameterAssembly.Profile

/-!
# Compact-parameter Sobolev assembly

Conditional deduction of the joint estimate in
`app:ch_response:eq:direct-envelope-profile` from the literal first derivative
identities and the uniform low theorem. The results hold at every point of the
open parameter domain, hence uniformly on any compact box it contains.
The parent must construct the mixed datum jets from the paper's smooth family;
that conversion and the analytic transfer producers are not asserted here.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier.ParameterAssembly

variable {d m : ℕ} {X E ι Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Actual ordered parameter derivatives, spatial Sobolev membership and the
weighted finite sum estimate for `app:ch_response:eq:direct-envelope-profile`.
Only primitive orders through `c+s+q` and datum derivative identities below `q`
are required. The constant precedes all scale and realization choices. -/
theorem exists_ordered_sobolev_constant
    (v : Fin m → X) (qs : Fin m → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin m → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin m → Fin d → ι)
    (sv : Fin d → X) (sq : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (sB : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (si : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : ℕ) (is : List (Fin m)) (e : AmplitudeExpression X E ι) (he : e.derivativeCost = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + s + is.length → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (U : Set Y), IsOpen U → ∀ (w : Fin m → Y),
      ∀ (T : Y → (X → E) → L2 →L[ℂ] L2) (P : (X → E) → Prop) (t : Y), t ∈ U →
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T t b‖ ≤ C₀ * A) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (sv i) (sq i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (sB i j) (si i j)).evaluate a)) →
      HasSpatialAmplitudeTransfer sv sq sB si a (T t) P →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a)) →
      HasParameterAmplitudeTransfer U w v qs B idx a T P →
      P (e.evaluate a) →
      ∀ (F : List (Fin m ⊕ Fin d) → Y → L2),
      HasMixedDatumJets U w is.length F →
      (∀ z', z'.length ≤ is.length → MemFourierSobolev (s : ℝ) (F z' t)) →
      MemFourierSobolev (s : ℝ) (orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
          (fun t => T t (e.evaluate a) (F [] t)) t) ∧
        fourierSobolevNorm (s : ℝ) (orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
          (fun t => T t (e.evaluate a) (F [] t)) t) ≤
          C * profile s L F is [] t := by
  obtain ⟨C, hC, hb⟩ := exists_value_constant (Y := Y) v qs B idx sv sq sB si M hM
    c R hR C₀ hC₀ s is e
  refine ⟨C, hC, ?_⟩
  intro L hL a ha hj U hU w T P t ht hl hsr hsc hs hpr hpc hp heP F hF hmem
  rw [orderedLineDeriv_eq_value hU hF hp hpr hpc is e [] (by simp) heP t ht]
  simpa only [he, pow_zero, one_mul] using hb L hL a ha (by simpa [he] using hj)
    T P t hl hsr hsc hs hpr hpc heP F [] (by simpa using hmem)

/-- The joint `K^(s+q)` bound of
`app:ch_response:eq:direct-envelope-profile` for actual parameter derivatives.
The only additional assumptions are finite mixed **datum** Sobolev profiles.
Their construction from pure parameter profiles remains with the parent task.
The finite datum constant is chosen before `L`, `K`, `A₀`, frequency-indexed
realizations, primitive fields, parameter points, and data. -/
theorem exists_ordered_K_constant
    (v : Fin m → X) (qs : Fin m → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin m → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin m → Fin d → ι)
    (sv : Fin d → X) (sq : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (sB : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (si : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : ℕ) (is : List (Fin m)) (e : AmplitudeExpression X E ι) (he : e.derivativeCost = 0)
    (D : ℕ → List (Fin m ⊕ Fin d) → ℝ) (hD : ∀ p z, 0 ≤ D p z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L K A₀ : ℝ), 1 ≤ L → L ≤ K → 0 ≤ A₀ →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + s + is.length → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (U : Set Y), IsOpen U → ∀ (w : Fin m → Y),
      ∀ (T : Y → (X → E) → L2 →L[ℂ] L2) (P : (X → E) → Prop) (t : Y), t ∈ U →
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T t b‖ ≤ C₀ * A) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (sv i) (sq i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (sB i j) (si i j)).evaluate a)) →
      HasSpatialAmplitudeTransfer sv sq sB si a (T t) P →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a)) →
      HasParameterAmplitudeTransfer U w v qs B idx a T P →
      P (e.evaluate a) →
      ∀ (F : List (Fin m ⊕ Fin d) → Y → L2),
      HasMixedDatumJets U w is.length F →
      (∀ z', z'.length ≤ is.length → MemFourierSobolev (s : ℝ) (F z' t)) →
      (∀ z, z.length ≤ is.length → ∀ p, p ≤ s →
        fourierSobolevNorm (p : ℝ) (F z t) ≤ A₀ * D p z * K ^ (p + z.length)) →
      MemFourierSobolev (s : ℝ) (orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
          (fun t => T t (e.evaluate a) (F [] t)) t) ∧
        fourierSobolevNorm (s : ℝ) (orderedTransferAction (fun i f t => lineDeriv ℝ f t (w i)) is.reverse
          (fun t => T t (e.evaluate a) (F [] t)) t) ≤
          C * A₀ * K ^ (s + is.length) := by
  obtain ⟨C, hC, hb⟩ := exists_ordered_sobolev_constant (Y := Y) v qs B idx sv sq sB si
    M hM c R hR C₀ hC₀ s is e he
  refine ⟨C * profileCoefficient s D is [], mul_nonneg hC
    (profileCoefficient_nonneg s D hD is []), ?_⟩
  intro L K A₀ hL hLK hA a ha hj U hU w T P t ht hl hsr hsc hs hpr hpc hp heP F hF hmem hnorm
  have hout := hb L hL a ha hj U hU w T P t ht hl hsr hsc hs hpr hpc hp heP F hF hmem
  refine ⟨hout.1, hout.2.trans ?_⟩
  have hprof := profile_le_K s D hD hL hLK hA F is [] t (by simpa using hnorm)
  have h := mul_le_mul_of_nonneg_left hprof hC
  simpa only [List.length_nil, Nat.add_zero, mul_assoc, mul_left_comm, mul_comm] using h

end JanetCartan.IsometricEmbedding.Response.NearCarrier.ParameterAssembly
