module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.SourceCoordinates

/-!
# Original supports of the output jets

The compact source and frequency sets used for dominated frequency
differentiation in `app:ch_response:thm:response-literal-transfer` are the
original amplitude's sets. Differentiation also preserves its target support.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison JanetCartan.Localization
variable {n r : ℕ}

/-- Target coordinate differentiation does not enlarge matrix support, for
the compact low-envelope graph in `app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_normalMatrixDerivList_subset
    (g : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (α : List (Fin n)) :
    tsupport (normalMatrixDerivList α g) ⊆ tsupport g := by
  induction α with
  | nil => exact Set.Subset.rfl
  | cons i α ih =>
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

/-- The full output-jet amplitude retains its original target support in
`app:ch_response:thm:response-literal-transfer`. No frequency smoothness of
the phase is used in this support statement. -/
theorem tsupport_outputJetAmplitude_target_subset
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) (y η : Euclidean n) :
    tsupport (fun x ↦ outputJetAmplitude τ α A x y η) ⊆
      tsupport (fun x ↦ A x y η) := by
  exact (tsupport_smul_subset_right _ _).trans
    ((tsupport_normalMatrixDerivList_subset _ α).trans (tsupport_smul_subset_right _ _))

/-- A frequency slice which is absent from the original full amplitude is
absent from every target jet (`app:ch_response:thm:response-literal-transfer`).
This supplies the fixed frequency carrier in the dominated integral proof. -/
theorem outputJetAmplitude_eq_zero_off_frequency
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) {K : Set (Euclidean n)}
    (hs : ∀ x y η, η ∉ K → A x y η = 0) (x y η : Euclidean n) (hη : η ∉ K) :
    outputJetAmplitude τ α A x y η = 0 := by
  have he : (fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η) = 0 := by
    funext z
    simp [hs z y η hη]
  simp [outputJetAmplitude, he, normalMatrixDerivList_zero]

/-- Every output jet has compact source-frequency support on the same original
sets. This is the fixed carrier for frequency differentiation in
`app:ch_response:thm:response-literal-transfer`, including the complete selector. -/
theorem hasCompactSupport_outputJetAmplitude_sourceFrequency
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) {Ks Kη : Set (Euclidean n)}
    (hKs : IsCompact Ks) (hKη : IsCompact Kη)
    (hsource : ∀ x y η, y ∉ Ks → A x y η = 0)
    (hfrequency : ∀ x y η, η ∉ Kη → A x y η = 0) (x : Euclidean n) :
    HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      outputJetAmplitude τ α A x p.2 p.1) := by
  apply HasCompactSupport.of_support_subset_isCompact (hKη.prod hKs)
  intro p hp
  constructor
  · by_contra hn
    exact hp (outputJetAmplitude_eq_zero_off_frequency τ α A hfrequency x p.2 p.1 hn)
  · by_contra hn
    exact hp (outputJetAmplitude_eq_zero_off_source τ α A hsource x p.2 p.1 hn)

end JanetCartan.ResponseTransfer.LowEnvelope
