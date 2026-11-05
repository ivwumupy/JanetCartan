module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.ReverseIntegratedJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.CompactSobolev

/-!
# Sobolev bounds for the literal compact-frequency low-envelope graphs

The compact-frequency conclusion of `app:ch_response:thm:response-literal-transfer`.
The full amplitude's primitive grades produce the kernel bounds and all output
coordinate bounds. Sobolev membership is a conclusion. The exponent `b+s+n`
is independent of the accuracy order; no projection is inserted in the graph.
The producers `jc-finite-fio-calculus` and `jc-compatible-phase-geometry` must
supply the explicit amplitude and phase hypotheses. The consumer
`jc-response-complement` instantiates them for the paper's actual factors.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison AmplitudeBound JanetCartan.Localization Pseudodifferential
variable {n r : ℕ}

/-- Constant for each output coordinate jet in the complete-complement estimate
of `app:ch_response:thm:response-literal-transfer`, including both physical
Fourier normalization factors. It is independent of `a`, `L`, `ρ`, `Λ`, and `b`. -/
def lowEnvelopeCoordinateConstant (n r : ℕ) (K : Set (Euclidean n))
    (c G : ℝ) (Q P : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (j q : ℕ) : ℝ :=
  ‖((2 * Real.pi) ^ n : ℂ)⁻¹‖ *
    ((r : ℝ) * lowEnvelopeJetConstant n c G Q P C j q *
      volume.real K * lowEnvelopeRadialMass n) *
    (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
      (2 * Real.pi) ^ (-(n : ℝ) / 2))

/-- Uniform Sobolev constant for `app:ch_response:thm:response-literal-transfer`.
The original source and target supports are retained, and the frequency support
of a compact regularization does not enter this constant. -/
def lowEnvelopeSobolevConstant (n r : ℕ) (Ks Kt : Set (Euclidean n))
    (c G : ℝ) (Q P : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (s q : ℕ) : ℝ :=
  compactCoordinateSobolevConstant n s * Real.sqrt (volume.real Kt) *
    ∑ j ∈ Finset.range (s + 1), lowEnvelopeCoordinateConstant n r Ks c G Q P C j q

private theorem coordinateConstant_nonneg (K : Set (Euclidean n))
    (c G : ℝ) (Q P : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hC : ∀ j k, 0 ≤ C j k) (j q : ℕ) :
    0 ≤ lowEnvelopeCoordinateConstant n r K c G Q P C j q := by
  have := lowEnvelopeJetConstant_nonneg c G Q P C hP hC n j q
  have := lowEnvelopeRadialMass_nonneg n
  unfold lowEnvelopeCoordinateConstant
  positivity

private theorem coordinate_of_integral_bound
    (K : Set (Euclidean n)) (c G : ℝ) (Q P : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (j q b : ℕ) (a ρ L Λ : ℝ) (f : Lp (α := Euclidean n)
      (EuclideanSpace ℂ (Fin r)) 2 volume) (v : Fin r → ℂ)
    (hv : ‖v‖ ≤ ((r : ℝ) * lowEnvelopeJetConstant n c G Q P C j q *
      volume.real K * lowEnvelopeRadialMass n) * a * ρ ^ (b + j + n) *
      (L / ρ) ^ q * (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
        Λ ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖))) (i : Fin r) :
    ‖((2 * Real.pi) ^ n : ℂ)⁻¹ * v i‖ ≤
      lowEnvelopeCoordinateConstant n r K c G Q P C j q *
        a * ρ ^ (b + j + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖ := by
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left ((norm_le_pi_norm v i).trans hv) (norm_nonneg _)).trans_eq
  unfold lowEnvelopeCoordinateConstant
  ring

private theorem compact_sobolev_of_graded_coordinates
    (s q b : ℕ) (u : Euclidean n → Fin r → ℂ) (hu : ContDiff ℝ ∞ u)
    {Ks Kt : Set (Euclidean n)} (hKt : IsCompact Kt) (hs : tsupport u ⊆ Kt)
    (c G : ℝ) (Q P : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hC : ∀ j k, 0 ≤ C j k)
    {a ρ L Λ : ℝ} (ha : 0 ≤ a) (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ)
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hb : ∀ i (α : List (Fin n)), α.length ≤ s → ∀ x,
      ‖euclideanCoordinateDerivList α (fun z ↦ u z i) x‖ ≤
        lowEnvelopeCoordinateConstant n r Ks c G Q P C α.length q *
          a * ρ ^ (b + α.length + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖) :
    ∃ hu₂ : ∀ i : Fin r, MemLp (fun x ↦ u x i) 2 volume,
      (∀ i, MemFourierSobolev (s : ℝ) ((hu₂ i).toLp (fun x ↦ u x i))) ∧
      (∀ i, fourierSobolevNorm (s : ℝ) ((hu₂ i).toLp (fun x ↦ u x i)) ≤
        lowEnvelopeSobolevConstant n r Ks Kt c G Q P C s q *
          a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖) := by
  let D := ∑ j ∈ Finset.range (s + 1), lowEnvelopeCoordinateConstant n r Ks c G Q P C j q
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ coordinateConstant_nonneg Ks c G Q P C hP hC j q
  let B := D * a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (i : Fin r) (α : List (Fin n)) (hα : α.length ≤ s) (x : Euclidean n) :
      ‖euclideanCoordinateDerivList α (fun z ↦ u z i) x‖ ≤ B := by
    have hsum : lowEnvelopeCoordinateConstant n r Ks c G Q P C α.length q ≤ D :=
      Finset.single_le_sum (fun j _ ↦ coordinateConstant_nonneg Ks c G Q P C hP hC j q)
        (Finset.mem_range.mpr (by omega))
    have hp : ρ ^ (b + α.length + n) ≤ ρ ^ (b + s + n) :=
      pow_le_pow_right₀ hρ (by omega)
    exact (hb i α hα x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right hsum ha) hp (by positivity) (by positivity))
        (Real.rpow_nonneg hΛ _)) (by positivity)) (norm_nonneg f))
  have hs' (i : Fin r) : Function.support (fun x ↦ u x i) ⊆ Kt := by
    intro x hx
    apply hs
    apply subset_closure
    intro hz
    exact hx (by simp [hz])
  choose hm hmem hnorm using fun i ↦ exists_compactCoordinateSobolev s
    (fun x ↦ u x i) (contDiff_pi.mp hu i) hKt (hs' i) hB (hbound i)
  refine ⟨hm, hmem, fun i ↦ (hnorm i).trans_eq ?_⟩
  dsimp [B, D, lowEnvelopeSobolevConstant]
  ring

/-- The complete forward complement satisfies the low-envelope Sobolev bound
in `app:ch_response:thm:response-literal-transfer`. Primitive smooth full-amplitude
and phase grades are the analytic inputs. The forward gap follows from the
selector plateau. The conclusion is about the actual graph with low-support L²
data, and includes Sobolev membership; physical L¹ data are not required. -/
theorem forwardComplement_lowSupport_sobolev
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (χ : Euclidean n → ℂ) (ζ : Euclidean n)
    (s q b : ℕ) (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ) (hΛρ : Λ ≤ c * ρ / 2)
    (hζ : ‖ζ‖ ≤ Z) (hχ : ∀ δ, ‖δ‖ < c * ρ → χ δ = 1)
    (hSc : Continuous (fun p : Euclidean n × Euclidean n ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      complementaryAmplitude A ζ ρ χ p.1.1 p.1.2 p.2))
    {K Kt Kη : Set (Euclidean n)} (hK : IsCompact K)
    (hKt : IsCompact Kt) (hKη : IsCompact Kη)
    (ht : ∀ x y η, x ∉ Kt → complementaryAmplitude A ζ ρ χ x y η = 0)
    (hf : ∀ x y η, η ∉ Kη → complementaryAmplitude A ζ ρ χ x y η = 0)
    (hs : ∀ η z y, y ∉ K → complementaryAmplitude A ζ ρ χ z y η = 0)
    (hAj : ∀ η (β : List (Fin n)) k z y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude A ζ ρ χ v w η) z) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ S w η) z‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j φ z‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ∃ hu₂ : ∀ i : Fin r, MemLp (fun x ↦ forwardDemodulatedGraph S φ
        (complementaryAmplitude A ζ ρ χ) ζ ρ (fun y ↦ ⇑(f y)) x i) 2 volume,
      (∀ i, MemFourierSobolev (s : ℝ) ((hu₂ i).toLp (fun x ↦
        forwardDemodulatedGraph S φ (complementaryAmplitude A ζ ρ χ) ζ ρ
          (fun y ↦ ⇑(f y)) x i))) ∧
      (∀ i, fourierSobolevNorm (s : ℝ) ((hu₂ i).toLp (fun x ↦
        forwardDemodulatedGraph S φ (complementaryAmplitude A ζ ρ χ) ζ ρ
          (fun y ↦ ⇑(f y)) x i)) ≤
        lowEnvelopeSobolevConstant n r K Kt (forwardGapConstant c Z)
          (1 + Z + c / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C s q *
          a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hρ : 0 ≤ ρ := hL0.trans hLρ
  obtain ⟨hu, hj, _⟩ := forwardDemodulatedGraph_lowSupport_frequencyJets
    S φ (complementaryAmplitude A ζ ρ χ) ζ hρ hL0 ha b hSc hS hφ hA hK hKη
    (fun x y η ↦ hs η x y) hf C PS Pφ hC hPS hPφ hAj hSj hφj f hΛ hfs
  apply compact_sobolev_of_graded_coordinates s q b _ hu hKt
    (tsupport_forwardDemodulatedGraph_subset S φ (complementaryAmplitude A ζ ρ χ)
      ζ ρ _ hKt.isClosed ht) (forwardGapConstant c Z) (1 + Z + c / 2)
    (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C (fun j ↦ add_nonneg (hPS j) (hPφ j)) hC
    ha (hL.trans hLρ) hL0 hΛ f
  intro i α _ x
  rw [hj α x i]
  apply coordinate_of_integral_bound
  exact norm_forwardComplement_outputJetIntegral_le S φ A χ ζ x α q b C PS Pφ
    hC hPS hPφ hc ha hL hLρ hΛ hΛρ hζ hχ hS hφ
    (fun η ↦ hA.comp (contDiff_id.prodMk contDiff_const)) hK hs hAj hSj hφj f hfs

/-- The complete reverse graph satisfies the low-envelope Sobolev estimate
in `app:ch_response:thm:response-literal-transfer`, from the full inverse-chart
gap and primitive amplitude/phase grades. The amplitude can be the literal
`reverseFullAmplitude`, with all cutoffs, or its complete complement. The
constant is uniform in the compact frequency support of regularizations. -/
theorem reverse_lowSupport_sobolev
    {Ω K : Set (Euclidean n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (s q b : ℕ)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ)
    (hζ : ‖ζ‖ ≤ Z) (hΛρ : Λ ≤ c * ρ / 2)
    (hSc : Continuous (fun p : Euclidean n × Euclidean n ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Kt Kη : Set (Euclidean n)} (hKt : IsCompact Kt) (hKη : IsCompact Kη)
    (ht : ∀ y x η, y ∉ Kt → A y x η = 0)
    (hf : ∀ y x η, η ∉ Kη → A y x η = 0)
    (hs : ∀ η z x, x ∉ K → A z x η = 0)
    (hgap : ∀ η, (∃ z x, A z x η ≠ 0) → ∀ x ∈ Ω,
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x‖)
    (hAj : ∀ η (β : List (Fin n)) k z x,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A v w η) z) x‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ∃ hu₂ : ∀ i : Fin r, MemLp (fun y ↦
        reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x)) y i) 2 volume,
      (∀ i, MemFourierSobolev (s : ℝ) ((hu₂ i).toLp (fun y ↦
        reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x)) y i))) ∧
      (∀ i, fourierSobolevNorm (s : ℝ) ((hu₂ i).toLp (fun y ↦
        reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x)) y i)) ≤
        lowEnvelopeSobolevConstant n r K Kt (c / 2) (PS 1 + Pφ 1 + c / 2)
          (fun j ↦ PS (j + 1) + Pφ (j + 1)) (fun _ ↦ 1 + Z) C s q *
          a * ρ ^ (b + s + n) * Λ ^ ((n : ℝ) / 2) * (L / ρ) ^ q * ‖f‖) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hρ : 0 ≤ ρ := hL0.trans hLρ
  obtain ⟨hu, hj, _⟩ := reverseDemodulatedGraph_lowSupport_frequencyJets
    S φ A ζ hρ hL0 ha b hSc hS hφ hA hK hKη
    (fun y x η ↦ hs η y x) hf C hC hAj f hΛ hfs
  apply compact_sobolev_of_graded_coordinates s q b _ hu hKt
    (tsupport_reverseDemodulatedGraph_subset S φ A ζ ρ _ hKt.isClosed ht)
    (c / 2) (PS 1 + Pφ 1 + c / 2)
    (fun j ↦ PS (j + 1) + Pφ (j + 1)) (fun _ ↦ 1 + Z) C
    (fun _ ↦ add_nonneg zero_le_one ((norm_nonneg ζ).trans hζ)) hC
    ha (hL.trans hLρ) hL0 hΛ f
  intro i α _ y
  rw [hj α y i]
  apply coordinate_of_integral_bound
  exact norm_reverse_outputJetIntegral_le hΩ hK hKΩ S φ A ζ y α q b C PS Pφ
    hC hPS hPφ hc ha hL hLρ hΛ hζ hΛρ hS hφ
    (fun η ↦ hA.comp (contDiff_id.prodMk contDiff_const)) hs hgap hAj hSj hφj f hfs

/-- The reverse amplitude used in the low-envelope estimate is exactly the
literal weighted inverse from `app:ch_regular_base:eq:actual-matrix-inverse`.
This identity retains the Jacobian, matrix order, and all three cutoffs. -/
theorem reverseDemodulatedGraph_reverseFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (f : Euclidean n → Fin r → ℂ) (y : Euclidean n) :
    reverseDemodulatedGraph S φ (reverseFullAmplitude S U χs χt χg) ζ ρ f y =
      carrier (-ρ) (fun z ↦ inner ℝ z ζ) y •
        weightedReverseGraph S U χs χt χg (fun x ↦ carrier ρ φ x • f x) y := by
  exact congrArg (fun v ↦ carrier (-ρ) (fun z ↦ inner ℝ z ζ) y • v)
    (ReverseDerivative.reverseGraph_literalAmplitude S U χs χt χg _ y)

end JanetCartan.ResponseTransfer.LowEnvelope
