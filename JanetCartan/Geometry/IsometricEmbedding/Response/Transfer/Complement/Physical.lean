module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Multiplier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorDecay
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Basic

/-!
# Physical and demodulated complete complements

Literal carrier multiplication on the SAME Euclidean vector L² space in
`app:ch_response:thm:response-literal-transfer`. The physical output is obtained
by undoing the demodulation in the graph estimates. A supplied fixed polynomial
Sobolev cost of carrier multiplication is absorbed by higher internal precision;
this is the fixed multiplier input of the finite calculus, not a decay premise.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace JanetCartan.ResponseTransfer.Complement
open FourierIntegral Pseudodifferential ArbitraryAccuracy
variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual unit-modulus physical carrier as a bounded multiplier, for
`app:ch_response:thm:response-literal-transfer`. -/
def carrierMask (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) : InactiveSource.BoundedMask n where
  symbol := carrier ρ φ
  measurable := (by unfold carrier; fun_prop : Continuous (carrier ρ φ)).stronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by simp [carrier, Complex.norm_exp]

/-- Actual bounded carrier multiplication on the original Euclidean vector
L² space (`app:ch_response:thm:response-literal-transfer`). -/
def carrierMultiplication (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) : H →L[ℂ] H := by
  let m := carrierMask ρ φ hφ
  let T : H →ₗ[ℂ] H := {
    toFun := m.multiply
    map_add' := fun u v ↦ by
      apply Lp.ext
      filter_upwards [m.multiply_ae (u + v), m.multiply_ae u, m.multiply_ae v,
        Lp.coeFn_add u v, Lp.coeFn_add (m.multiply u) (m.multiply v)] with x h h₁ h₂ h₃ h₄
      simp only [h, h₁, h₂, h₃, h₄, Pi.add_apply, smul_add]
    map_smul' := fun c v ↦ by
      apply Lp.ext
      filter_upwards [m.multiply_ae (c • v), m.multiply_ae v,
        Lp.coeFn_smul c v, Lp.coeFn_smul c (m.multiply v)] with x h h₁ h₂ h₃
      simp only [h, h₁, h₂, h₃, Pi.smul_apply, RingHom.id_apply]
      exact smul_comm _ _ _ }
  exact T.mkContinuous 1 (fun v ↦ m.norm_multiply_le v)

/-- The carrier operator has precisely the literal pointwise representative
(`app:ch_response:thm:response-literal-transfer`). -/
theorem carrierMultiplication_ae (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (v : H) :
    carrierMultiplication ρ φ hφ v =ᵐ[volume] fun x ↦ carrier ρ φ x • v x :=
  (carrierMask ρ φ hφ).multiply_ae v

/-- Demodulation inverts the physical carrier exactly on Euclidean L²,
without a support projection (`app:ch_response:eq:response-two-envelopes`). -/
theorem carrierMultiplication_neg_cancel (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (v : H) :
    carrierMultiplication (-ρ) φ hφ (carrierMultiplication ρ φ hφ v) = v := by
  apply Lp.ext
  filter_upwards [carrierMultiplication_ae (-ρ) φ hφ (carrierMultiplication ρ φ hφ v),
    carrierMultiplication_ae ρ φ hφ v] with x hx hv
  rw [hx, hv, smul_smul, carrier_neg_mul, one_smul]

/-- Undoing the forward demodulation gives the original literal graph on the
original modulated source, with all amplitude cutoffs intact.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem remodulate_forwardDemodulatedGraph
    (S : E → E → ℝ) (φ : E → ℝ) (A : FullAmplitude n r)
    (ζ : E) (ρ : ℝ) (f : E → Fin r → ℂ) (x : E) :
    carrier ρ φ x • LowEnvelope.forwardDemodulatedGraph S φ A ζ ρ f x =
      graphOperator S A (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • f y) x := by
  rw [LowEnvelope.forwardDemodulatedGraph, smul_smul, mul_comm,
    carrier_neg_mul, one_smul]

/-- Undoing reverse demodulation retains the literal weighted reverse graph,
not an unweighted-adjoint replacement.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem remodulate_reverseDemodulatedGraph
    (S : E → E → ℝ) (φ : E → ℝ) (A : FullAmplitude n r)
    (ζ : E) (ρ : ℝ) (f : E → Fin r → ℂ) (y : E) :
    carrier ρ (fun z ↦ inner ℝ z ζ) y • LowEnvelope.reverseDemodulatedGraph S φ A ζ ρ f y =
      ReverseDerivative.reverseGraph S A (fun x ↦ carrier ρ φ x • f x) y := by
  rw [LowEnvelope.reverseDemodulatedGraph, smul_smul, mul_comm,
    carrier_neg_mul, one_smul]

/-- The SAME literal regularization limit remains the physical output after
remodulation (`app:ch_response:thm:response-literal-transfer`). -/
theorem carrierMultiplication_tendsto (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    {u : ℕ → H} {v : H} (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun k ↦ carrierMultiplication ρ φ hφ (u k)) atTop
      (𝓝 (carrierMultiplication ρ φ hφ v)) :=
  ((carrierMultiplication ρ φ hφ).continuous.tendsto v).comp hu

/-- Simultaneous physical and demodulated bounds for a proved complementary
error. The graph theorems supply `hv`; the finite calculus supplies the fixed
carrier-multiplier cost `hcost`. The output is the actual carrier product and
its exact inverse, and the single constant precedes the family index.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem completeComplement_physical_and_demodulated
    (v : ι → H) (ρ a : ι → ℝ) (φ : ι → E → ℝ) (hφ : ∀ i, Continuous (φ i))
    (s : ℕ) (D d : ℝ) (hρ : ∀ i, 0 < ρ i) (ha : ∀ i, 0 ≤ a i) (hD : 0 ≤ D)
    (hv : RapidDecayAt vectorFourierSobolevScale s ρ a v)
    (hcost : ∀ i (w : H), MemVectorFourierSobolev (s : ℝ) w →
      MemVectorFourierSobolev (s : ℝ) (carrierMultiplication (ρ i) (φ i) (hφ i) w) ∧
      vectorFourierSobolevNorm (s : ℝ) (carrierMultiplication (ρ i) (φ i) (hφ i) w) ≤
        D * (ρ i) ^ d * vectorFourierSobolevNorm (s : ℝ) w) :
    ∀ Q : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      let physical := carrierMultiplication (ρ i) (φ i) (hφ i) (v i)
      let demodulated := carrierMultiplication (-ρ i) (φ i) (hφ i) physical
      MemVectorFourierSobolev (s : ℝ) physical ∧
      vectorFourierSobolevNorm (s : ℝ) physical ≤ C * a i * (ρ i) ^ (-Q) ∧
      MemVectorFourierSobolev (s : ℝ) demodulated ∧
      vectorFourierSobolevNorm (s : ℝ) demodulated ≤ C * a i * (ρ i) ^ (-Q) := by
  have hphysical := rapidDecayAt_polynomial_observation vectorFourierSobolevScale
    vectorFourierSobolevScale v (fun i ↦ carrierMultiplication (ρ i) (φ i) (hφ i) (v i))
    ρ a s s D d hρ hD hv (fun i hi ↦ by
      obtain ⟨hm, hb⟩ := hcost i _ hi
      exact ⟨hm, by simpa only [vectorFourierSobolevScale_gradeNorm s hm,
        vectorFourierSobolevScale_gradeNorm s hi] using hb⟩)
  intro Q
  obtain ⟨C₁, hC₁, hb₁⟩ := hphysical Q
  obtain ⟨C₂, hC₂, hb₂⟩ := hv Q
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro i
  dsimp only
  rw [carrierMultiplication_neg_cancel]
  refine ⟨(hb₁ i).1, ?_, (hb₂ i).1, ?_⟩
  · have h := (hb₁ i).2
    rw [vectorFourierSobolevScale_gradeNorm s (hb₁ i).1] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (ha i))
      (Real.rpow_nonneg (hρ i).le _))
  · have h := (hb₂ i).2
    rw [vectorFourierSobolevScale_gradeNorm s (hb₂ i).1] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (ha i))
      (Real.rpow_nonneg (hρ i).le _))

end JanetCartan.ResponseTransfer.Complement
