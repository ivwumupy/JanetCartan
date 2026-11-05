module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ResidualSmoothEnvelopes
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.SourceProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.CompactMultiplier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.DatumBridge
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Modulation

/-!
# Exact classes and parameter jets for finite measured words

The consumer is the finite-word input of
`complex_inverse_parameter_envelopes_of_actual_finite_words`, in
`app:ch_response:eq:response-graded-reduced`. These lemmas identify the actual
carrier-conjugated operators, sum their already proved ordered estimates, and
make the parameter-direction constants uniform. Smoothness follows from the
original supported source and compact phase; it is not an output assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles

open Pseudodifferential FourierIntegral ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.CompactTransfer
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
open FiniteResidualEnvelopes ObservedParameterRemainders

variable {d r : ℕ} {I J : Type*}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The actual modulated operators compose by cancelling the very same
intermediate carrier. No intermediate representative or operator is changed
(`app:ch_regular:lem:finite-chain`). -/
theorem demodulated_comp_apply_same_phase
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (T U : H →L[ℂ] H) (u : H) :
    demodulatedL2Operator lam φ hφ T (demodulatedL2Operator lam φ hφ U u) =
      demodulatedL2Operator lam φ hφ (T.comp U) u := by
  simp only [demodulatedL2Operator, ContinuousLinearMap.comp_apply]
  rw [show carrierMultiplication lam φ hφ
      (carrierMultiplication (-lam) φ hφ
        (U (carrierMultiplication lam φ hφ u))) =
      U (carrierMultiplication lam φ hφ u) from by
    simpa only [neg_neg] using carrierMultiplication_neg_cancel (-lam) φ hφ
      (U (carrierMultiplication lam φ hφ u))]

/-- A fixed bounded physical operator has a norm-smooth observed source
family for the original compactly supported joint amplitude and phase. This
supplies parameter calculus in the finite-word sum without assuming spatial
or parameter smoothness of the operator's output
(`app:ch_response:eq:response-two-envelopes`). -/
theorem contDiffOn_demodulated_supported_operator
    {V : Set Par} (hV : IsOpen V) {S X : Set E} (hS : IsCompact S) (hX : IsCompact X)
    (a : E × Par → F) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q, q.1 ∉ S → a q = 0)
    (lam : ℝ) (φ : Par → E → ℝ)
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hφs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (T : H →L[ℂ] H) :
    ContDiffOn ℝ ∞ (fun c ↦ demodulatedL2Operator lam (φ c)
      (hφ.continuous.comp (continuous_const.prodMk continuous_id)) T
      (graphTestToLp (vectorOriginalDatumTest a ha hS hs [] c))) V := by
  have hu : ContDiffOn ℝ ∞
      (fun c ↦ graphTestToLp (vectorOriginalDatumTest a ha hS hs [] c)) V :=
    contDiffOn_l2_of_supported_joint_representative hV hS a ha hs _
      (fun c _ ↦ by simpa only [originalDatumDerivative, orderedTransferAction] using
        vectorOriginalDatumTest_toLp_ae a ha hS hs [] c)
  have hmod := contDiffOn_demodulationOperators (r := r) hV hX (-lam) φ
    (fun _ ↦ hφ.continuous.comp (continuous_const.prodMk continuous_id))
    hφ.contDiffOn hφs
  have hdemod := contDiffOn_demodulationOperators (r := r) hV hX lam φ
    (fun _ ↦ hφ.continuous.comp (continuous_const.prodMk continuous_id))
    hφ.contDiffOn hφs
  have hphysical := (T.restrictScalars ℝ).contDiff.comp_contDiffOn (hmod.clm_apply hu)
  simpa only [neg_neg, demodulatedL2Operator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', Function.comp_apply] using hdemod.clm_apply hphysical

/-- A finite sum of actual smooth ordered words retains the identical
natural reserve. Only the constants are summed; no negative power is extracted
at low orders (`app:ch_regular:lem:finite-chain`). -/
theorem ordered_reserved_bounds_finite_sum [Fintype J]
    {V : Set Par} (hV : IsOpen V) (u : J → I → Par → H)
    (hu : ∀ j i, ContDiffOn ℝ ∞ (u j i) V)
    (A K : I → ℝ) (reserve : ℕ)
    (hbound : ∀ j (ps : List Par), (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (u j q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve)) :
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ ∑ j, u j q.1 c) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve) := by
  classical
  intro ps hps s
  choose C hC hest using fun j ↦ hbound j ps hps s
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro q value
  let jet := fun j ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (u j q.1) q.2
  have he : value = ∑ j, jet j := by
    dsimp only [value]
    rw [orderedParameterWord_eq_iteratedFDeriv hV
      (ContDiffOn.sum (s := Finset.univ) (fun j _ ↦ hu j q.1)) ps q.2.property]
    rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦
      ((hu j q.1).contDiffAt (hV.mem_nhds q.2.property)).of_le (by simp))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact (orderedParameterWord_eq_iteratedFDeriv hV (hu j q.1) ps q.2.property).symm
  obtain ⟨hm, hb⟩ := gradeNorm_sum_le vectorFourierSobolevScale Finset.univ jet s
    (fun j _ ↦ (hest j q).1)
  rw [he]
  refine ⟨hm, ?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hm] at hb
  calc
    vectorFourierSobolevNorm (s : ℝ) (∑ j, jet j)
        ≤ ∑ j, vectorFourierSobolevScale.gradeNorm s (jet j) := hb
    _ ≤ ∑ j, C j * A q.1 * K q.1 ^ (s+ps.length-reserve) := by
      apply Finset.sum_le_sum
      intro j _
      rw [vectorFourierSobolevScale_gradeNorm s (hest j q).1]
      exact (hest j q).2
    _ = (∑ j, C j) * A q.1 * K q.1 ^ (s+ps.length-reserve) := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Ordered estimates on the same smooth L² family give one constant for
all unit Fréchet directions. This is the precise parameter format of `hfinite`
in `complex_inverse_parameter_envelopes_of_actual_finite_words`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem uniform_jets_of_ordered_reserved_bounds
    {V : Set Par} (hV : IsOpen V) (u : I → Par → H)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) V) (A K : I → ℝ) (reserve : ℕ)
    (hbound : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (u q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve)) :
    ∀ s k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ l, ‖v l‖ ≤ 1) →
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k (u i) c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k (u i) c v) ≤
            C * A i * K i ^ (s+k-reserve) := by
  intro s k
  let D : I × V → ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Par) H :=
    fun q ↦ iteratedFDeriv ℝ k (u q.1) q.2
  have hD (v : Fin k → Par) (hv : ∀ l, ‖v l‖ ≤ 1) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        D q v ∈ vectorFourierSobolevScale.level s ∧
          vectorFourierSobolevScale.gradeNorm s (D q v) ≤
            C * (A q.1 * K q.1 ^ (s+k-reserve)) := by
    have hvlist : ∀ w ∈ List.ofFn v, ‖w‖ ≤ 1 := by
      intro w hw
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hw
      exact hv l
    obtain ⟨C, hC, hb⟩ := hbound (List.ofFn v) hvlist s
    refine ⟨C, hC, ?_⟩
    intro q
    have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) (List.ofFn v)
        (u q.1) q.2 = D q v := by
      rw [orderedParameterWord_eq_iteratedFDeriv hV (hu q.1) _ q.2.property]
      exact parameterListJet_ofFn (u q.1) k v q.2
    obtain ⟨hm, hest⟩ := hb q
    rw [he] at hm hest
    refine ⟨hm, ?_⟩
    rw [vectorFourierSobolevScale_gradeNorm s hm]
    simpa only [List.length_ofFn, mul_assoc] using hest
  obtain ⟨C, hC, hb⟩ := exists_uniform_parameter_jet_grade_constant
    vectorFourierSobolevScale k s D (fun q ↦ A q.1 * K q.1 ^ (s+k-reserve)) hD
  refine ⟨C, hC, ?_⟩
  intro i c hc v hv
  obtain ⟨hm, hest⟩ := hb (i, ⟨c,hc⟩) v hv
  refine ⟨hm, ?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hm] at hest
  simpa only [mul_assoc] using hest

end JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles
