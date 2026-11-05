module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.FullNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The retained carrier amplitude after common measurement restriction

The initialized row uses `CommonMeasurement.restrictCarrier` on its retained
uncut carriers. The amplitude in the commutator endpoints must therefore
contain the common cutoff at both physical positions. This file proves the
smoothness, support, primitive bounds and literal PDO identity for that SAME
restriction, preserving the reflected amplitude's existing factor four.

Consumers: `exists_augmentedNormal_tame_commutators` and
`exists_uniform_augmentedNormal_elliptic_estimates`.
Sources: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`, `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator
open ContinuumRow ContinuumRow.CommonMeasurement ContinuumNormal
  AmplitudeBound Pseudodifferential PeriodicLocalL2

variable {n : ℕ}

/-- Common measurement restriction is smooth at both physical positions
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem contDiff_restrictAmplitude
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (Function.uncurry (restrictAmplitude b β)) :=
  ((hβ.comp (freezingOutputProjection.contDiff.comp contDiff_snd)).mul
    (hβ.comp (freezingSourceProjection.contDiff.comp contDiff_snd))).smul hb

/-- Multiplication keeps every original support box; no masks are replaced
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem supportedInCenteredBox_restrictAmplitude
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (β : Euclidean n → ℝ) {R : ℝ}
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) :
    ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ restrictAmplitude b β ξ z i j) := by
  intro ξ i j z hz
  apply hs ξ i j z
  intro hzero
  apply hz
  simp [restrictAmplitude, Matrix.smul_apply, hzero]

/-- The original common measurement mask supplies one support box for every
retained carrier, including when the incidence family is empty
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem supportedInCenteredBox_restrictAmplitude_fixedMeasurement
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ ξ i j, SupportedInCenteredBox (4 * r)
      (fun z ↦ restrictAmplitude b (FixedCutoffs.physical hr 1) ξ z i j) := by
  intro ξ i j z hz k
  have hout : FixedCutoffs.physical hr 1 (freezingOutputProjection z) ≠ 0 := by
    intro h
    simp [restrictAmplitude, h] at hz
  have hin : FixedCutoffs.physical hr 1 (freezingSourceProjection z) ≠ 0 := by
    intro h
    simp [restrictAmplitude, h] at hz
  have hbound (x : Euclidean n) (hx : FixedCutoffs.physical hr 1 x ≠ 0) (l : Fin n) :
      |x l| ≤ 4 * r := by
    have hx' := FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx)
    have hcoord : |x l| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x l
    exact hcoord.trans (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx')
  by_cases hk : k.val < n
  · exact hbound _ hout ⟨k.val, hk⟩
  · simpa [freezingSourceProjection, show n + (k.val - n) = k.val by omega] using
      hbound _ hin ⟨k.val - n, by omega⟩

private theorem exists_measurement_pair_jet_bounds (β : Euclidean n → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β) :
    ∃ G : ℕ → ℝ, (∀ k, 0 ≤ G k) ∧ ∀ k z,
      ‖iteratedFDeriv ℝ k (fun z : Euclidean (2 * n) ↦
        β (freezingOutputProjection z) * β (freezingSourceProjection z)) z‖ ≤ G k := by
  choose B hB hbound using fun k ↦ hβs.exists_bound_iteratedFDeriv hβ k
  refine ⟨fun k ↦ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
    (B k * ‖freezingOutputProjection (d := n)‖ ^ j) *
      (B k * ‖freezingSourceProjection (d := n)‖ ^ (k - j)), ?_, ?_⟩
  · intro k
    have := hB k
    exact Finset.sum_nonneg fun j _ ↦ by positivity
  · intro k z
    apply (norm_iteratedFDeriv_mul_le
      (hβ.comp freezingOutputProjection.contDiff)
      (hβ.comp freezingSourceProjection.contDiff) z (by simp)).trans
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    have hout := (norm_iteratedFDeriv_comp_linear_le
      freezingOutputProjection β hβ j z).trans
      (mul_le_mul_of_nonneg_right (hbound k j hjk _) (by positivity))
    have hin := (norm_iteratedFDeriv_comp_linear_le
      freezingSourceProjection β hβ (k - j) z).trans
      (mul_le_mul_of_nonneg_right (hbound k (k - j) (Nat.sub_le ..) _) (by positivity))
    have := hB k
    exact mul_le_mul (mul_le_mul_of_nonneg_left hout (by positivity)) hin
      (norm_nonneg _) (by positivity)

/-- A fixed common measurement cutoff costs a fixed constant at each order
and no extra derivative reserve or high norm. Constants precede the varying
carrier amplitude (`app:ch_background:eq:bg-commutator`). -/
theorem exists_restrictAmplitude_derivative_constants
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧
      ∀ (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ (Function.uncurry b) → ∀ p A,
      (∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) p A) →
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ restrictAmplitude b β ξ z i j) p (C p * A) := by
  obtain ⟨G, hG, hg⟩ := exists_measurement_pair_jet_bounds β hβ hβs
  let C := fun p ↦ ∑ k ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * G j * (2 * n : ℕ) ^ (k - j)
  have hC : ∀ p, 0 ≤ C p := by
    intro p
    exact Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun j _ ↦ by
      have := hG j
      positivity
  refine ⟨C, hC, ?_⟩
  intro b hb p A hA i j ξ is his z
  have hentry : ∀ ξ, ContDiff ℝ ∞ (fun z ↦ b ξ z i j) := fun ξ ↦
    ((matrixEntryEvaluation i j).contDiff.comp hb).comp (contDiff_const.prodMk contDiff_id)
  have hnonneg : 0 ≤ A := (norm_nonneg _).trans ((hA i j).norm_le ξ z)
  let g := fun z : Euclidean (2 * n) ↦
    β (freezingOutputProjection z) * β (freezingSourceProjection z)
  have hgc : ContDiff ℝ ∞ g :=
    (hβ.comp freezingOutputProjection.contDiff).mul
      (hβ.comp freezingSourceProjection.contDiff)
  change ‖euclideanCoordinateDerivList is (fun z ↦ g z • b ξ z i j) z‖ ≤ _
  apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv
    (hgc.smul (hentry ξ)) is z).trans
  apply (norm_iteratedFDeriv_smul_le hgc (hentry ξ) z (by simp)).trans
  calc
    _ ≤ (∑ k ∈ Finset.range (is.length + 1),
        (is.length.choose k : ℝ) * G k * (2 * n : ℕ) ^ (is.length - k)) * A := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      have hder := norm_iteratedFDeriv_le_amplitudeBudget hentry (hA i j) ξ
        (show is.length - k ≤ p by omega) z
      have := hG k
      calc
        _ ≤ (is.length.choose k : ℝ) * G k *
            ((2 * n : ℕ) ^ (is.length - k) * A) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hg k z) (by positivity)) hder
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ C p * A := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      dsimp only [C]
      exact Finset.single_le_sum (f := fun k ↦
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * G j * (2 * n : ℕ) ^ (k - j))
        (fun k _ ↦ Finset.sum_nonneg fun j _ ↦ by have := hG j; positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le his))

/-- The physically sandwiched operator is the literal PDO of the restricted
amplitude, on all L² data. This also permits changing its bound and support
witnesses without changing the operator (`app:ch_background:eq:bg-real-symbol`). -/
theorem vectorTwoPositionL2Operator_physicalSandwich
    (hn : 0 < n) (R R' : ℝ)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hs' : ∀ ξ i j, SupportedInCenteredBox R'
      (fun z ↦ restrictAmplitude b β ξ z i j))
    (B' : ℝ) (hB' : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ restrictAmplitude b β ξ z i j) (2 * (n + 1)) B') :
    freezingVectorPhysicalMultiplier β hβ.continuous hβs ∘L
        vectorTwoPositionL2Operator hn R b hb hs B hB ∘L
        freezingVectorPhysicalMultiplier β hβ.continuous hβs =
      vectorTwoPositionL2Operator hn R' (restrictAmplitude b β)
        (contDiff_restrictAmplitude b hb β hβ) hs' B' hB' := by
  apply DFunLike.coe_injective
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Euclidean n)))
    (F := EuclideanSpace ℂ (Fin n)) (p := 2) (by norm_num)).denseRange_val.equalizer
    (map_continuous _) (map_continuous _)
  funext ⟨v, f, hv, hfs, hfc⟩
  simp only [Function.comp_apply]
  have hf : MemLp f 2 volume := hfc.continuous.memLp_of_hasCompactSupport hfs
  have he : v = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  rw [he]
  apply Lp.ext
  exact (physicalSandwich_ae_matrixFullAmplitudeOperator hn R b hb hs B hB
    β hβ hβs f hf hfc hfs).trans
    (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R'
      (restrictAmplitude b β) (contDiff_restrictAmplitude b hb β hβ) hs' B' hB' f hf
      (fun j ↦ ((contDiff_piLp 2).mp hfc j).of_le (by simp))
      (fun j ↦ hfs.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)).symm

/-- The SAME restricted carrier satisfies the precise real PDO identity
required by both augmented commutator endpoints. Its old reflected amplitude
already contains four; the two measurement multipliers add no factor
(`app:ch_background:eq:bg-real-symbol`, `app:ch_background:eq:bg-commutator`). -/
theorem restricted_carrier_normal_eq
    (hn : 0 < n) (R R' : ℝ)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z))
    (hs' : ∀ ξ i j, SupportedInCenteredBox R'
      (fun z ↦ restrictAmplitude b β ξ z i j))
    (B' : ℝ) (hB' : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ restrictAmplitude b β ξ z i j) (2 * (n + 1)) B')
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hV : carrierChannel V ∘L (carrierChannel V).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R b hb hs B hB))) :
    carrierChannel (restrictCarrier χ V) ∘L (carrierChannel (restrictCarrier χ V)).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R' (restrictAmplitude b β)
          (contDiff_restrictAmplitude b hb β hβ) hs' B' hB')) := by
  rw [restrictCarrier_global_normal χ β hβ.continuous hβs hχ V _ hV,
    vectorTwoPositionL2Operator_physicalSandwich hn R R' b hb hs B hB β hβ hβs hs' B' hB']

/-- Apply the common measurement restriction to the exact full reflected
normal exported by the retained row. The restricted primitive bound and
global normal identity are conclusions, with a constant chosen before all
varying coefficient data. The support is the original common `4*r < 1/2`
box. This closes the operator-identification part of the commutator consumer;
its additional uniform first-derivative baseline is a separate obligation
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem exists_fixedMeasurement_reflected_normal_realization
    (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}
      (a : ContinuumNormalReduction.TransportSymbol.Coefficients n N)
      (J : ContinuumNormalReduction.TransportSymbol.InputVariables n → ℝ)
      (u : ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2 →
        ContinuumRow.TransportKernel.SliceVariable n)
      (Ω : Set (ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2))
      (S : Set (Euclidean 2)) (R : ℝ),
      let b := CarrierNormalRealization.fullReflectedMatrixAmplitude a J u Ω S
      ∀ (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
        (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
        (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      carrierChannel V ∘L (carrierChannel V).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R b hb hs B hB)) →
      let b' := restrictAmplitude b (FixedCutoffs.physical hr 1)
      ∃ hB' : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ b' ξ z i j) (2 * (n + 1)) (C * B),
        let V' := restrictCarrier (FixedCutoffs.periodic hr hcell 1) V
        carrierChannel V' ∘L (carrierChannel V').adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn (4 * r) b'
              (contDiff_restrictAmplitude b hb _ (FixedCutoffs.physical hr 1).contDiff)
              (supportedInCenteredBox_restrictAmplitude_fixedMeasurement b hr) (C * B) hB')) := by
  obtain ⟨C, hC, hrestrict⟩ := exists_restrictAmplitude_derivative_constants
    (FixedCutoffs.physical (n := n) hr 1) (FixedCutoffs.physical hr 1).contDiff
    (FixedCutoffs.physical hr 1).hasCompactSupport
  refine ⟨C (2 * (n + 1)), hC _, ?_⟩
  intro N a J u Ω S R b hb hs B hB V hV
  dsimp only
  refine ⟨hrestrict b hb _ B hB, ?_⟩
  exact restricted_carrier_normal_eq hn R (4 * r) b hb hs B hB
    (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.physical hr 1)
    (FixedCutoffs.physical hr 1).contDiff (FixedCutoffs.physical hr 1).hasCompactSupport
    (FixedCutoffs.periodic_apply hr hcell 1)
    (supportedInCenteredBox_restrictAmplitude_fixedMeasurement b hr)
    (C (2 * (n + 1)) * B) (hrestrict b hb _ B hB) V hV

end JanetCartan.ContinuumCommutator
