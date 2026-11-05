module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.PrimitiveSobolev
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration

/-!
# Elapsed integration of the complementary jets

The input estimates here are the fixed-time conclusions of
`AnnularComplement.originalAnnularComplement_sobolev`, indexed by the original
family and the elapsed time in the fixed interval. This deduction proves the
derivative interchange; it does not assume it. The original regularization
constructor and the same-operator identification supply orbit measurability.
The primitive assembly must instantiate both inputs before using this result
for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open AnnularComplement JanetCartan.Pseudodifferential
open RegularSector.Characteristic.EvolutionIntegral

variable {p d r : ℕ} {I : Type}
local notation "P" => Euclidean p
local notation "H" => SpacetimeL2 d r

/-- Measurability of every actual carrier jet on the fixed elapsed interval
follows from orbit measurability and smoothness in the carrier parameter.
No time differentiability is needed. Consumer: dominated time differentiation
in `app:ch_response:lem:energy-carrier-jets`. -/
theorem aestronglyMeasurable_elapsed_jet
    {Δ : ℝ} {V : Set P} (hV : IsOpen V) {R : ℝ → P → H}
    (hm : ∀ c ∈ V, AEStronglyMeasurable (fun t => R t c)
      (volume.restrict (Icc 0 Δ)))
    (hR : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (R t) V)
    (k : ℕ) {c : P} (hc : c ∈ V) :
    AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (R t) c)
      (volume.restrict (Icc 0 Δ)) := by
  classical
  let F : ℝ → P → H := fun t => if t ∈ Icc 0 Δ then R t else 0
  have he : ∀ᵐ t ∂volume.restrict (Icc 0 Δ), F t = R t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [F, ite_eq_left_iff]
    exact fun h => (h ht).elim
  have hmF (a : P) (ha : a ∈ V) : AEStronglyMeasurable (fun t => F t a)
      (volume.restrict (Icc 0 Δ)) :=
    (hm a ha).congr (he.mono (fun _ h => congrFun h.symm a))
  have hF (t : ℝ) : ContDiffOn ℝ ∞ (F t) V := by
    dsimp only [F]
    split_ifs with ht
    · exact hR t ht
    · exact contDiffOn_const
  exact (aestronglyMeasurable_annularKernel_jet hV hmF hF k hc).congr
    (he.mono (fun _ h => congrArg (fun f => iteratedFDeriv ℝ k f c) h))

/-- Uniform fixed-time complementary precision passes to the actual Bochner
integral, with exactly the interval-length cost. All carrier derivatives
commute with the integral as multilinear maps and on arbitrary direction
tuples. The constant remains uniform in the family, and every real Sobolev
order and accuracy is retained.

The sole estimate input is the conclusion of
`originalAnnularComplement_sobolev`; its producer retains the separate window
`1 ≤ L ≤ K ≤ λ^(1-ν)`. This lemma makes no change to that window or its fixed
losses. It is an integration deduction, not a primitive construction.
Source: `app:ch_response:lem:energy-carrier-jets`.
Consumer: the complementary term in `app:ch_response:eq:direct-envelope-profile`. -/
theorem elapsedIntegral_complementary_sobolev
    {Δ : ℝ} (hΔ : 0 ≤ Δ) {V : Set P} (hV : IsOpen V)
    (R : I → ℝ → P → H) (lam A : I → ℝ)
    (hA : ∀ i, 0 ≤ A i)
    (hm : ∀ i c, c ∈ V → AEStronglyMeasurable (fun t => R i t c)
      (volume.restrict (Icc 0 Δ)))
    (hR : ∀ i t, t ∈ Icc 0 Δ → ContDiffOn ℝ ∞ (R i t) V)
    (hsob : ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i t, t ∈ Icc 0 Δ → ∀ c, c ∈ V → ∀ v : Fin k → P,
        (∀ j, ‖v j‖ ≤ 1) →
        MemVectorFourierSobolev s (iteratedFDeriv ℝ k (R i t) c v) ∧
        vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (R i t) c v) ≤
          C * A i * lam i ^ (-Q)) :
    (∀ i c, c ∈ V → IntegrableOn (fun t => R i t c) (Icc 0 Δ)) ∧
    (∀ i k c, c ∈ V → IntegrableOn
      (fun t => iteratedFDeriv ℝ k (R i t) c) (Icc 0 Δ)) ∧
    (∀ i, ContDiffOn ℝ ∞ (fun c => ∫ t in Icc 0 Δ, R i t c) V) ∧
    (∀ i k c, c ∈ V → iteratedFDeriv ℝ k
      (fun a => ∫ t in Icc 0 Δ, R i t a) c =
        ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R i t) c) ∧
    (∀ i k (v : Fin k → P) c, c ∈ V → iteratedFDeriv ℝ k
      (fun a => ∫ t in Icc 0 Δ, R i t a) c v =
        ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R i t) c v) ∧
    ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i c, c ∈ V → ∀ v : Fin k → P, (∀ j, ‖v j‖ ≤ 1) →
        MemVectorFourierSobolev s
          (iteratedFDeriv ℝ k (fun a => ∫ t in Icc 0 Δ, R i t a) c v) ∧
        vectorFourierSobolevNorm s
          (iteratedFDeriv ℝ k (fun a => ∫ t in Icc 0 Δ, R i t a) c v) ≤
            (Δ * C) * A i * lam i ^ (-Q) := by
  choose B hB hb using fun k => hsob 0 k 0
  have hmj (i : I) (k : ℕ) (c : P) (hc : c ∈ V) :=
    aestronglyMeasurable_elapsed_jet hV (hm i) (hR i) k hc
  have hbound (i : I) (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Δ)
      (c : P) (hc : c ∈ V) : ‖iteratedFDeriv ℝ k (R i t) c‖ ≤ B k * A i := by
    apply annularJet_norm_le_of_unit_directions _ (mul_nonneg (hB k) (hA i))
    intro v hv
    simpa only [vectorFourierSobolevNorm_zero, neg_zero, Real.rpow_zero, mul_one]
      using (hb k i t ht c hc v hv).2
  have hint (i : I) (k : ℕ) (c : P) (hc : c ∈ V) : IntegrableOn
      (fun t => iteratedFDeriv ℝ k (R i t) c) (Icc 0 Δ) := by
    apply (integrableOn_const (C := B k * A i) (measure_Icc_lt_top.ne)).mono'
      (hmj i k c hc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound i k t ht c hc
  have he (i : I) (k : ℕ) (c : P) (hc : c ∈ V) :
      iteratedFDeriv ℝ k (fun a => ∫ t in Icc 0 Δ, R i t a) c =
        ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R i t) c := by
    apply MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
      (r := k) (b := fun j _ => B j * A i) hV
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht a ha
      exact ((hR i t ht).contDiffAt (hV.mem_nhds ha)).of_le (by simp)
    · exact fun j _ a ha => hmj i j a ha
    · exact fun j _ => integrableOn_const (measure_Icc_lt_top.ne)
    · intro j _
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht a ha
      exact hbound i j t ht a ha
    · exact le_rfl
    · exact hc
  have hev (i : I) (k : ℕ) (v : Fin k → P) (c : P) (hc : c ∈ V) :
      iteratedFDeriv ℝ k (fun a => ∫ t in Icc 0 Δ, R i t a) c v =
        ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R i t) c v := by
    rw [he i k c hc, ContinuousMultilinearMap.integral_apply (hint i k c hc)]
  refine ⟨?_, hint, ?_, he, hev, ?_⟩
  · intro i c hc
    have hi := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => P) H 0).integrable_comp
      (hint i 0 c hc)
    change IntegrableOn (fun t => iteratedFDeriv ℝ 0 (R i t) c 0) (Icc 0 Δ) at hi
    simpa only [iteratedFDeriv_zero_apply] using hi
  · intro i
    have hd (k : ℕ) (c : P) (hc : c ∈ V) : DifferentiableAt ℝ
        (fun a => ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R i t) a) c := by
      apply HasFDerivAt.differentiableAt
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun a t => fderiv ℝ (iteratedFDeriv ℝ k (R i t)) a)
        (bound := fun _ => B (k + 1) * A i) (hV.mem_nhds hc)
      · exact Filter.mem_of_superset (hV.mem_nhds hc) (fun a ha => hmj i k a ha)
      · exact hint i k c hc
      · exact (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) => P) H).continuous.comp_aestronglyMeasurable
            (hmj i (k + 1) c hc)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht a ha
        simpa only [norm_fderiv_iteratedFDeriv] using hbound i (k + 1) t ht a ha
      · exact integrableOn_const (measure_Icc_lt_top.ne)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht a ha
        exact (((hR i t ht).contDiffAt (hV.mem_nhds ha)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top k : (k : ℕ∞ω) < ∞)).hasFDerivAt
    have hew (k : ℕ) : EqOn
        (iteratedFDerivWithin ℝ k (fun a => ∫ t in Icc 0 Δ, R i t a) V)
        (fun a => ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R i t) a) V := by
      intro c hc
      rw [iteratedFDerivWithin_of_isOpen k hV hc]
      exact he i k c hc
    apply (contDiffOn_iff_continuousOn_differentiableOn hV.uniqueDiffOn).mpr
    exact ⟨fun k _ => ContinuousOn.congr
      (fun c hc => (hd k c hc).continuousAt.continuousWithinAt) (hew k),
      fun k _ => DifferentiableOn.congr
      (fun c hc => (hd k c hc).differentiableWithinAt) (hew k)⟩
  · intro s k Q
    obtain ⟨C, hC, hs⟩ := hsob s k Q
    refine ⟨C, hC, fun i c hc v hv => ?_⟩
    rw [hev i k v c hc]
    have hi := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P) H v).integrable_comp
      (hint i k c hc)
    change IntegrableOn (fun t => iteratedFDeriv ℝ k (R i t) c v) (Icc 0 Δ) at hi
    have h := SobolevIntegration.integral_vectorSobolev_bound hΔ s
      (C * A i * lam i ^ (-Q)) _ hi (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hs i t ht c hc v hv)
    simpa only [mul_assoc] using h

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
