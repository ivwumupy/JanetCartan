module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ResidualSmoothEnvelopes.JointRegularity
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Physical

/-!
# Smooth amplitudes for literal measured residual words

The finite inverse expansion in `app:ch_regular:lem:finite-chain` reuses the
retained characteristic envelope estimate on intermediate outputs. These
outputs must have a single globally jointly smooth amplitude representing
the SAME demodulated L² family. The actual output cutoff gives the original
spatial support, and a single fixed linear smooth realization preserves the
original parameter cutoff. All spatial regularity comes from the actual
all-order Sobolev estimates of the fixed measured residual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
open RetardedSobolev.Spaces FourierIntegral Pseudodifferential
open RegularSector.FiniteAssembly ResponseSmoothParameters
open FiniteChain.Graph.KernelLimits
open ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
open LocalSobolev RegularSector.FiniteAssembly.CoefficientNorms
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

open ResponseTransfer ResponseTransfer.Complement
open RegularSector.Characteristic.RetardedLocalization FourierIntegral.LowBounds

/-- Construct one globally jointly smooth representative of the actual
measured operator. Its outer mask proves spatial support, and linearity
preserves every parameter on which the source is zero. The all-order Fourier
premise is supplied by the original residual's positive estimates and
`exists_measuredOperator_fourier_constants`; no output smoothness is assumed.
Consumer: reapplying the retained envelope theorem in
`app:ch_regular:lem:finite-chain`. -/
theorem exists_jointly_smooth_measured_response
    {p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (c : Euclidean p ≃L[ℝ] Z)
    {X : Set E} (hX : IsCompact X)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (T : H →L[ℂ] H)
    (hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ)
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (f : Z → graphTestSpace (d + 1) r)
    (hf : ContDiff ℝ ∞ (fun w : E × Z ↦ (f w.2).val w.1))
    (hs : ∀ a, tsupport (f a).val ⊆ X) :
    ∃ b : E × Z → F, ContDiff ℝ ∞ b ∧
      (∀ z, z.1 ∉ tsupport χout → b z = 0) ∧
      (∀ a, (fun x ↦ b (x,a)) =ᵐ[volume]
        measuredOperator χout χin ho hi hob hib T (graphTestToLp (f a))) ∧
      ∀ a, f a = 0 → (fun x ↦ b (x,a)) = 0 := by
  let A := measuredOperator χout χin ho hi hob hib T
  have hmem (u : graphTestSpace (d + 1) r) (s : ℕ) :
      MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) := by
    obtain ⟨_, _, _, h⟩ := hA s
    exact (h u).1
  obtain ⟨R, hR⟩ := exists_smooth_linear_graph_realization A hmem
  have hcont := contDiff_joint_graph_realization e he c hX A R hR hA f hf hs
  refine ⟨fun z ↦ R (f z.2) z.1, hcont, ?_, fun a ↦ (hR (f a)).2, ?_⟩
  · intro z hz
    have ha : R (f z.2) =ᵐ[volume.restrict (tsupport χout)ᶜ] (fun _ ↦ (0 : F)) := by
      filter_upwards [ae_restrict_of_ae (hR (f z.2)).2,
        ae_restrict_of_ae (sourceCutMultiplier_coeFn χout ho hob
          (T (sourceCutMultiplier χin hi hib (graphTestToLp (f z.2))))),
        ae_restrict_mem (isClosed_tsupport χout).isOpen_compl.measurableSet] with y hy hm hyS
      rw [hy]
      change (sourceCutMultiplier χout ho hob
        (T (sourceCutMultiplier χin hi hib (graphTestToLp (f z.2))))) y = _
      rw [hm, image_eq_zero_of_notMem_tsupport hyS]
      exact zero_smul _ _
    exact Measure.eqOn_open_of_ae_eq ha (isClosed_tsupport χout).isOpen_compl
      (hR (f z.2)).1.continuous.continuousOn continuousOn_const hz
  · intro a ha
    change R (f a) = 0
    rw [ha, map_zero]

/-- Demodulate the SAME measured output while retaining its global joint
smoothness, actual spatial support, and original parameter zero support.
The equality is an equality of whole parameter families of L² classes, so
ordered differentiation acts on this same representative
(`app:ch_response:eq:response-two-envelopes`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_jointly_smooth_demodulated_measured_response
    {p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (c : Euclidean p ≃L[ℝ] Z)
    {X : Set E} (hX : IsCompact X)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (T : H →L[ℂ] H)
    (hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ)
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (f : Z → graphTestSpace (d + 1) r)
    (hf : ContDiff ℝ ∞ (fun w : E × Z ↦ (f w.2).val w.1))
    (hs : ∀ a, tsupport (f a).val ⊆ X)
    (lam : ℝ) (φ : E × Z → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∃ b : E × Z → F, ContDiff ℝ ∞ b ∧
      (∀ z, z.1 ∉ tsupport χout → b z = 0) ∧
      (∀ a, (fun x ↦ b (x,a)) =ᵐ[volume]
        carrierMultiplication (-lam) (fun x ↦ φ (x,a))
          (hφ.continuous.comp (continuous_id.prodMk continuous_const))
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp (f a)))) ∧
      ∀ a, f a = 0 → (fun x ↦ b (x,a)) = 0 := by
  obtain ⟨b, hb, hbs, hbe, hbz⟩ := exists_jointly_smooth_measured_response
    e he c hX χout χin ho hi hob hib T hA f hf hs
  refine ⟨fun z ↦ carrier (-lam) (fun x ↦ φ (x,z.2)) z.1 • b z, ?_, ?_, ?_, ?_⟩
  · have hc : ContDiff ℝ ∞ (fun z : E × Z ↦ carrier (-lam) (fun x ↦ φ (x,z.2)) z.1) := by
      change ContDiff ℝ ∞ (fun z : E × Z ↦ Complex.exp (Complex.I * ↑(-lam * φ z)))
      exact (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ))).cexp
    exact hc.smul hb
  · intro z hz
    change carrier (-lam) (fun x ↦ φ (x,z.2)) z.1 • b z = 0
    rw [hbs z hz, smul_zero]
  · intro a
    filter_upwards [hbe a, carrierMultiplication_ae (-lam) (fun x ↦ φ (x,a))
      (hφ.continuous.comp (continuous_id.prodMk continuous_const))
      (measuredOperator χout χin ho hi hob hib T (graphTestToLp (f a)))] with x hx hc
    rw [hc, hx]
  · intro a ha
    funext x
    change carrier (-lam) (fun y ↦ φ (y,a)) x • b (x,a) = 0
    rw [congrFun (hbz a ha) x]
    exact smul_zero _



/-- Modulate the original graph-test family, apply the literal measured
residual, and demodulate its ONE smooth representative. Both carrier factors
are the published L² multipliers, and the source graph-test class is unchanged
(`app:ch_response:eq:fixed-factor-transfer`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_jointly_smooth_measured_envelope
    {p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (c : Euclidean p ≃L[ℝ] Z)
    {X : Set E} (hX : IsCompact X)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (T : H →L[ℂ] H)
    (hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ)
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (measuredOperator χout χin ho hi hob hib T (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (f : Z → graphTestSpace (d + 1) r)
    (hf : ContDiff ℝ ∞ (fun w : E × Z ↦ (f w.2).val w.1))
    (hs : ∀ a, tsupport (f a).val ⊆ X)
    (lam : ℝ) (φ : E × Z → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∃ b : E × Z → F, ContDiff ℝ ∞ b ∧
      (∀ z, z.1 ∉ tsupport χout → b z = 0) ∧
      (∀ a, (fun x ↦ b (x,a)) =ᵐ[volume]
        carrierMultiplication (-lam) (fun x ↦ φ (x,a))
          (hφ.continuous.comp (continuous_id.prodMk continuous_const))
          (measuredOperator χout χin ho hi hob hib T
            (carrierMultiplication lam (fun x ↦ φ (x,a))
              (hφ.continuous.comp (continuous_id.prodMk continuous_const))
              (graphTestToLp (f a))))) ∧
      ∀ a, f a = 0 → (fun x ↦ b (x,a)) = 0 := by
  have hcarrier : ContDiff ℝ ∞
      (fun z : E × Z ↦ carrier lam (fun x ↦ φ (x,z.2)) z.1) := by
    change ContDiff ℝ ∞ (fun z : E × Z ↦ Complex.exp (Complex.I * ↑(lam * φ z)))
    exact (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ))).cexp
  have hcm (a : Z) : ContDiff ℝ ∞ (fun x : E ↦ carrier lam (fun y ↦ φ (y,a)) x) := by
    exact hcarrier.comp (contDiff_id.prodMk (contDiff_const (c := a)))
  let fm (a : Z) : graphTestSpace (d + 1) r :=
    ⟨fun x ↦ carrier lam (fun y ↦ φ (y,a)) x • (f a).val x,
      (hcm a).smul (f a).property.1,
      (f a).property.2.smul_left (f := carrier lam (fun y : E ↦ φ (y,a)))⟩
  have hfm : ContDiff ℝ ∞ (fun w : E × Z ↦ (fm w.2).val w.1) := hcarrier.smul hf
  have hsm (a : Z) : tsupport (fm a).val ⊆ X :=
    (tsupport_smul_subset_right _ _).trans (hs a)
  have hme (a : Z) : graphTestToLp (fm a) =
      carrierMultiplication lam (fun x ↦ φ (x,a))
        (hφ.continuous.comp (continuous_id.prodMk continuous_const)) (graphTestToLp (f a)) := by
    apply Lp.ext
    filter_upwards [(graphTest_memLp (fm a)).coeFn_toLp,
      (graphTest_memLp (f a)).coeFn_toLp,
      carrierMultiplication_ae lam (fun x ↦ φ (x,a))
        (hφ.continuous.comp (continuous_id.prodMk continuous_const)) (graphTestToLp (f a))]
      with x hx hf hc
    change (graphTestToLp (fm a) : E → F) x = (fm a).val x at hx
    change (graphTestToLp (f a) : E → F) x = (f a).val x at hf
    rw [hx, hc, hf]
  obtain ⟨b, hb, hbs, hbe, hbz⟩ := exists_jointly_smooth_demodulated_measured_response
    e he c hX χout χin ho hi hob hib T hA fm hfm hsm lam φ hφ
  refine ⟨b, hb, hbs, ?_, ?_⟩
  · intro a
    simpa only [hme a] using hbe a
  · intro a ha
    apply hbz a
    apply Subtype.ext
    funext x
    change carrier lam (fun y ↦ φ (y,a)) x • (f a).val x = 0
    rw [ha]
    exact smul_zero _

/-- A supported envelope has the SAME zero extension after restriction to
the original inverse domain. Apply with the actual `tsupport χ₂ ⊆ Uinv`;
no boundary regularity of an uncut local representative is presumed
(`app:ch_regular:thm:exact-correction`, `app:ch_regular:lem:finite-chain`). -/
theorem zeroExtend_restrict_envelope_eq
    {U S : Set E} (hU : MeasurableSet U) (hSU : S ⊆ U)
    (b : E → F) (hs : ∀ x, x ∉ S → b x = 0) (v : H)
    (he : b =ᵐ[volume] v) :
    SmallSupport.zeroExtend hU (restrictL2 U v) = v := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hU).mp (restrictL2_coeFn U v)
  filter_upwards [SmallSupport.zeroExtend_coeFn hU (restrictL2 U v), hr, he]
    with x hx hr he
  rw [hx]
  by_cases hxU : x ∈ U
  · exact (indicator_of_mem hxU _).trans (hr hxU)
  · rw [indicator_of_notMem hxU]
    exact (hs x (fun hxS ↦ hxU (hSU hxS))).symm.trans he


/-- The original all-order positive tame estimates give the graph-test
signature used by the smooth measured-envelope construction. Fixed-history
high coefficient quantities are absorbed into the constant using the SAME
Sobolev norm. Producers are the actual retarded, PDO, and elliptic positive
bounds, followed by the existing measured-mask estimates
(`app:ch_regular_base:eq:sector-theorem-residual`). -/
theorem all_order_graph_bounds_of_tame
    (A : H →L[ℂ] H) (sourceOrder : ℕ → ℕ) (cost high : ℕ → ℝ)
    (hcost : ∀ s, 0 ≤ cost s) (hhigh : ∀ s, 0 ≤ high s)
    (hA : ∀ s : ℕ, ∀ u : H,
      MemVectorFourierSobolev (sourceOrder s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (A u) ∧
        vectorFourierSobolevNorm (s : ℝ) (A u) ≤
          cost s * (vectorFourierSobolevNorm (sourceOrder s : ℝ) u + high s * ‖u‖)) :
    ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ) (A (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u) := by
  intro s
  refine ⟨sourceOrder s, cost s * (1 + high s),
    mul_nonneg (hcost s) (add_nonneg zero_le_one (hhigh s)), ?_⟩
  intro u
  have hu := graphTest_memVectorFourierSobolev (sourceOrder s : ℝ) u
  obtain ⟨hm, hn⟩ := hA s (graphTestToLp u) hu
  have hnorm : ‖graphTestToLp u‖ ≤
      vectorFourierSobolevNorm (sourceOrder s : ℝ) (graphTestToLp u) := by
    simpa only [vectorFourierSobolevNorm_zero] using
      vectorFourierSobolevNorm_mono hu (Nat.cast_nonneg (sourceOrder s))
  refine ⟨hm, hn.trans ?_⟩
  calc
    cost s * (vectorFourierSobolevNorm (sourceOrder s : ℝ) (graphTestToLp u) +
        high s * ‖graphTestToLp u‖) ≤
      cost s * (vectorFourierSobolevNorm (sourceOrder s : ℝ) (graphTestToLp u) +
        high s * vectorFourierSobolevNorm (sourceOrder s : ℝ) (graphTestToLp u)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm (hhigh s))) (hcost s)
    _ = cost s * (1 + high s) *
        vectorFourierSobolevNorm (sourceOrder s : ℝ) (graphTestToLp u) := by ring

end JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
