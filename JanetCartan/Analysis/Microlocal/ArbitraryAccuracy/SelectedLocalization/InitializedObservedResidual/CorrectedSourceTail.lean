module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedCorrectedExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.RecutRemainderObservation
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.RecutInverseRemainder
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Restriction

/-!
# Angular observation of the same initialized corrected source

The actual finite expansion of the normalized corrected source joins the
observed complete residual powers to the unobserved inverse remainder.
The latter is supplied on the literal inner-cut product source by
`exists_normalized_innerCut_product_inverse_remainder_constants`.
The normalized source has the proved order-zero observation cost.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open LocalSobolev FixedDomainInverse SmallSupport
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization FourierIntegral.LowBounds SignedProductEstimates
variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem sourceCut_realCompression_eq_bump {D : Set E} (hD : MeasurableSet D)
    (W : Set E) (χ : ContDiffBump center) (T : H →L[ℂ] H) (u : LocalL2 D E) :
    localRealCompression hD W ((sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ)).comp T) u =
      bumpL2 (p := 2) le_rfl χ (localRealCompression hD W T u) := by
  let z := T (zeroExtend hD (l2ComplexInclusion (volume.restrict D) u))
  change l2RealPart (volume.restrict W)
      (restrictL2 W (sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ) z)) =
    bumpL2 (p := 2) le_rfl χ (l2RealPart (volume.restrict W) (restrictL2 W z))
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL
      (restrictL2 W (sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ) z)),
    restrictL2_coeFn W (sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ) z),
    ae_restrict_of_ae (sourceCutMultiplier_coeFn χ χ.continuous (bump_norm_le_one χ) z),
    bumpL2_coeFn (p := 2) le_rfl χ (l2RealPart (volume.restrict W) (restrictL2 W z)),
    euclideanRealPart.coeFn_compLpL (restrictL2 W z), restrictL2_coeFn W z]
    with y hleft hleftRestr hmul hright hrightReal hrightRestr
  change l2RealPart (volume.restrict W)
      (restrictL2 W (sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ) z)) y = _ at hleft
  change l2RealPart (volume.restrict W) (restrictL2 W z) y = _ at hrightReal
  rw [hleft, hleftRestr, hmul, hright, hrightReal, hrightRestr]
  ext k
  simp only [euclideanRealPart_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Restrict the observed smooth cutoff back to its unchanged core values.
The genuine weak extension is retained; no positive-order zero-extension
bound across either boundary is used. -/
private theorem observed_core_sobolev_bound {D : Set E} (hD : MeasurableSet D)
    (V W : Set E) (hV : MeasurableSet V) (hW : MeasurableSet W) (hWV : W ⊆ V)
    (χ : ContDiffBump center) (hχ : ∀ y ∈ W, χ y = 1)
    (T : H →L[ℂ] H) (u : LocalL2 D E) (s : ℕ)
    (hv : MemRestrictionSobolev V s
      (bumpL2 (p := 2) le_rfl χ (localRealCompression hD V T u))) :
    MemRestrictionSobolev W s (localRealCompression hD W T u) ∧
      restrictionSobolevNorm W s (localRealCompression hD W T u) ≤
        restrictionSobolevNorm V s
          (bumpL2 (p := 2) le_rfl χ (localRealCompression hD V T u)) := by
  have hext (e : SobolevExtension V s
      (bumpL2 (p := 2) le_rfl χ (localRealCompression hD V T u))) :
      e.toFun =ᵐ[volume.restrict W] localRealCompression hD W T u := by
    filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hV).mp e.restrict_eq),
      ae_restrict_of_ae ((ae_restrict_iff' hV).mp
        (bumpL2_coeFn (p := 2) le_rfl χ (localRealCompression hD V T u))),
      ae_restrict_of_ae ((ae_restrict_iff' hV).mp (localRealCompression_coeFn hD V T u)),
      localRealCompression_coeFn hD W T u, ae_restrict_mem hW]
      with y he hb hrealV hrealW hy
    rw [he (hWV hy), hb (hWV hy), hχ y hy, one_smul, hrealV (hWV hy), hrealW]
  let cut (e : SobolevExtension V s
      (bumpL2 (p := 2) le_rfl χ (localRealCompression hD V T u))) :
      SobolevExtension W s (localRealCompression hD W T u) :=
    { e with restrict_eq := hext e }
  refine ⟨⟨cut hv.some⟩, ?_⟩
  unfold restrictionSobolevNorm
  refine le_csInf ⟨hv.some.jetNorm, hv.some, rfl⟩ ?_
  rintro _ ⟨e, rfl⟩
  exact restrictionSobolevNorm_le (cut e)

/-- Observe the actual normalized corrected source on its original core.
The finite-word input is constructed by `exists_original_retained_residual_hchain`.
The unobserved finite-remainder input is exactly the literal inner-cut source
output of `exists_normalized_innerCut_product_inverse_remainder_constants`
(or the retained primary remainder constructor). Its actual source must be
instantiated before applying this theorem. The complete normalized source
minus ONE identity is given its proved order-zero cost here; no angular
inverse remainder estimate is assumed. The finite expansion and the L²-to-Lᵖ
corrected-source implementation use the SAME residual and inverse throughout
(`app:ch_regular:eq:finite-neumann-identity`,
`app:ch_regular:eq:resolved-angular-tail`, `app:ch_pairs:eq:pairs-lag-one-error`). -/
theorem normalized_correctedSource_angular_rapidDecayAt_of_original_remainder
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (Q : ι → E → Fin (d+1) → MetricTensor (d+1)) (B : ι → E → MetricTensor (d+1))
    (W₁ : ι → f.centers → TwoTimeAmplitude d (d+1)) (retarded : ι → H →L[ℂ] H)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    {D : Set E} (hD : MeasurableSet D) {rLp : ℝ} (hrLp : 0 < rLp)
    (hball : ball center rLp ⊆ D)
    (hmem : ∀ i v, MemRestrictionSobolev (ball center rLp) 1
      (localRealCompression hD (ball center rLp)
        (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i)) v))
    {budget : ℝ} (hbudget : 0 ≤ budget)
    (hbound : ∀ i v, restrictionSobolevNorm (ball center rLp) 1
      (localRealCompression hD (ball center rLp)
        (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i)) v) ≤
          budget * ‖v‖)
    (χ₂ χ₃ χobs : ContDiffBump center)
    (hχ₂ball : tsupport (χ₂ : E → ℝ) ⊆ ball center rLp)
    (hnest : ∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1)
    (hχ₃D : tsupport (χ₃ : E → ℝ) ⊆ D)
    (Vobs Wcore : Set E) (hVobs : MeasurableSet Vobs) (hWcore : MeasurableSet Wcore)
    (hχobsV : tsupport (χobs : E → ℝ) ⊆ Vobs) (hWV : Wcore ⊆ Vobs)
    (hχobsCore : ∀ y ∈ Wcore, χobs y = 1)
    (ρ A : ι → ℝ) (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (s : ℕ) (h : ι → LocalL2 D E) :
    let Rp := fun i ↦ residualToLpOnBall center hrLp hball
      (localRealCompression hD (ball center rLp)
        (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i)))
      (hmem i) hbudget (hbound i)
    let Kloc := fun i ↦ localizedResidual (two_lt_ballSobolevExponent (F := E) center hrLp).le
      χ₂ χ₃ isOpen_ball.measurableSet (Rp i)
    let Krecut := fun i ↦ localRealCompression hD D
      (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
        (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
        (pairedResidual f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i)))
    let u := fun i ↦ bumpL2 (p := 2) le_rfl χ₂ (h i)
    let observation := localRealCompression hD Vobs (pairedSource f hK L₀ output ho.continuous hob - 1)
    (∀ i, ‖Kloc i‖ < 1) →
    (∀ j, RapidDecayAt (restrictionSobolevScale Vobs E hVobs) s ρ A
      (fun i ↦ observation ((Krecut i^j) (u i)))) →
    (∀ q : ℕ, ∃ depth : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      MemRestrictionSobolev D s (neumannInverse (Krecut i) ((Krecut i^(depth+s)) (u i))) ∧
      restrictionSobolevNorm D s (neumannInverse (Krecut i) ((Krecut i^(depth+s)) (u i))) ≤
        C*A i*((ρ i)^q)⁻¹) →
    RapidDecayAt (restrictionSobolevScale Wcore E hWcore) s ρ A
      (fun i ↦ localRealCompression hD Wcore (pairedSource f hK L₀ output ho.continuous hob - 1)
        (correctedSource (two_lt_ballSobolevExponent (F := E) center hrLp).le
          χ₂ χ₃ isOpen_ball.measurableSet (Rp i) (h i))) := by
  intro Rp Kloc Krecut u observation hKloc hchain hremainder
  have hsame (i : ι) : Kloc i = Krecut i := by
    simpa only [Kloc, Krecut, Rp, pairedResidual, normalizedPair,
      RegularSector.FiniteAssembly.physicalPair_measuredOperator] using
      localizedResidual_eq_real_measuredOperator (d := d) (q := d+1) hD center hrLp hball
        ((1/2 : ℂ) • (selectedFiniteDirectResidual f L₀ (Q i) (B i) (W₁ i)
          output ho.continuous hob (retarded i) +
          (sourceCutMultiplier output ho.continuous hob).comp
            (RegularSector.EllipticComplement.ellipticResidual f hK L₀ (Q i) (B i))))
        (hmem i) hbudget (hbound i) χ₂ χ₃ hχ₂ball
  have hKrecut (i : ι) : ‖Krecut i‖ < 1 := hsame i ▸ hKloc i
  let G := restrictionSobolevScale Vobs E hVobs
  let cutObs : LocalL2 Vobs E →L[ℝ] LocalL2 Vobs E :=
    bumpL2 (F := E) (μ := volume.restrict Vobs) (p := 2) le_rfl χobs
  obtain ⟨Cbump, hCbump, hbump⟩ := exists_bumpL2_sobolev_bound (F := E) χobs s
  have hchainCut (j : ℕ) : RapidDecayAt G s ρ A
      (fun i ↦ cutObs (observation ((Krecut i^j) (u i)))) := by
    intro accuracy
    obtain ⟨C, hC, hc⟩ := hchain j accuracy
    refine ⟨Cbump*C, mul_nonneg (zero_le_one.trans hCbump) hC, ?_⟩
    intro i
    obtain ⟨hm, hn⟩ := hbump Vobs hVobs hχobsV _ (hc i).1
    refine ⟨hm, ?_⟩
    change G.gradeNorm s (cutObs (observation ((Krecut i^j) (u i)))) ≤ _
    have hb := (hc i).2
    rw [restrictionSobolevScale_gradeNorm hVobs (hc i).1] at hb
    exact (restrictionSobolevScale_gradeNorm hVobs hm).trans_le
      (hn.trans ((mul_le_mul_of_nonneg_left hb (zero_le_one.trans hCbump)).trans_eq (by ring)))
  obtain ⟨Cobs, hCobs, hobserve⟩ := exists_normalized_inverse_remainder_observation_constants
    f hK output ho hoc hob χ₂ χ₃ hnest χobs χobs.contDiff χobs.hasCompactSupport
    (bump_norm_le_one χobs)
  let corrected := fun i ↦ correctedSource (two_lt_ballSobolevExponent (F := E) center hrLp).le
    χ₂ χ₃ isOpen_ball.measurableSet (Rp i) (h i)
  have htail : RapidDecayAt G s ρ A (fun i ↦ cutObs (observation (corrected i))) := by
    intro accuracy
    obtain ⟨q, hq⟩ := exists_nat_gt accuracy
    obtain ⟨depth, Crem, hCrem, hrem⟩ := hremainder q
    let power := depth+s
    let rem := fun i ↦ neumannInverse (Krecut i) ((Krecut i^power) (u i))
    have hobsrem (i : ι) : cutObs (observation (rem i)) ∈ G.level s ∧
        G.gradeNorm s (cutObs (observation (rem i))) ≤ Cobs s*Crem*A i*(ρ i)^(-accuracy) := by
      have hb := hobserve L₀ hL₀ (Q i) (B i) (W₁ i) (retarded i) D Vobs hD hVobs
        hχ₃D hχobsV power (h i) (hKrecut i) s (hrem i).1
      have heq := sourceCut_realCompression_eq_bump hD Vobs χobs
        (pairedSource f hK L₀ output ho.continuous hob - 1) (rem i)
      change MemRestrictionSobolev Vobs s
          (localRealCompression hD Vobs ((sourceCutMultiplier χobs χobs.continuous
            (bump_norm_le_one χobs)).comp (pairedSource f hK L₀ output ho.continuous hob - 1)) (rem i)) ∧
        restrictionSobolevNorm Vobs s
          (localRealCompression hD Vobs ((sourceCutMultiplier χobs χobs.continuous
            (bump_norm_le_one χobs)).comp (pairedSource f hK L₀ output ho.continuous hob - 1)) (rem i)) ≤
          Cobs s * restrictionSobolevNorm D s (rem i) at hb
      rw [heq] at hb
      refine ⟨hb.1, ?_⟩
      apply (restrictionSobolevScale_gradeNorm hVobs hb.1).trans_le
      have hrate : ((ρ i)^q)⁻¹ ≤ (ρ i)^(-accuracy) := by
        have hh := Real.rpow_le_rpow_of_exponent_le (hρ i) (neg_le_neg hq.le)
        simpa only [Real.rpow_neg (zero_le_one.trans (hρ i)), Real.rpow_natCast] using hh
      calc
        _ ≤ Cobs s * restrictionSobolevNorm D s (rem i) := hb.2
        _ ≤ Cobs s * (Crem*A i*((ρ i)^q)⁻¹) := mul_le_mul_of_nonneg_left (hrem i).2 (hCobs s)
        _ = (Cobs s*Crem*A i)*((ρ i)^q)⁻¹ := by ring
        _ ≤ (Cobs s*Crem*A i)*(ρ i)^(-accuracy) :=
          mul_le_mul_of_nonneg_left hrate (mul_nonneg (mul_nonneg (hCobs s) hCrem) (hA i))
    choose C hC hc using fun j ↦ hchainCut j accuracy
    refine ⟨Cobs s*Crem + ∑ j ∈ Finset.range power, C j,
      add_nonneg (mul_nonneg (hCobs s) hCrem) (Finset.sum_nonneg fun j _ ↦ hC j), ?_⟩
    intro i
    have hexp := normalized_correctedSource_angular_finite_expansion
      f hK L₀ (Q i) (B i) output ho.continuous hob (W₁ i) (retarded i)
      hD hrLp hball (hmem i) hbudget (hbound i) χ₂ χ₃ hχ₂ball Vobs power (h i) (hKloc i)
    have hdecomp : cutObs (observation (corrected i)) =
        ((-1 : ℝ)^power) • cutObs (observation (rem i)) +
          ∑ j ∈ Finset.range power, ((-1 : ℝ)^j) • cutObs (observation ((Krecut i^j) (u i))) := by
      have he := congrArg cutObs hexp
      simp only [map_sub, map_sum, map_smul] at he
      exact eq_add_of_sub_eq he
    obtain ⟨hsm, hsb⟩ := signed_sum_bound G s power
      (fun j ↦ cutObs (observation ((Krecut i^j) (u i)))) C (A i*(ρ i)^(-accuracy))
      (fun j _ ↦ (hc j i).1)
      (fun j _ ↦ by simpa only [mul_assoc] using (hc j i).2)
    have hrm := (G.level s).smul_mem ((-1 : ℝ)^power) (hobsrem i).1
    change cutObs (observation (corrected i)) ∈ G.level s ∧
      G.gradeNorm s (cutObs (observation (corrected i))) ≤ _
    rw [hdecomp]
    refine ⟨(G.level s).add_mem hrm hsm, (gradeNorm_add_le G hrm hsm).trans ?_⟩
    rw [G.gradeNorm_neg_one_pow_smul s power (hobsrem i).1]
    exact (add_le_add (hobsrem i).2 hsb).trans_eq (by ring)
  intro accuracy
  obtain ⟨C, hC, hc⟩ := htail accuracy
  refine ⟨C, hC, ?_⟩
  intro i
  obtain ⟨hm, hn⟩ := observed_core_sobolev_bound hD Vobs Wcore hVobs hWcore hWV
    χobs hχobsCore (pairedSource f hK L₀ output ho.continuous hob - 1)
    (corrected i) s (hc i).1
  refine ⟨hm, ?_⟩
  rw [restrictionSobolevScale_gradeNorm hWcore hm]
  apply hn.trans
  have hb := (hc i).2
  rw [restrictionSobolevScale_gradeNorm hVobs (hc i).1] at hb
  exact hb

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
