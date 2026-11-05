module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.ReducedReal
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ObservedSourceInputs
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedSampledSource

/-!
# Initial localization of the original sampled signed products

The sampling witness supplies the SAME normalized phase and true beat.
The joint Hamilton jets supply its higher phase bounds via the short-chord
estimate. The original complete product amplitudes, half stress contraction,
and both cutoffs are retained. Only the minus diagonal is omitted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.InitialSignedChainSource

open InitialSourceLocalization

open SignedPairs InnerProductSpace SignedProductEstimates ResponseTransfer.RetainedFactors
open FiniteChain.Graph JanetCartan.Localization LocalSobolev
open ResponseSourceExtension ResponseTransfer.SourceNegative Sampling.BackgroundModulation
open ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic.RetardedLocalization

variable {d N : ℕ} {G ι : Type*}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- Joint jets of the original phase pay the mixed parameter derivative
before division by the true beat (`app:ch_pairs:setup:pairs-lag`). -/
theorem normalized_sample_pair_joint_jets_le
    {Z : G → Set (Euclidean 3)} (hZ : ∀ g, Convex ℝ (Z g))
    (q : Pair G (Euclidean 3) Z) (Φ : G → E × Euclidean 3 → ℝ)
    (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g)) {L : ℝ} (hL : 1 ≤ L)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) (x : E)
    (hjoint : ∀ g z, z ∈ Z g → ∀ m,
      ‖iteratedFDeriv ℝ m (Φ g) (x,z)‖ ≤ P m * L^(m-2))
    (m : ℕ) :
    ‖iteratedFDeriv ℝ (m+1)
      (fun y ↦ q.vector (fun g z ↦ Φ g (y,z)) / q.beat) x‖ ≤
        (2 * (P (m+1)+P (m+2))) * L^m := by
  have hs g z : ContDiff ℝ ∞ (fun y : E ↦ Φ g (y,z)) :=
    (hΦ g).comp (contDiff_id.prodMk contDiff_const)
  apply (norm_iteratedFDeriv_normalized_signed_pair_phase_le hZ q
    (fun g z y ↦ Φ g (y,z))
    (fun g z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ (m+1)
      (fun y : E ↦ Φ g (y,w)) x) z)
    (add_nonneg (hP _) (hP _)) (zero_le_one.trans hL)
    (fun g z _ ↦ (hs g z).contDiffAt.of_le (by simp)) ?_ ?_ ?_).trans_eq
      (by rw [Nat.add_sub_cancel])
  · intro g z hz
    apply (primary_phase_spatial_jet_le_joint (Φ g) (hΦ g) x z (m+1)).trans
    apply (hjoint g z hz (m+1)).trans
    apply mul_le_mul (le_add_of_nonneg_right (hP _))
      (pow_le_pow_right₀ hL (by omega))
      (pow_nonneg (zero_le_one.trans hL) _) (add_nonneg (hP _) (hP _))
  · intro g z _
    exact ((contDiff_parameter_spatial_phase_jet (Φ g) (hΦ g) (m+1) x).differentiable
      (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  · intro g z hz
    apply (norm_parameter_spatial_phase_jet_le_joint (Φ g) (hΦ g) (m+1) x z).trans
    apply (hjoint g z hz (m+2)).trans
    simp only [show m+2-2=m by omega, Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hP _))
      (pow_nonneg (zero_le_one.trans hL) _)


/-- Fix the original sampled pair, true frequency and L² datum before every
first-mask choice (`app:ch_pairs:prop:pairs-lag-sum`,
`app:ch_regular:eq:source-tail`). The scale threshold uses only the original
separation and slow-scale comparison. Bounds may depend on the later mask
profile and plateau width, but precede all samples and histories. Actual joint
phase, row and amplitude profiles are the retained-history/canonical producer
inputs; no localization error is assumed. The low norm and admission come from
`exists_signed_product_source_chain_low_constant`, independently of masks.
Consumer: the original-history source input of the observed residual chain. -/
theorem exists_sampled_source_before_firstMask
    (K : Set E) (hK : IsCompact K) (Bgrad : ℝ)
    {csep : ℝ} (hcsep : 0 < csep) (Cscale : ℝ)
    (P X Y CQ C : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j)
    (hX : ∀ j, 0 ≤ X j) (hY : ∀ j, 0 ≤ Y j)
    (hCQ : ∀ j, 0 ≤ CQ j) (hC : ∀ j, 0 ≤ C j) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∃ Csource : ℝ, 0 ≤ Csource ∧
    ∃ B : {δ : ℝ // 0 < δ} → {D : ℕ → ℝ // ∀ j, 0 ≤ D j} → ℕ → ℝ → ℝ,
      (∀ δ D s accuracy, 0 ≤ B δ D s accuracy) ∧
    ∀ (G ι : Type*) (Hull : Set (E × E)),
    ∀ (U : Set E), IsOpen U → K ⊆ U →
    ∀ (χ ψ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
      (Φ : G → E × Euclidean 3 → ℝ) (Z : G → Set (Euclidean 3)) (R L sep : ℝ),
    (∀ g, Convex ℝ (Z g)) → (∀ g, ContDiff ℝ ∞ (Φ g)) →
    ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
    tsupport χ ⊆ K → 1 ≤ L → Rmin ≤ R → 0 < sep → sep ≤ 1 →
    csep * R^(-separationExponent) ≤ sep → L ≤ Cscale * R^(1+meanSlack) →
    (∀ y ∈ U, ∀ p : Pair G (Euclidean 3) Z,
      ‖p.vector (fun g z ↦ gradient (fun x ↦ Φ g (x,z)) y)‖ ≤ Bgrad*p.beat) →
    (∀ y ∈ K, ∀ p : Pair G (Euclidean 3) Z,
      (y, p.beat⁻¹ • p.vector (fun g z ↦ gradient (fun x ↦ Φ g (x,z)) y)) ∈ Hull) →
    (∀ y ∈ K, ∀ g z, z ∈ Z g → ∀ j,
      ‖iteratedFDeriv ℝ j (Φ g) (y,z)‖ ≤ P j * L^(j-2)) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j χ y‖ ≤ X j * L^j) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j ψ y‖ ≤ Y j * L^j) →
    (∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j Q y‖ ≤ CQ j * L^j) →
    ∀ (group : ι → G) (z : ι → Euclidean 3), (∀ i, z i ∈ Z (group i)) →
    (∀ i j, i ≠ j → group i = group j → sep ≤ ‖z i-z j‖) →
    ∀ A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ,
    (∀ i, ContDiffOn ℝ ∞ (A i) U) →
    (∀ i y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (A i) y‖ ≤ C j * L^j) →
    ∀ (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
    let θ := fun i y ↦ R^carrierExponent * Φ (group i) (y,z i)
    let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource ψ
      (AmbientResponse.stressSource Q (fun x ↦ χ x •
        (if minus then ProductSum.minusSource θ A i j x else ProductSum.plusSource θ A i j x))) y)
    ∃ p : Pair G (Euclidean 3) Z, sep ≤ p.beat ∧
      (∀ v : G → Euclidean 3 → ℝ, p.vector v =
        if minus then v (group i) (z i)-v (group j) (z j)
          else v (group i) (z i)+v (group j) (z j)) ∧
    ∃ hg : MemLp g 2 volume, ‖hg.toLp g‖ ≤ Csource ∧
    2 ≤ R^carrierExponent*p.beat ∧
    ∀ (δ : {δ : ℝ // 0 < δ}) (D : {D : ℕ → ℝ // ∀ j, 0 ≤ D j})
      (m : LocalizerSymbol (d+1)), ContDiff ℝ ∞ m → HasCompactSupport m →
    (∀ j p, ‖iteratedFDeriv ℝ j m p‖ ≤ D.val j) →
    (∀ y ξ, m (y, -ξ) = m (y, ξ)) →
    cthickening δ.val Hull ⊆ interior {p | m p = 1} →
    ∀ (M : H →L[ℂ] H),
    (∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer (R^carrierExponent*p.beat) m (fun y ↦ (v y).ofLp) x)) →
    ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W →
    ∀ (s : ℕ) (accuracy : ℝ),
    let h := (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g
    let e := h - localRealCompression hW W M h
    e ∈ (restrictionSobolevScale W RV hW).level s ∧
      (restrictionSobolevScale W RV hW).gradeNorm s e ≤
        B δ D s accuracy * (R^carrierExponent*p.beat)^(-accuracy) := by
  obtain ⟨Rmin, hRmin, hscale⟩ := exists_signed_pair_scale_threshold hcsep Cscale
  let Ppair := fun j ↦ 2 * (P (j+1) + P (j+2))
  have hPpair j : 0 ≤ Ppair j := mul_nonneg (by norm_num) (add_nonneg (hP _) (hP _))
  obtain ⟨Csource, hCsource, hlow⟩ :=
    exists_signed_product_source_chain_low_constant (N := N) hK X Y CQ C hX hY hCQ hC
  choose B hB hb using fun (δ : {δ : ℝ // 0 < δ})
      (D : {D : ℕ → ℝ // ∀ j, 0 ≤ D j}) s accuracy ↦
    exists_reducedSigned_local_initialSource_accuracy_constants (N := N)
      K hK δ.val Bgrad δ.property Ppair D.val X Y CQ C hPpair D.property hX hY hCQ hC s
      (σ := 1/1000) (by norm_num) accuracy
  refine ⟨Rmin, hRmin, Csource, hCsource, B, hB, ?_⟩
  intro G ι Hull U hU hKU χ ψ Q Φ Z R L sep hZ hΦ hχ hψ hQ
    hχK hL hR hsep hsepOne hsepStage hslow hband hgraph hjoint hχjet hψjet hQjet
    group z hz hsample A hA hAjet minus i j hdiag θ g
  obtain ⟨p, hpsep, hp⟩ : ∃ p : Pair G (Euclidean 3) Z, sep ≤ p.beat ∧
      ∀ v : G → Euclidean 3 → ℝ, p.vector v = if minus then
        v (group i) (z i)-v (group j) (z j) else v (group i) (z i)+v (group j) (z j) := by
    cases minus with
    | false =>
      obtain ⟨p, hpbeat, hp⟩ := sample_plus_represented_with_beat («E» := ℝ) group z hz i j
      exact ⟨p, hpbeat ▸ hsepOne, hp⟩
    | true =>
      obtain ⟨p, hpsep, _, _, hp⟩ := sample_minus_represented_with_beat
        («E» := ℝ) hsep hsepOne group z hz hsample (hdiag rfl)
      exact ⟨p, hpsep, hp⟩
  refine ⟨p, hpsep, hp, ?_⟩
  have hRp : 0 < R := (by norm_num : (0:ℝ) < 2).trans_le (hRmin.trans hR)
  have hlam : 0 < R^carrierExponent := Real.rpow_pos_of_pos hRp _
  have hfrequency : csep*(R^carrierExponent*R^(-separationExponent)) ≤
      R^carrierExponent*p.beat := by
    calc
      _ = R^carrierExponent*(csep*R^(-separationExponent)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsepStage.trans hpsep) hlam.le
  obtain ⟨hρ, hslow'⟩ := hscale R hR _ L hfrequency hslow
  let φ := fun y ↦ p.vector (fun g z ↦ Φ g (y,z)) / p.beat
  have hs g z : ContDiff ℝ ∞ (fun y : E ↦ Φ g (y,z)) :=
    (hΦ g).comp (contDiff_id.prodMk contDiff_const)
  have hφ : ContDiff ℝ ∞ φ := by
    apply ContDiff.div_const
    cases p with
    | difference g z w hne => exact (hs g z).sub (hs g w)
    | sum g z w => exact (hs g z).add (hs g w)
    | cross g h hne z w s t hs' ht =>
      exact ((hs g z).const_smul s).add ((hs h w).const_smul t)
  have hupper y (hy : y ∈ U) : ‖fderiv ℝ φ y‖ ≤ Bgrad :=
    (normalized_signed_pair_phase_geometry (a := 0) p (fun g z y ↦ Φ g (y,z))
      (fun g z _ ↦ ((hs g z).differentiable (by simp)).differentiableAt)
      ⟨by simp,
        hband y hy p⟩ (K := univ) (mem_univ _)).2.1
  have hgrad y : gradient φ y =
      p.beat⁻¹ • p.vector (fun g z ↦ gradient (fun x ↦ Φ g (x,z)) y) := by
    apply (toDual ℝ E).injective
    rw [toDual_gradient, fderiv_normalized_signed_pair_phase p (fun g z y ↦ Φ g (y,z))
      (fun g z _ ↦ ((hs g z).differentiable (by simp)).differentiableAt), map_smul]
    congr 1
    cases p <;> simp only [Pair.vector, map_sub, map_add, map_smul, toDual_gradient]
  have hχglobal : ContDiff ℝ ∞ χ :=
    JanetCartan.Localization.contDiff_of_contDiffOn_support_neighborhood hU hχ (hχK.trans hKU)
  obtain ⟨hg, hgnorm, _⟩ := hlow U hU L hL χ ψ Q hχglobal hχK (hχK.trans hKU)
    hψ hQ hχjet hψjet hQjet ι θ A i j
    ((contDiff_const.mul (hs (group i) (z i))).contDiffOn)
    ((contDiff_const.mul (hs (group j) (z j))).contDiffOn)
    (hA i) (hA j) (hAjet i) (hAjet j) minus
  refine ⟨hg, hgnorm, hρ, ?_⟩
  intro δ D m hm hmc hmjet heven hplateau M hM W hW hχW s accuracy
  have hinitial s accuracy := hb δ D s accuracy m hm hmc hmjet heven Hull hplateau U hU hKU
    χ ψ Q (A i) (A j) hχ hψ hQ (hA i) (hA j) hχK L hL hχjet hψjet hQjet
    (hAjet i) (hAjet j) (fun _ ↦ φ) (fun _ ↦ R^carrierExponent*p.beat)
    (fun _ ↦ hφ.contDiffOn) (fun _ ↦ (by norm_num : (1:ℝ) ≤ 2).trans hρ)
    (fun _ ↦ hslow') (fun _ y hy ↦ by rw [hgrad]; exact hgraph y (hχK hy) p)
    (fun _ ↦ hupper)
    (fun _ y hy j _ ↦ normalized_sample_pair_joint_jets_le hZ p Φ hΦ hL P hP y
      (hjoint y (hχK hy)) j) minus
  obtain ⟨hf, _⟩ := hinitial 0 0
  let a := fun y ↦ ψ y • ((1/2:ℝ) • complexStressContraction (Q y)
    (if minus then symmetricBilinearTensor (A i y) ((A j y).map conj)
      else symmetricBilinearTensor (A i y) (A j y)))
  let f := modulatedSource χ φ a (R^carrierExponent*p.beat)
  let u := hf.toLp f
  have hφeq : (fun y ↦ (if minus then θ i y-θ j y else θ i y+θ j y) /
      (R^carrierExponent*p.beat)) = φ := by
    funext y
    dsimp only [φ, θ]
    rw [hp]
    cases minus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> field_simp
  have he : g = fun y ↦ euclideanRealPart (f y) := by
    cases minus
    · simp only [Bool.false_eq_true, ↓reduceIte] at hφeq
      exact (cutoff_stressSource_plus_eq_real_modulatedSource Q χ ψ θ A i j
        (mul_pos hlam p.beat_pos).ne').trans (by rw [hφeq]; rfl)
    · simp only [↓reduceIte] at hφeq
      exact (cutoff_stressSource_minus_eq_real_modulatedSource Q χ ψ θ A i j
        (mul_pos hlam p.beat_pos).ne').trans (by rw [hφeq]; rfl)
  have hrep : l2RealPart volume u =ᵐ[volume] g := by
    rw [he]
    filter_upwards [euclideanRealPart.coeFn_compLpL u, hf.coeFn_toLp] with y hr hu
    exact hr.trans (congrArg euclideanRealPart hu)
  have hloc : (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g =
      l2RealPart (volume.restrict W) (restrictL2 W u) := by
    apply Lp.ext
    filter_upwards [(hg.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp,
      euclideanRealPart.coeFn_compLpL (restrictL2 W u), restrictL2_coeFn W u,
      ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL u), ae_restrict_of_ae hrep]
      with y hg' hr hl hgr hgR
    change (l2RealPart (volume.restrict W) (restrictL2 W u)) y = _ at hr
    change (l2RealPart volume u) y = _ at hgr
    rw [hg', hr, hl, ← hgr, hgR]
  dsimp only
  rw [hloc]
  obtain ⟨_, hbound⟩ := hinitial s accuracy
  simpa only [one_smul] using hbound M hM W hW hχW 1 (by simp)


end JanetCartan.InitialSignedChainSource
