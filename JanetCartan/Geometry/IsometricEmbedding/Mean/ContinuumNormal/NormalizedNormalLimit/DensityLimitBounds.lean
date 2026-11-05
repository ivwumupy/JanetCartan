module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourceAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SmoothAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityLimit

/-!
# Uniform bounds for both zero-scale density amplitudes

The genuine source limit retains both divided ODE footpoints. The existing
frozen gap uses the distinct origin multiplier. Their spatial comparison needs
uniform absolute bounds through μ+1 on the same geometry, in addition to the
source-to-limit small difference. This module derives those bounds from the
canonical zero-slice coefficients and the original-domain source transport.
No amplitude or operator bound is a premise, and no mask support is removed.

Consumer: ActualConstruction.exists_sourceDensityLimit_frozen_error_constant.
The common-family geometry and literal normal realizations remain with the
normalized selection and normal variation producers. Sources:
app:ch_background:prop:bg-normalized, bg-Nsigma,
app:ch_background:eq:bg-full-complex-amplitude, and bg-frame, Steps 2–3.
-/

@[expose] public noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs.WideDensity CarrierVariation.AmplitudeDifference
open CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs NullTransport NormalizedBackground.SourceGeometry FrozenModel
open AmplitudeBound

/-- The original-domain weighted primitive estimate gives absolute full
amplitude bounds, uniformly before the positive density. Apply the existing
shell-difference transfer against zero normal coefficients; no density or
mask is replaced. The physical Fourier conversion and reflection occur once.
Consumer: the two zero-limit bounds below; sources:
app:ch_background:eq:bg-full-complex-amplitude and bg-real-symbol. -/
private theorem exists_sqrtFootpoint_fullAmplitude_bounds
    {n N : ℕ} (D : CoefficientNormCharts n) (a : Coefficients n N)
    (J : InputVariables n → ℝ) (u : Variables n × Euclidean 2 → SliceVariable n)
    (Fwd : InputVariables n → Variables n × Euclidean 2)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hL : IsCompact L) (hconv : Convex ℝ L)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    (hreg : PrimitiveRegularity a J W) (hgap : ∀ p ∈ K, δ ≤ |J p|)
    (s : ℕ) (hreserve : 2 * (n + 1) ≤ s)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hcoeff : D.Controls (s + 1) M₀ (M₀ + 1) 1 a)
    (hu : ContDiffOn ℝ ∞ u Ω) (huK : MapsTo (inverseCoordinates u) Q K)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, Fwd (inverseCoordinates u p) = p)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    (hbuffer : closure (Fwd '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    (hzero : ∀ t, t ≤ 1 → a.high t = 0) (htail : ∀ t, 2 ≤ t → a.high t = 1)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (huScale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJScale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p))
    (hshell : ∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ z ∈ S,
      (p, z) ∈ closure (Fwd '' Zmask) → (p, z) ∈ Q)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1) × Euclidean 3)
    (hY : ∀ side, ContDiffOn ℝ ∞ (Y ∘ densityEndpoint side) W)
    (hYL : ∀ side, MapsTo (Y ∘ densityEndpoint side) W L) :
    ∃ B > (0 : ℝ), ∀ d₀ : ℕ, s + 1 ≤ d₀ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      (∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := {a with normal := fun p ↦ Real.sqrt (1 + v (Y p)) • a.normal p}
      ContDiff ℝ ∞ (Function.uncurry (fullComplexMatrixAmplitude av J u Ω S)) ∧
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude av J u Ω S)) ∧
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude av J u Ω S ξ z i j) s B ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude av J u Ω S ξ z i j) s (4 * B) := by
  let g := fun side ↦ Y ∘ densityEndpoint side ∘ inverseCoordinates u
  let M := M₀ + cNorm K s J + cNorm Q s (inverseCoordinates u) +
    cNorm Q s (g false) + cNorm Q s (g true)
  have hm : M₀ ≤ M ∧ cNorm K s J ≤ M ∧ cNorm Q s (inverseCoordinates u) ≤ M ∧
      ∀ side, cNorm Q s (g side) ≤ M := by
    have h₁ := cNorm_nonneg K s J
    have h₂ := cNorm_nonneg Q s (inverseCoordinates u)
    have h₃ := cNorm_nonneg Q s (g false)
    have h₄ := cNorm_nonneg Q s (g true)
    dsimp only [M]
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    intro side
    cases side <;> linarith
  have hc : D.Controls (s + 1) M (M + 1) 1 a := by
    have up {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup G] [NormedSpace ℝ G]
        {D' : PrimitiveNormChart E} {f : E → G}
        (hf : D'.Controls (s + 1) M₀ (M₀ + 1) 1 f) :
        D'.Controls (s + 1) M (M + 1) 1 f :=
      ⟨hf.smooth, hf.low.trans hm.1, hf.high.trans (by simpa using hm.1)⟩
    exact ⟨up hcoeff.measurement, up hcoeff.angular, up hcoeff.high,
      up hcoeff.normal, up hcoeff.reduced⟩
  have hc' : D.Controls s M (M + 1) 1 a := by
    have down {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup G] [NormedSpace ℝ G]
        {D' : PrimitiveNormChart E} {f : E → G} (hf : D'.Controls (s + 1) M (M + 1) 1 f) :
        D'.Controls s M (M + 1) 1 f :=
      ⟨hf.smooth, hf.low, by
        have hnorm := cNorm_mono_order (s := D'.carrier) (f := f) (Nat.le_succ s)
        have hhigh := hf.high
        linarith⟩
    exact ⟨down hc.measurement, down hc.angular, down hc.high, down hc.normal, down hc.reduced⟩
  have hg (side : Bool) : ContDiffOn ℝ ∞ (g side) Ω :=
    (hY side).comp (inverseCoordinates_contDiffOn hu) hmap
  have hgr (side : Bool) : MapsTo (g side) Ω L := (hYL side).comp hmap
  obtain ⟨B₀, hB₀, hweighted⟩ := exists_rescaled_weighted_inputDensity_sub_le
    (N := N) D hreg.high htail hK hW hKW hQ hΩ hQΩ hL hconv hη hδ hfreq hrange
      hreg.jacobian hgap s (hM₀.trans hm.1) hm.2.1
  obtain ⟨B, hB, hfull⟩ := exists_fullAmplitude_sub_bounds_of_supported_shell
    (N := N) s hreserve hS hQ hCupper hℓ hlow hB₀.le
  refine ⟨B, hB, ?_⟩
  intro d₀ horder v hv hvm hpos av
  let az : Coefficients n N := {a with normal := 0}
  have hav : PrimitiveRegularity av J W :=
    primitiveRegularity_sqrtFootpoints hreg Y hY hYL v hv hpos
  have haz : PrimitiveRegularity az J W := {hreg with
    leftNormal := contDiffOn_const
    rightNormal := contDiffOn_const}
  have hdensityZero (t : ℝ) : inputDensity (rescaledCoefficients az t) J = 0 := by
    funext p
    ext i j
    simp [inputDensity, inputWeight, rescaledCoefficients, az]
  have hampZero : amplitude az J u Ω S = 0 := by
    funext p
    apply integral_eq_zero_of_ae
    filter_upwards [] with z
    by_cases hz : (p, z) ∈ Ω <;>
      simp [extendedDensity, hz, inputDensity, inputWeight, az]
  have hcomplexZero : fullComplexMatrixAmplitude az J u Ω S = 0 := by
    funext ξ z
    ext i j
    simp [fullComplexMatrixAmplitude, hampZero]
  have hreflectZero : fullReflectedMatrixAmplitude az J u Ω S = 0 := by
    funext ξ z
    rw [fullReflectedMatrixAmplitude_eq_complex_add_reflection, hcomplexZero]
    simp
  have hsmooth := (amplitude_smooth_and_derivatives_of_punctured_buffer av J u Fwd
    hΩ hav hu hmap hright hmask hbuffer hzero hCupper hℓ hlow hupper hS).1
  have hphysical := fullAmplitudes_contDiff_of_transportAmplitude av J u Ω S hsmooth
  refine ⟨hphysical.1, hphysical.2, ?_⟩
  have hb := hfull ![av, az] (fun _ ↦ J) (fun _ ↦ u) (fun _ ↦ Fwd) Ω
    (fun _ ↦ W) (fun _ ↦ Zmask) 1 zero_le_one hΩ hQΩ
    (by intro i; fin_cases i <;> assumption)
    (fun _ ↦ hu) (fun _ ↦ hmap) (fun _ ↦ hright)
    (by intro i; fin_cases i <;> exact hmask) (fun _ ↦ hbuffer)
    (by intro i; fin_cases i <;> exact hzero) (fun _ ↦ hupper)
    hcone (fun _ ↦ huScale) (fun _ ↦ hJScale)
    (fun p hp z hz hmem ↦ hshell p hp z hz (hmem.elim id id)) ?_
  · intro i j
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      hcomplexZero, hreflectZero, Pi.zero_apply, Matrix.zero_apply, sub_zero, mul_one] using hb i j
  · intro t ht
    have he : (fun p ↦ inputDensity (rescaledCoefficients av t) J (inverseCoordinates u p))
        =ᶠ[𝓝ˢ Q] (fun p ↦ densityPair v g p •
          inputDensity (rescaledCoefficients a t) J (inverseCoordinates u p)) := by
      filter_upwards [hΩ.mem_nhdsSet.mpr hQΩ] with p hp
      exact inputDensity_sqrtFootpoints (rescaledCoefficients a t) J Y v
        (inverseCoordinates u p) (fun side ↦ (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
          (hpos _ (hgr side hp)))
    have heNorm := GeometricProfile.cNorm_eq_of_eventuallyEq
      (fun p hp ↦ he.filter_mono (nhds_le_nhdsSet hp)) s
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      hdensityZero, Pi.zero_apply, sub_zero, mul_one]
    rw [heNorm]
    exact (hweighted a a J u u g g 0 le_rfl rfl rfl hc' hc hreg.jacobian hgap hm.2.1
      hu hu huK huK hm.2.2.1 hm.2.2.1
      (fun side p hp ↦ (hg side).contDiffAt (hΩ.mem_nhds (hQΩ hp)))
      (fun side p hp ↦ (hg side).contDiffAt (hΩ.mem_nhds (hQΩ hp)))
      (fun side ↦ (hgr side).mono_left hQΩ) (fun side ↦ (hgr side).mono_left hQΩ)
      hm.2.2.2 hm.2.2.2
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun _ ↦ by simp) d₀ horder v hv hvm t ht).1

/-- Uniform full-amplitude bounds for the genuine divided-footpoint limit and
the distinct origin-frozen multiplier, on the SAME unit coefficients, inverse,
Jacobian and complete masks. Both smoothness and the reserve μ+1 are proved
from primitive bounds. The common bound precedes the original density class;
the scalar domain and its μ+14 low hypothesis are unchanged.

The supplied unit zero-slice controls are produced by
NormalizedCarrierProfiles.exists_normalizedCarrierData_all_order_controls;
the conic geometry is supplied by normalized selection and normal variation.
Consumer: ActualConstruction.exists_sourceDensityLimit_frozen_error_constant,
which needs these two absolute bounds in addition to the source-to-limit
small difference. Sources: app:ch_background:prop:bg-normalized,
app:ch_background:prop:bg-frame, and bg-full-complex-amplitude. -/
private theorem exists_source_density_limit_reflected_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (NormalizedBackground.SourceGeometry.sourceTransportFlow Y σ))
        (ball 0 R ×ˢ V) (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (a : Coefficients n N)
    (J : InputVariables n → ℝ) (u : Variables n × Euclidean 2 → SliceVariable n)
    (Fwd : InputVariables n → Variables n × Euclidean 2)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    (hreg : PrimitiveRegularity a J W) (hgap : ∀ p ∈ K, δ ≤ |J p|)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : D.Controls (2 * (n + 1) + 2) M (M + 1) 1 a)
    (hu : ContDiffOn ℝ ∞ u Ω) (huK : MapsTo (inverseCoordinates u) Q K)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, Fwd (inverseCoordinates u p) = p)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    (hbuffer : closure (Fwd '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    (hhighZero : ∀ t, t ≤ 1 → a.high t = 0) (hhighOne : ∀ t, 2 ≤ t → a.high t = 1)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (huScale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJScale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p))
    (hshell : ∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ z ∈ S,
      (p, z) ∈ closure (Fwd '' Zmask) → (p, z) ∈ Q)
    (hend : ∀ side, MapsTo (densityEndpoint side) W (ball (0 : Euclidean n) R ×ˢ V))
    (Rbox : ℝ) (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox) :
    let foot : Bool → Euclidean n × CarrierParameter → Euclidean (n - 1) × Euclidean 3 :=
      fun frozen p ↦ if frozen then (0, parameter p.2) else
        sourceDensityFootpointExtension T Y (0, p)
    ∃ B > (0 : ℝ), ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (2 * (n + 1) + 14) v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      ∀ frozen : Bool,
      let av := {a with normal := fun p ↦ Real.sqrt (1 + v (foot frozen p)) • a.normal p}
      let b := fullReflectedMatrixAmplitude av J u Ω S
      ContDiff ℝ ∞ (Function.uncurry b) ∧
      (∀ ξ i j, SupportedInCenteredBox Rbox (fun z ↦ b ξ z i j)) ∧
      ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1) + 1) B := by
  intro foot
  obtain ⟨hfootSmooth, hfootRange⟩ := source_footpoint_original_domain_regular T hR hV hY
    hzero hparam hs₀ hsource 0 ⟨le_rfl, le_min hs₀.le (by norm_num)⟩
  have hsmall : closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16) ⊆
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8) :=
    closedBall_subset_closedBall (by linarith)
  have hfoot (frozen side : Bool) :
      ContDiffOn ℝ ∞ (foot frozen ∘ densityEndpoint side) W ∧
      MapsTo (foot frozen ∘ densityEndpoint side) W
        (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) := by
    cases frozen
    · exact ⟨hfootSmooth.comp (densityEndpoint_contDiff side).contDiffOn (hend side),
        ((hfootRange.comp (hend side)).mono_right hsmall)⟩
    · refine ⟨?_, ?_⟩
      · exact (contDiff_const.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn.comp
          (densityEndpoint_contDiff side).contDiffOn (mapsTo_univ _ _)
      · intro p hp
        have hm := hfootRange (show ((0 : Euclidean n), (densityEndpoint side p).2) ∈
            ball (0 : Euclidean n) R ×ˢ V from ⟨mem_ball_self hR, (hend side hp).2⟩)
        have he : sourceDensityFootpointExtension T Y
            (0, ((0 : Euclidean n), (densityEndpoint side p).2)) =
            (0, parameter (densityEndpoint side p).2) := by
          rw [ActualConstruction.sourceDensityFootpointExtension_zero_eq_differential]
          apply Prod.ext
          · ext j
            simp
          · rfl
        dsimp only at hm
        rw [he] at hm
        exact hsmall hm
  have hb (frozen : Bool) := exists_sqrtFootpoint_fullAmplitude_bounds
    D a J u Fwd hK hW hKW hQ hΩ hQΩ (isCompact_closedBall _ _) (convex_closedBall _ _)
    hS hη hδ hfreq hrange hreg hgap (2 * (n + 1) + 1) (by omega) hM hcoeff
    hu huK hmap hright Zmask hmask hbuffer hhighZero hhighOne hCupper hℓ hlow hupper
    hcone huScale hJScale hshell (foot frozen) (fun side ↦ (hfoot frozen side).1)
      (fun side ↦ (hfoot frozen side).2)
  choose B hB hbound using hb
  refine ⟨4 * (B false + B true), mul_pos (by norm_num) (add_pos (hB false) (hB true)), ?_⟩
  intro v hv hvm hpos frozen av b
  obtain ⟨_, hsm, hentry⟩ := hbound frozen (2 * (n + 1) + 14) (by omega) v hv hvm hpos
  refine ⟨hsm, fullReflectedMatrixAmplitude_supportedInCenteredBox av J u Ω S Rbox hsupport, ?_⟩
  intro i j ξ is his z
  apply ((hentry i j).2 ξ is his z).trans
  cases frozen <;> linarith [hB false, hB true]

/-- On the supplied normalized zero slice, derive a common full reflected
amplitude bound through μ+1 for BOTH the divided-footpoint density and the
origin-frozen density. The canonical source-coefficient theorem supplies
all coefficient bounds; original-domain source transport supplies both
density ranges. No amplitude smoothness or derivative bound is a premise.

The remaining inputs are the same whole-mask inverse geometry supplied by
normalized selection and normal variation. Consumer:
ActualConstruction.exists_sourceDensityLimit_frozen_error_constant, before
the local coercivity radius is selected. The density reserve stays μ+14.
Sources: app:ch_background:prop:bg-normalized, bg-Nsigma,
app:ch_background:eq:bg-full-complex-amplitude, and bg-frame, Steps 2–3. -/
theorem exists_sourceDensityLimit_reflected_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ t, t ≤ 1 → high t = 0) (hhighOne : ∀ t, 2 ≤ t → high t = 1)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    (hu : ContDiffOn ℝ ∞ u Ω) (huK : MapsTo (inverseCoordinates u) Q K)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (huScale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) :
    let a := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0)
      (FixedCutoffs.physical hr 1)
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) Z
    let foot : Bool → Euclidean n × CarrierParameter → Euclidean (n - 1) × Euclidean 3 :=
      fun frozen p ↦ if frozen then (0, parameter p.2) else
        sourceDensityFootpointExtension T Y (0, p)
    ContDiffOn ℝ ∞ J W → (∀ p ∈ W, J p ≠ 0) → (∀ p ∈ K, δ ≤ J p) →
    (∀ p ∈ Ω, transportAveragedGradient Z (inverseCoordinates u p) = p.1.2.2) →
    (closure (augmentedTransportGradient Z '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
    (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
    (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ z ∈ S,
      (p, z) ∈ closure (augmentedTransportGradient Z '' Zmask) → (p, z) ∈ Q) →
    ∃ B > (0 : ℝ), ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (2 * (n + 1) + 14) v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      ∀ frozen : Bool,
      let av := {a with normal := fun p ↦ Real.sqrt (1 + v (foot frozen p)) • a.normal p}
      let b := fullReflectedMatrixAmplitude av J u Ω S
      ContDiff ℝ ∞ (Function.uncurry b) ∧
      (∀ ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ b ξ z i j)) ∧
      ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1) + 1) B := by
  intro a Z J foot hJ hJne hgap hright hbuffer hJScale hshell
  obtain ⟨M, hM, _, _, _, hcoeff, _⟩ := exists_normalizedCarrierData_coefficient_controls
    T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high (FixedCutoffs.physical hr 1)
    hP hseed hF hi hrank hR hRT hRU hV hVP hb D hD
    (FixedCutoffs.physical hr 1).contDiff.contDiffOn ha.contDiffOn hh.contDiffOn
      (2 * (n + 1) + 1)
  have hc : D.Controls (2 * (n + 1) + 2) M (M + 1) 1 a := hcoeff
  have hreg : PrimitiveRegularity a J W := {
    leftMeasurement := (FixedCutoffs.physical hr 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
    rightMeasurement := (FixedCutoffs.physical hr 1).contDiff.comp_contDiffOn contDiffOn_fst.snd
    angular := ha
    high := hh
    leftNormal := hc.normal.smooth.comp (densityEndpoint_contDiff false).contDiffOn (hend false)
    rightNormal := hc.normal.smooth.comp (densityEndpoint_contDiff true).contDiffOn (hend true)
    leftReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
      (densityEndpoint_contDiff false).contDiffOn (hend false)
    rightReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
      (densityEndpoint_contDiff true).contDiffOn (hend true)
    jacobian := hJ
    jacobian_ne_zero := hJne
    covector_ne_zero := hfreqW }
  have hmaskA : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask := by
    dsimp only [a]
    as_aux_lemma => exact hmask
  have hhighEq : a.high = high := by dsimp only [a]; as_aux_lemma => rfl
  have hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * r := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx)))
  exact exists_source_density_limit_reflected_bounds T hR hV hY hzero hparam hL hs₀ hsource
    D a J u (augmentedTransportGradient Z) hK hW hKW hQ hΩ hQΩ hS hη hδ hfreq hrange
    hreg (fun p hp ↦ (hgap p hp).trans (le_abs_self _)) hM.le hc hu huK hmap
    (augmentedTransportGradient_inverseCoordinates Z u hright)
    Zmask hmaskA hbuffer (hhighEq.symm ▸ hhighZero) (hhighEq.symm ▸ hhighOne)
    hCupper hℓ hlow hupper hcone huScale hJScale hshell
    (fun side p hp ↦ hD (hend side hp)) (4 * r) hsupport

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
