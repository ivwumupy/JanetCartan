module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.SobolevNorm
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.NormComparison

/-!
# The physical raw Sobolev slice bound from original primitive jets

This completes the deduction of `app:ch_waves:eq:individual-raw-slice` from
the original buffered phase charts and joint coefficient grades. The actual
canonical WKB/history family must supply those primitive inputs; it is not
constructed or assumed successful here. The integral, original wide-input
norm, both quadratures, Frobenius norm and physical Lebesgue measure are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds
open NormalComparison RawInputPartition SingleChannel ActualCarriers.FrozenPhaseReference

variable {d m : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "E" => Euclidean (d + 1)
local notation "Qₚ" => ℝ × X × Y
local notation "Mat" => Matrix (Fin m) (Fin (d + 1)) ℂ

/-- Physical Sobolev slice estimate for the SAME raw integral on arbitrary
original wide-band Hilbert data (`app:ch_waves:eq:individual-raw-slice`).

`exists_rawSliceDifferentiatedOperator` produces the derivative channels from
the displayed original joint jets and `UniformNormalData` phase geometry;
`rawSlice_weightedWideDensity_regular` produces all weak identities from the
same original smooth coefficients. No raw operator bound, differentiated
estimate, weak identity, or Sobolev membership is an input. The Cartesian
whole-space norm counts each multiindex once, with the Frobenius matrix norm.

Constants precede the scales, coefficients, datum and measurement set. The
quantitative orders are finite, through `s + rawSliceJetOrder (d+1) + 1`,
and the reserve is the fixed `Dpr + r_par + 2`. Specializing `L=1` gives every
`K≥1` at the prescribed finite order. The raw-primary parent must instantiate
the retained phase charts, cutoffs and original grades on its SAME canonical
derivative amplitude; the separate zero atom and physical wave are unchanged. -/
theorem exists_rawPhysicalSliceSobolev
    {ξ : E} (sec : AdaptedSection ξ)
    (G : UniformNormalGeometry d (m * (d + 1))) (C : ℕ → ℝ)
    {U : Set E} {V Ω : Set Y} {Q H : Set Qₚ} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hH : IsCompact H) (hHQ : H ⊆ Q)
    (hband : wideBand (d + 1) 0 ⊆ Ω) (ζ : Y) (hζ : ζ ∈ V)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q
      ((adaptedPhysicalCoordinates sec ⁻¹' U) ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (a p bmask : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hbmask : ∀ j, 0 ≤ bmask j) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      ∀ (K L τ : ℝ), 1 ≤ K → 1 ≤ L → L ≤ K → τ ≠ 0 →
      ∀ (χ : E → ℝ) (mask : Y → ℂ) (S : E → Y → ℝ) (A : E → Y → Mat),
      ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      (∀ q, χ (adaptedPhysicalCoordinates sec q) ≠ 0 → q.2 ∈ G.X₀) →
      (∀ x ∈ tsupport χ, ((adaptedPhysicalCoordinates sec).symm x).1 ∈ Ioo t₀ t₁) →
      Measurable mask → ∀ M : ℝ, (∀ η, ‖mask η‖ ≤ M) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V) →
      ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V) →
      let U₀ := adaptedPhysicalCoordinates sec ⁻¹' U
      let S₀ := fun q η ↦ S (adaptedPhysicalCoordinates sec q) η
      let A₀ := fun q η i ↦ matrixChannelEquiv m (d + 1) (A (adaptedPhysicalCoordinates sec q) η) i
      let χ₀ := fun q ↦ χ (adaptedPhysicalCoordinates sec q)
      let mask₀ := fun (j : Fin (cutoffCount K)) (θ : Y) ↦
        (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand (n := d + 1) mask j.val ((2 : ℝ) ^ j.val • θ)
      (∀ j, ContDiffOn ℝ ∞ (mask₀ j) Ω) →
      (∀ j, Function.support (mask₀ j) ⊆ G.D₀) →
      (∀ j, tsupport (mask₀ j) ⊆ Ω) →
      ∀ (Dpr s : ℕ),
      (∀ j, ∀ q ∈ H, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun z : Qₚ ↦ (χ₀ z.2.1 : ℂ) * mask₀ j z.2.2) q‖ ≤ bmask k) →
      (∀ z ∈ U₀ ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (Function.uncurry A₀) z‖ ≤
          a k * L ^ (k + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) →
      (∀ z ∈ U₀ ×ˢ V, ∀ k ≤ s + rawSliceJetOrder (d + 1) + 1,
        ‖iteratedFDeriv ℝ k (fun w : X × Y ↦ fderiv ℝ (S₀ w.1) w.2) z‖ ≤
          p k * L ^ (k - 1 + Dpr - rawSlicePrimitiveReserve (d + 1) Dpr)) →
      (∀ j : Fin (cutoffCount K), τ * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      (∀ j : Fin (cutoffCount K), ∀ x ∈ U₀, ∀ θ ∈ Ω,
        (τ * (2 : ℝ) ^ j.val, x, θ) ∈ Q) →
      (∀ j : Fin (cutoffCount K), ∀ θ ∈ Ω, ζ + (τ * (2 : ℝ) ^ j.val) • θ ∈ V) →
      (∀ η ∈ Metric.closedBall 0 (4 * K), ζ + τ • η ∈ V) →
      ∀ (F : (j : Fin (cutoffCount K)) → (t : ℝ) → t ∈ Ioo t₀ t₁ → UniformNormalData G C),
      (∀ j t (ht' : t ∈ Ioo t₀ t₁), ∀ q ∈ (F j t ht').parameterDomain ×ˢ (F j t ht').extensionDomain,
        (q.1, (t, q.2.1), q.2.2) ∈ Q) →
      (∀ t ∈ Ioo t₀ t₁, ∀ ε' ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D,
        (ε', (t, z.1), z.2) ∈ H) →
      (∀ j t (ht' : t ∈ Ioo t₀ t₁) ε' y u,
        (F j t ht').phase ε' y u = rawSlicePhaseExtension S₀ ζ (ε', (t, y), u)) →
      ∀ (v : WideInput (d + 1) (cutoffCount K)) (R : Set E),
      let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity (n := d + 1) mask v) x
      let J := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity (n := d + 1) mask v)
      ∃ u : LocalSobolev.LocalL2 R Mat, g =ᵐ[volume.restrict R] u ∧
        ∃ e : LocalSobolev.SobolevExtension R s u, e.toFun = g ∧ e.jet = J ∧
          e.jetNorm ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
          LocalSobolev.cartesianJetNorm univ s J ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
          LocalSobolev.restrictionSobolevNorm R s u ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
  classical
  let c : ℝ := (2 * Real.pi) ^ (((d + 1 : ℕ) : ℝ) / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  let coord := (NullTransport.ActualFlow.adaptedCoordinates sec).symm
  have hU₀ : IsOpen (adaptedPhysicalCoordinates sec ⁻¹' U) := hU.preimage coord.continuous
  obtain ⟨D, hD, hconstruct⟩ := exists_rawSliceDifferentiatedOperator G C
    hU₀ hV hΩ hQ hW hIW hH hHQ hband ζ hζ hshift hθ a p bmask ha hp hbmask t₀ t₁ ht
  let b (s : ℕ) := ∑ j ∈ Finset.range (s + 1), ((d + 1 : ℕ) : ℝ) ^ j * (c * D j)
  let q (s : ℕ) := Real.sqrt (BallExtension.cartesianEnergyComparisonConstant (d + 1) s)
  let B (s : ℕ) := (1 + q s) * (1 + b s)
  have hb (s : ℕ) : 0 ≤ b s := Finset.sum_nonneg fun j _ ↦
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg hc.le (hD j).le)
  have hq (s : ℕ) : 0 ≤ q s := Real.sqrt_nonneg _
  have hB (s : ℕ) : 0 < B s := mul_pos (by linarith [hq s]) (by linarith [hb s])
  refine ⟨B, hB, ?_⟩
  intro K L τ hK hL hLK hτ χ mask S A hχ hχc hχU hχsp htime hmask M hmb hS hA
    U₀ S₀ A₀ χ₀ mask₀ hm hmsp hmΩ Dpr s hmaskjet hAj hDj hε hstrip hshiftBand hshift4
    F hchart hpoints hphase v R g J
  have hM : 0 ≤ M := (norm_nonneg (mask 0)).trans (hmb 0)
  have hχ₀ : ContDiff ℝ ∞ χ₀ := hχ.comp coord.contDiff
  have hχ₀c : HasCompactSupport χ₀ := hχc.comp_homeomorph coord.toHomeomorph
  have hsupport : tsupport χ₀ = adaptedPhysicalCoordinates sec ⁻¹' tsupport χ :=
    tsupport_comp_eq_preimage χ coord.toHomeomorph
  have hχ₀U : tsupport χ₀ ⊆ U₀ := by rw [hsupport]; exact preimage_mono hχU
  have htime₀ : ∀ x ∈ tsupport χ₀, x.1 ∈ Ioo t₀ t₁ := by
    intro x hx
    rw [hsupport] at hx
    simpa only [MeasurableEquiv.symm_apply_apply] using htime _ hx
  have hmap : ContDiff ℝ ∞ (fun z : X × Y ↦ (coord z.1, z.2)) :=
    (coord.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hS₀ : ContDiffOn ℝ ∞ (Function.uncurry S₀) (U₀ ×ˢ V) :=
    hS.comp hmap.contDiffOn (fun _ hz ↦ hz)
  have hAv : ContDiffOn ℝ ∞
      (fun z : X × Y ↦ matrixChannelEquiv m (d + 1) (A (coord z.1) z.2)) (U₀ ×ˢ V) :=
    ((matrixChannelEquiv m (d + 1)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
      (hA.comp hmap.contDiffOn (fun _ hz ↦ hz))
  have hA₀ : ContDiffOn ℝ ∞ (Function.uncurry A₀) (U₀ ×ˢ V) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m * (d + 1)) ↦ ℂ)).contDiff.comp_contDiffOn hAv
  have hshiftOriginal (j : Fin (cutoffCount K)) (η : Y) (hη : η ∈ wideBand (d + 1) j.val) :
      ζ + τ • η ∈ V := by
    apply hshift4 η
    exact Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left ((lt_cutoffCount_iff hK j.val).mp j.isLt) (by norm_num)) hη.1
  obtain ⟨hg, _, hJ, _, _, _⟩ := rawSlice_weightedWideDensity_regular
    hU hV hS hA hχ hχc hχU hζ hK hshift4 hmask hM hmb v
  change ∀ j, J j = iteratedFDeriv ℝ j g at hJ
  have hfield : (fun y ↦ (χ₀ y : ℂ) • rawPrimaryDemodulatedIntegral S₀
      (fun z η ↦ WithLp.toLp 2 (A₀ z η)) ζ τ volume
        (weightedWideDensity (n := d + 1) mask v) y) =
      (fun y ↦ matrixChannelEquiv m (d + 1) (g (adaptedPhysicalCoordinates sec y))) := by
    funext y
    change (χ₀ y : ℂ) • rawPrimaryDemodulatedIntegral S₀
      (fun z η ↦ matrixChannelEquiv m (d + 1) (A (adaptedPhysicalCoordinates sec z) η))
      ζ τ volume _ y = _
    have hi := rawPrimaryDemodulatedIntegral_matrixChannelEquiv (n := d + 1)
      S₀ (fun z η ↦ A (adaptedPhysicalCoordinates sec z) η) ζ τ
      (weightedWideDensity (n := d + 1) mask v) y
    erw [hi]
    rw [← map_smul]
    congr 1
  have hchannels (j : ℕ) (hj : j ≤ s) (α : Fin j → Fin (d + 1)) :
      ∃ T : Lp Mat 2 (volume : Measure E),
        T =ᵐ[volume] (fun x ↦ J j x (fun k ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ (α k))) ∧
        ‖T‖ ≤ (c * D j) * K ^ ((j : ℝ) + 1 / 2) * ‖v‖ := by
    let w : Fin j → E := fun k ↦ EuclideanSpace.basisFun (Fin (d + 1)) ℝ (α k)
    have hw : ∀ k, ‖(adaptedPhysicalCoordinates sec).symm (w k)‖ ≤ 1 := by
      intro k
      exact (norm_adaptedPhysicalCoordinates_symm_le sec (w k)).trans
        (le_of_eq (OrthonormalBasis.norm_eq_one _ _))
    obtain ⟨T, hT, hn, _, _⟩ := hconstruct K L τ hK hL hLK hτ χ₀ mask S₀ A₀
      hχ₀.contDiffOn hχ₀c hχ₀U hχsp htime₀ hmask M hmb hS₀ hA₀ hm hmsp hmΩ Dpr j
      (fun i z hz k hk ↦ hmaskjet i z hz k (by omega))
      (fun z hz k hk ↦ hAj z hz k (by omega))
      (fun z hz k hk ↦ hDj z hz k (by omega)) hε hstrip hshiftBand hshiftOriginal F
      hchart hpoints hphase (fun k ↦ (adaptedPhysicalCoordinates sec).symm (w k)) hw
    refine ⟨physicalRawSliceOperator sec T v, ?_, ?_⟩
    · have hTv := hT v
      have hnormalized : (fun y ↦ (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
          ((χ₀ y : ℂ) • rawPrimaryDemodulatedIntegral S₀
            (fun z η ↦ WithLp.toLp 2 (A₀ z η)) ζ τ volume
              (weightedWideDensity (n := d + 1) mask v) y)) =
          (fun y ↦ (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
            matrixChannelEquiv m (d + 1) (g (adaptedPhysicalCoordinates sec y))) :=
        funext fun y ↦ congrArg ((2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) • ·) (congrFun hfield y)
      erw [hnormalized] at hTv
      have heq := physicalRawSliceOperator_coeFn_derivative sec T g hg v w hTv
      simpa only [hJ j] using heq
    · apply ((physicalRawSliceOperator sec T).le_opNorm v).trans
      rw [norm_physicalRawSliceOperator]
      calc
        (c * ‖T‖) * ‖v‖ ≤ (c * (D j * K ^ ((j : ℝ) + 1 / 2))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hc.le) (norm_nonneg _)
        _ = _ := by ring
  choose P hP hPn using hchannels
  let T (j : ℕ) (α : Fin j → Fin (d + 1)) := if hj : j ≤ s then P j hj α else 0
  have hT (j : ℕ) (hj : j ≤ s) (α) : T j α = P j hj α := dite_eq_left hj
  obtain ⟨u, hu, _, he⟩ := exists_rawSlice_weightedWideDensity_sobolevExtensions
    hU hV hS hA hχ hχc hχU hζ hK hshift4 hmask hM hmb v R
  obtain ⟨e, hef, hej⟩ := he s
  change e.jet = J at hej
  have heBound : e.jetNorm ≤ b s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
    apply rawSliceExtension_jetNorm_le e T _ (fun j ↦ mul_nonneg hc.le (hD j).le) hK (norm_nonneg _) _
    · intro j hj α
      rw [hej, hT j hj]
      exact hP j hj α
    · intro j hj α
      rw [hT j hj]
      exact hPn j hj α
  have hjet : e.jetNorm ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
    apply heBound.trans
    gcongr
    dsimp only [B]
    nlinarith [hb s, hq s]
  refine ⟨u, hu, e, hef, hej, hjet, ?_, (LocalSobolev.restrictionSobolevNorm_le e).trans hjet⟩
  have hcart := LocalSobolev.cartesianJetNorm_le_mul_jetL2Norm univ s e.jet
    (fun j hj ↦ (e.memLp_jet j hj).restrict univ)
  simp only [LocalSobolev.jetL2Norm, Measure.restrict_univ] at hcart
  rw [← hej]
  calc
    LocalSobolev.cartesianJetNorm univ s e.jet ≤ q s * e.jetNorm := hcart
    _ ≤ q s * (b s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖) := mul_le_mul_of_nonneg_left heBound (hq s)
    _ ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
      rw [← mul_assoc, ← mul_assoc]
      gcongr
      dsimp only [B]
      nlinarith [hb s, hq s]

end JanetCartan.RawPrimary.SliceBounds
