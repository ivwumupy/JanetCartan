module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.DensityWeights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.ShellTransfer

/-!
# Full normal-amplitude comparison in the original positive density class

The fixed masks, two scalar-ODE footpoints, genuine conic inverse and absolute
Jacobian enter the literal amplitudes. Uniform radial control is applied before
spectator integration and reflection. The physical and scalar domains are
supplied unchanged. The geometric and primitive convergence inputs still have
to be instantiated on the normalized row by their concrete producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs.WideDensity CarrierVariation.AmplitudeDifference
open AmplitudeBound

variable {n N : ℕ}

/-- Original-domain primitive differences give the full complex and reflected
amplitude differences uniformly over the wider positive density class. Both
normal fields are multiplied by the SAME density at their own ODE labels.
All masks are fixed, and no detector support is removed. The factor four is
exactly the reflection normalization. Constants precede the varying density
and the primitive error; the density reserve is only `s + 1 ≤ d₀`.

Consumer: the normalized current/frozen PDO comparison at `s = 2 * (n + 1)`.
Sources: `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-full-complex-amplitude`, `bg-real-symbol`, and
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_fullAmplitude_sqrtFootpoints_sub_bounds
    (D : CoefficientNormCharts n)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hL : IsCompact L) (hconv : Convex ℝ L)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hη : ∀ p ∈ K, ε ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    {J₀ : InputVariables n → ℝ} (hJ₀ : ContDiffOn ℝ ∞ J₀ W)
    (hgap₀ : ∀ p ∈ K, δ ≤ |J₀ p|)
    (s : ℕ) (hreserve : 2 * (n + 1) ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hJ₀M : cNorm K s J₀ ≤ M)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1) :
    ∃ C > 0, ∀ (a : Fin 2 → Coefficients n N)
      (J : Fin 2 → InputVariables n → ℝ)
      (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (F : Fin 2 → InputVariables n → Variables n × Euclidean 2)
      (Z : Fin 2 → Set (InputVariables n))
      (Y : Fin 2 → Euclidean n × ContinuumRow.CarrierParameter →
        Euclidean (n - 1) × Euclidean 3) (d : ℝ),
      0 ≤ d → J 1 = J₀ → (∀ i, (a i).high = h) →
      (a 0).measurement = (a 1).measurement → (a 0).angular = (a 1).angular →
      D.Controls s M (M + 1) 1 (a 0) → D.Controls (s + 1) M (M + 1) 1 (a 1) →
      (∀ i, PrimitiveRegularity (a i) (J i) W) →
      (∀ p ∈ K, δ ≤ |J 0 p|) → cNorm K s (J 0) ≤ M →
      (∀ i, ContDiffOn ℝ ∞ (u i) Ω) →
      (∀ i, MapsTo (inverseCoordinates (u i)) Q K) →
      (∀ i, cNorm Q s (inverseCoordinates (u i)) ≤ M) →
      (∀ i, MapsTo (inverseCoordinates (u i)) Ω W) →
      (∀ i p, p ∈ Ω → F i (inverseCoordinates (u i) p) = p) →
      (∀ i p, p ∈ W → (a i).measurement p.1.1 ≠ 0 →
        (a i).measurement p.1.2 ≠ 0 →
        (a i).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z i) →
      (∀ i, closure (F i '' Z i) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ i p, p ∈ Ω → ‖(u i p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ i t, 0 < t → ∀ p ∈ Ω,
        u i (scaleFrequency t p.1, p.2) = ((u i p).1, t • (u i p).2)) →
      (∀ i t, 0 < t → ∀ p ∈ Ω,
        J i (scaleInput t (inverseCoordinates (u i) p)) = t * J i (inverseCoordinates (u i) p)) →
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (F 0 '' Z 0) ∪ closure (F 1 '' Z 1) → (p, v) ∈ Q) →
      (∀ i side, ContDiffOn ℝ ∞ (Y i ∘ densityEndpoint side) W) →
      (∀ i side, MapsTo (Y i ∘ densityEndpoint side) W L) →
      (∀ i side, cNorm Q s (Y i ∘ densityEndpoint side ∘ inverseCoordinates (u i)) ≤ M) →
      cNorm D.field.carrier s ((a 0).normal - (a 1).normal) ≤ d →
      cNorm D.field.carrier s ((a 0).reduced - (a 1).reduced) ≤ d →
      cNorm K s (J 0 - J 1) ≤ d →
      cNorm Q s (inverseCoordinates (u 0) - inverseCoordinates (u 1)) ≤ d →
      (∀ side, cNorm Q s
        (Y 0 ∘ densityEndpoint side ∘ inverseCoordinates (u 0) -
          Y 1 ∘ densityEndpoint side ∘ inverseCoordinates (u 1)) ≤ d) →
      ∀ (d₀ : ℕ), s + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      (∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := fun i ↦ {(a i) with normal := fun q ↦ Real.sqrt (1 + v (Y i q)) • (a i).normal q}
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j -
          fullComplexMatrixAmplitude (av 1) (J 1) (u 1) Ω S ξ z i j) s (C * d) ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j -
          fullReflectedMatrixAmplitude (av 1) (J 1) (u 1) Ω S ξ z i j) s ((4 * C) * d) := by
  obtain ⟨B, hB, hcompare⟩ := exists_rescaled_weighted_inputDensity_sub_le
    (N := N) D hh htail hK hW hKW hQ hΩ hQΩ hL hconv hε hδ hη hrange
      hJ₀ hgap₀ s hM hJ₀M
  obtain ⟨C, hC, hfull⟩ := exists_fullAmplitude_sub_bounds_of_supported_shell
    (N := N) s hreserve hS hQ hCupper hℓ hlow hB.le
  refine ⟨C, hC, ?_⟩
  intro a J u F Z Y d hd href hhigh hm hang ha ha₀ hreg hgap hJM hu huK huM hmap hright
    hsupp hbuffer hupper hscale huScale hJScale hshell hY hYL hYM hn hq hj hi hYd
    d₀ horder v hv hvm hpos
  let av := fun i ↦ {(a i) with normal := fun q ↦ Real.sqrt (1 + v (Y i q)) • (a i).normal q}
  let g := fun i side ↦ Y i ∘ densityEndpoint side ∘ inverseCoordinates (u i)
  have hg (i : Fin 2) (side : Bool) : ContDiffOn ℝ ∞ (g i side) Ω :=
    (hY i side).comp (inverseCoordinates_contDiffOn (hu i)) (hmap i)
  have hgr (i : Fin 2) (side : Bool) : MapsTo (g i side) Ω L :=
    (hYL i side).comp (hmap i)
  have hav : ∀ i, PrimitiveRegularity (av i) (J i) W :=
    fun i ↦ primitiveRegularity_sqrtFootpoints (hreg i) (Y i) (hY i) (hYL i) v hv hpos
  apply hfull av J u F Ω (fun _ ↦ W) Z d hd hΩ hQΩ hav hu hmap hright hsupp hbuffer
    (fun i r hr ↦ by change (a i).high r = 0; rw [hhigh i]; exact hzero r hr)
    hupper hscale huScale hJScale hshell
  intro t ht
  have he (i : Fin 2) :
      (fun p ↦ inputDensity (rescaledCoefficients (av i) t) (J i) (inverseCoordinates (u i) p))
        =ᶠ[𝓝ˢ Q]
      (fun p ↦ densityPair v (g i) p •
        inputDensity (rescaledCoefficients (a i) t) (J i) (inverseCoordinates (u i) p)) := by
    filter_upwards [hΩ.mem_nhdsSet.mpr hQΩ] with p hp
    exact inputDensity_sqrtFootpoints (rescaledCoefficients (a i) t) (J i) (Y i) v
      (inverseCoordinates (u i) p)
      (fun side ↦ (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (hpos _ (hgr i side hp)))
  have heNorm : cNorm Q s
      ((fun p ↦ inputDensity (rescaledCoefficients (av 0) t) (J 0) (inverseCoordinates (u 0) p)) -
        (fun p ↦ inputDensity (rescaledCoefficients (av 1) t) (J 1) (inverseCoordinates (u 1) p))) =
      cNorm Q s
      ((fun p ↦ densityPair v (g 0) p • inputDensity (rescaledCoefficients (a 0) t)
          (J 0) (inverseCoordinates (u 0) p)) -
        (fun p ↦ densityPair v (g 1) p • inputDensity (rescaledCoefficients (a 1) t)
          (J 1) (inverseCoordinates (u 1) p))) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ s
    intro p hp
    exact ((he 0).filter_mono (nhds_le_nhdsSet hp)).sub ((he 1).filter_mono (nhds_le_nhdsSet hp))
  change cNorm Q s
    ((fun p ↦ inputDensity (rescaledCoefficients (av 0) t) (J 0) (inverseCoordinates (u 0) p)) -
      (fun p ↦ inputDensity (rescaledCoefficients (av 1) t) (J 1) (inverseCoordinates (u 1) p))) ≤ B * d
  rw [heNorm]
  have hb := hcompare (a 0) (a 1) (J 0) (u 0) (u 1) (g 0) (g 1) d hd
    (hhigh 0) (hhigh 1) ha ha₀ (hreg 0).jacobian hgap hJM (hu 0) (hu 1)
    (huK 0) (huK 1) (huM 0) (huM 1)
    (fun side p hp ↦ (hg 0 side).contDiffAt (hΩ.mem_nhds (hQΩ hp)))
    (fun side p hp ↦ (hg 1 side).contDiffAt (hΩ.mem_nhds (hQΩ hp)))
    (fun side ↦ (hgr 0 side).mono_left hQΩ) (fun side ↦ (hgr 1 side).mono_left hQΩ)
    (hYM 0) (hYM 1)
    (by simpa only [hm, sub_self, cNorm_zero] using hd)
    (by simpa only [hang, sub_self, cNorm_zero] using hd)
    hn hq (by simpa only [href] using hj) hi hYd d₀ horder v hv hvm t ht
  simpa only [href] using hb.2.2

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
