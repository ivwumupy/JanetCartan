module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian.Jacobian

/-!
# Primitive transport jets control forward, inverse and Jacobian differences

The quantitative transport input to the full amplitude comparison in
`paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4', from the actual gradient
integral `app:ch_background:eq:bg-Psi` and the literal determinant
`app:ch_background:eq:bg-jacobian`.

All sets, the reference, normalization and positive determinant gap are fixed
before the comparison constant and positive tolerance. The varying primitive,
genuine inverse, supplied Jacobian and perturbation size come afterwards.
No inverse or Jacobian derivative difference is assumed. The geometric
construction remains responsible for the common domains, inverse identities,
normalized differential gap and positive determinant gap. The parent amplitude
construction supplies these hypotheses; this is not normal-operator continuity.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Quantitative finite mixed-jet differences from the primitive transport
map alone, with loss two. This is the forward/inverse/Jacobian input to the
full-amplitude difference estimate of `app:ch_osc:prop:osc-normal`, Step 4'.
Both physical positions and the spectator remain variables. `J` and `J₀`
are the literal absolute Jacobians on the open chart, with a common positive
gap on the compact source. Constants may use higher norms of the fixed
reference, and precede `Y`, `u`, `J`, and `d`.

The primitive and geometric construction must supply segment containment,
smoothness, the genuine inverse identities and the differential gaps. All
derivative difference premises of the inverse and determinant lemmas are
discharged here from `cNorm L (m + 2) (Y - Y₀) ≤ d`. -/
theorem exists_transportForwardJacobian_sub_le
    {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {J₀ : InputVariables n → ℝ}
    {K W B : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hB : IsCompact B) (hWB : W ⊆ B)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (hY₀ : ContDiffOn ℝ ∞ Y₀ V) (hu₀ : ContDiffOn ℝ ∞ u₀ Ω)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (c : TransportSliceCoordinates n)
    (hrange₀ : MapsTo (inverseCoordinates u₀) Q K)
    (heq₀ : ∀ p ∈ Ω, transportAveragedGradient Y₀ (inverseCoordinates u₀ p) = p.1.2.2)
    (hJ₀ : EqOn J₀ (transportAbsoluteJacobian c Y₀) W)
    {δ : ℝ} (hδ : 0 < δ) (hgap₀ : ∀ p ∈ K, δ ≤ J₀ p) (m : ℕ) :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (d : ℝ),
      ContDiffOn ℝ ∞ Y V → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) Q K →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      (∀ q ∈ K,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      EqOn J (transportAbsoluteJacobian c Y) W → (∀ p ∈ K, δ ≤ J p) →
      cNorm L (m + 2) (Y - Y₀) ≤ d → d ≤ ε →
      cNorm K m (augmentedTransportGradient Y - augmentedTransportGradient Y₀) +
        cNorm Q m (inverseCoordinates u - inverseCoordinates u₀) +
        cNorm K m (J - J₀) +
        cNorm K m ((fun p ↦ (J p)⁻¹) - (fun p ↦ (J₀ p)⁻¹)) ≤ C * d := by
  have hg₀ := transportAveragedGradient_contDiffOn hW hV hT hIT hsegT hY₀
  have ha₀ := augmentedTransportGradient_contDiffOn hW hV hT hIT hsegT hY₀
  obtain ⟨F, hF, hforward⟩ := exists_transportForward_sub_le
    hKW hW hB hWB hV hL hLV hT hIT hsegT hseg A (m + 1)
  obtain ⟨I, hI, hinverse⟩ := exists_inverseCoordinates_sub_le
    hK hconv hQ hW hKW hΩ hQΩ ha₀ hu₀ A hrange₀ heq₀ m
  obtain ⟨H, hH, hjac⟩ := exists_transportAbsoluteJacobian_sub_le
    c hK hW hKW hg₀ hδ (fun p hp ↦ (hJ₀ (hKW hp)) ▸ hgap₀ p hp) m
  let D := ((m + 1 : ℕ) : ℝ) * ‖transportDifferentialRestriction c‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let R := 1 + F + D * F
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨F + I * F + H * D * F, by positivity, R⁻¹, inv_pos.mpr hR, ?_⟩
  intro Y u J d hY hu hrange heq hgap hJ hJgap hprim hsmall
  have hd : 0 ≤ d := (cNorm_nonneg _ _ _).trans hprim
  have hRd : R * d ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hsmall hR.le).trans_eq (mul_inv_cancel₀ hR.ne')
  have hFd : F * d ≤ 1 := (mul_le_mul_of_nonneg_right
    (show F ≤ R by dsimp [R]; nlinarith [mul_nonneg hD hF.le]) hd).trans hRd
  have hDFd : D * F * d ≤ 1 := (mul_le_mul_of_nonneg_right
    (show D * F ≤ R by dsimp [R]; linarith) hd).trans hRd
  have hfwd := hforward Y Y₀ hY hY₀
  have hprim' : cNorm L (m + 1 + 1) (Y - Y₀) ≤ d := by simpa [Nat.add_assoc] using hprim
  have hscale := mul_le_mul_of_nonneg_left hprim' hF.le
  have hgdiff := hfwd.1.trans hscale
  have hadiff := (cNorm_mono_order (s := K)
    (f := augmentedTransportGradient Y - augmentedTransportGradient Y₀)
    (Nat.le_succ m)).trans (hfwd.2.1.trans hscale)
  have hndiff := (cNorm_mono_order (s := K)
    (f := (A.symm ∘ augmentedTransportGradient Y) - (A.symm ∘ augmentedTransportGradient Y₀))
    (Nat.le_succ m)).trans (hfwd.2.2.trans hscale)
  have hg := transportAveragedGradient_contDiffOn hW hV hT hIT hsegT hY
  have ha := augmentedTransportGradient_contDiffOn hW hV hT hIT hsegT hY
  have hidiff := (hinverse Y u ha hu hrange heq hgap (hndiff.trans hFd)).trans
    (mul_le_mul_of_nonneg_left hndiff hI.le)
  have hsdiff : cNorm K m (transportSliceDifferential c Y - transportSliceDifferential c Y₀)
      ≤ D * F * d := (cNorm_transportSliceDifferential_sub_le c hK hW hKW hg hg₀ m).trans
        ((mul_le_mul_of_nonneg_left hgdiff hD).trans_eq (by ring))
  have hjdiff := (hjac Y hg (fun p hp ↦ (hJ (hKW hp)) ▸ hJgap p hp)
    (hsdiff.trans hDFd)).trans (mul_le_mul_of_nonneg_left hsdiff hH.le)
  have he (p) (hp : p ∈ K) : J - J₀ =ᶠ[𝓝 p]
      transportAbsoluteJacobian c Y - transportAbsoluteJacobian c Y₀ := by
    filter_upwards [hW.mem_nhds (hKW hp)] with q hq
    exact congrArg₂ (· - ·) (hJ hq) (hJ₀ hq)
  have hei (p) (hp : p ∈ K) :
      (fun q ↦ (J q)⁻¹) - (fun q ↦ (J₀ q)⁻¹) =ᶠ[𝓝 p]
      (fun q ↦ (transportAbsoluteJacobian c Y q)⁻¹) -
        (fun q ↦ (transportAbsoluteJacobian c Y₀ q)⁻¹) := by
    filter_upwards [hW.mem_nhds (hKW hp)] with q hq
    exact congrArg₂ (fun a b : ℝ ↦ a⁻¹ - b⁻¹) (hJ hq) (hJ₀ hq)
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he m,
    GeometricProfile.cNorm_eq_of_eventuallyEq hei m]
  nlinarith [hadiff, hidiff, hjdiff]

end JanetCartan.ContinuumNormal.CarrierVariation
