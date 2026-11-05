module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeTransport
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Transversality

/-!
# The two-time root of the actual stress pencil

The root in `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`,
is constructed from the literal current pencil. We apply the existing scalar
root theorem to its normalized determinant, whose degree-one homogeneity and
smoothness are already proved. The original determinant transverse derivative
supplies the scalar implicit-function hypothesis. No root or phase is an input.

The fixed coordinate equivalence is instantiated by the retained adapted
coordinates in the sector construction. This local result retains the original
pencil's characteristic equation and simple-root condition throughout the
constructed domain. Uniform coefficient-family buffers and symbol estimates
remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The original physical position and covector in the retained linear
coordinates (`app:ch_regular_base:lem:characteristic-kernel`). -/
def adaptedPencilState (e : Euclidean n ≃L[ℝ] (ℝ × E))
    (z : ((ℝ × E) × E) × ℝ) : Euclidean n × Euclidean n :=
  (e.symm z.1.1, e.symm (z.2, z.1.2))

/-- The literal normalized determinant in the scalar-root argument order
`((x,η),τ)` (`app:ch_regular_base:lem:characteristic-kernel`). -/
def adaptedNormalizedPencil (Q : Euclidean n → Fin n → MetricTensor n)
    (e : Euclidean n ≃L[ℝ] (ℝ × E)) (z : ((ℝ × E) × E) × ℝ) : ℝ :=
  normalizedSymbol Q (adaptedPencilState e z)

omit [CompleteSpace E] in
/-- The coordinate change is smooth jointly in position and covector
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiff_adaptedPencilState (e : Euclidean n ≃L[ℝ] (ℝ × E)) :
    ContDiff ℝ ∞ (adaptedPencilState e) :=
  (e.symm.contDiff.comp contDiff_fst.fst).prodMk
    (e.symm.contDiff.comp (contDiff_snd.prodMk contDiff_fst.snd))

omit [CompleteSpace E] in
/-- Homogeneity is derived from the actual determinant normalization, not
postulated for a replacement scalar symbol
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem adaptedNormalizedPencil_homogeneous
    (Q : Euclidean n → Fin n → MetricTensor n) (e : Euclidean n ≃L[ℝ] (ℝ × E))
    (x : ℝ × E) (η : E) (τ : ℝ) {a : ℝ} (ha : 0 < a) :
    adaptedNormalizedPencil Q e ((x, a • η), a * τ) =
      a * adaptedNormalizedPencil Q e ((x, η), τ) := by
  have he : e.symm (a * τ, a • η) = a • e.symm (τ, η) :=
    e.symm.map_smul a (τ, η)
  simpa only [adaptedNormalizedPencil, adaptedPencilState, he] using
    normalizedSymbol_pos_homogeneous Q (e.symm x, e.symm (τ, η)) ha

omit [CompleteSpace E] in
/-- The scalar covector derivative at a characteristic point is precisely the
positive normalization times the original determinant derivative. This
connects the actual pencil gap to the implicit-function constructor
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_adaptedNormalizedPencil
    (Q : Euclidean n → Fin n → MetricTensor n) (e : Euclidean n ≃L[ℝ] (ℝ × E))
    (x : ℝ × E) (η : E) (τ : ℝ) (hξ : e.symm (τ, η) ≠ 0)
    (hp : determinant (Q (e.symm x)) (e.symm (τ, η)) = 0) :
    HasDerivAt (fun t ↦ adaptedNormalizedPencil Q e ((x, η), t))
      (determinantNormalization (e.symm (τ, η)) *
        fderiv ℝ (determinant (Q (e.symm x))) (e.symm (τ, η)) (e.symm (1, 0))) τ := by
  have hf : DifferentiableAt ℝ (fun ξ ↦ normalizedSymbol Q (e.symm x, ξ)) (e.symm (τ, η)) :=
    (hasFDerivAt_determinant (Q (e.symm x)) _).differentiableAt.mul
      ((contDiffAt_determinantNormalization hξ).differentiableAt (by simp))
  have hc := e.symm.hasFDerivAt.comp_hasDerivAt τ
    ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ η))
  have hd := hf.hasFDerivAt.comp_hasDerivAt τ hc
  rw [fderiv_covector_normalizedSymbol_of_determinant_eq_zero Q (e.symm x) hξ hp] at hd
  exact hd

/-- Construct a smooth homogeneous root of the literal current pencil from
its simple characteristic covector. The original determinant equation and
transverse nonvanishing hold on the entire returned conic domain. These are
the primitive inputs for the actual two-time flow and normalized minor
nullvectors in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_pencilRoot_domain
    (e : Euclidean n ≃L[ℝ] (ℝ × E))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (z : RootState E) (τ : ℝ) (hx : e.symm (z.1, z.2.1) ∈ Ω)
    (hξ : e.symm (τ, z.2.2) ≠ 0)
    (hp : determinant (Q (e.symm (z.1, z.2.1))) (e.symm (τ, z.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (τ, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState E), ∃ h : RootState E → ℝ,
      IsOpen D ∧ z ∈ D ∧ h z = τ ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
          (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) ∧
      (∀ w ∈ D, ∀ a : ℝ, 0 < a →
        (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w) := by
  let f := adaptedNormalizedPencil Q e
  let S := adaptedPencilState e ⁻¹' normalizedSymbolDomain Ω
  have hS : IsOpen S := (isOpen_normalizedSymbolDomain hΩ).preimage
    (contDiff_adaptedPencilState e).continuous
  have hf : ContDiffOn ℝ ∞ f S :=
    (contDiffOn_normalizedSymbol hΩ hQ).comp (contDiff_adaptedPencilState e).contDiffOn
      (fun _ hw ↦ hw)
  let z₀ : ((ℝ × E) × E) × ℝ := (((z.1, z.2.1), z.2.2), τ)
  have hzS : z₀ ∈ S := ⟨hx, hξ⟩
  have hz0 : f z₀ = 0 := (normalizedSymbol_eq_zero_iff Q hξ).mpr hp
  have hdf := CharacteristicRoot.hasDerivAt_scalar
    ((hf.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by simp))
  have hdf' := hasDerivAt_adaptedNormalizedPencil Q e (z.1, z.2.1) z.2.2 τ hξ hp
  have hscalar : CharacteristicRoot.scalarDerivative f z₀ ≠ 0 := by
    rw [hdf.unique hdf']
    exact mul_ne_zero (determinantNormalization_pos hξ).ne' hgap
  have hcoord : (τ, z.2.2) ≠ 0 := fun he ↦ hξ (by rw [he, map_zero])
  obtain ⟨ℓ, U, V, c, _, _, _, hc, hD₀, hzD₀, hbase, hh, hroot, hscale, _, hder, _⟩ :=
    CharacteristicRoot.exists_conicRoot_patch hS hf
      (fun x η t a ha ↦ adaptedNormalizedPencil_homogeneous Q e x η t ha)
      hzS hz0 hscalar hcoord
  let H := CharacteristicRoot.conicRoot ℓ (hf.contDiffAt (hS.mem_nhds hzS)) hscalar
  let R : RootState E → (ℝ × E) × E := fun w ↦ ((w.1, w.2.1), w.2.2)
  let D := R ⁻¹' CharacteristicRoot.conicDomain ℓ U ∩
    (fun w : RootState E ↦ e.symm (w.1, w.2.1)) ⁻¹' Ω
  have hR : ContDiff ℝ ∞ R := (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hopen : IsOpen D := (hD₀.preimage hR.continuous).inter
    (hΩ.preimage (e.symm.continuous.comp (continuous_fst.prodMk continuous_snd.fst)))
  refine ⟨D, H ∘ R, hopen, ⟨hzD₀, hx⟩, hbase,
    hh.comp hR.contDiffOn (fun _ hw ↦ hw.1), ?_, ?_⟩
  · intro w hw
    have hwη : w.2.2 ≠ 0 := by
      intro he
      have hpos := hw.1.1
      change 0 < ℓ w.2.2 at hpos
      simp [he] at hpos
    have hwξ : e.symm (H (R w), w.2.2) ≠ 0 := by
      intro he
      have hp0 : (H (R w), w.2.2) = 0 := e.symm.injective (by simpa using he)
      exact hwη (congrArg Prod.snd hp0)
    have hdet : determinant (Q (e.symm (w.1, w.2.1))) (e.symm (H (R w), w.2.2)) = 0 :=
      (normalizedSymbol_eq_zero_iff Q hwξ).mp (hroot (R w) hw.1).1
    refine ⟨hw.2, hwη, hdet, ?_⟩
    obtain ⟨d, hd, hcd⟩ := hder (R w) hw.1
    have hd' := hasDerivAt_adaptedNormalizedPencil Q e (w.1, w.2.1) w.2.2 (H (R w)) hwξ hdet
    have he := hd.unique hd'
    intro hzero
    dsimp only [Function.comp_apply] at hzero
    rw [hzero, mul_zero] at he
    have : 0 < |d| := hc.trans_le hcd
    simp [he] at this
  · intro w hw a ha
    obtain ⟨hmem, he⟩ := hscale (R w) hw.1 a ha
    exact ⟨⟨hmem, hw.2⟩, he⟩

/-- Construct the two-time phase and its signed-transport chart for the actual
stress pencil, starting only with the smooth frame and a simple nonzero
characteristic covector. Every scalar-root, flow, inverse and phase premise
of `exists_localTwoTimePhase_transport` is discharged by its concrete producer.
The signed datum and potential are chosen after the chart; the sector's
`lᵀσ` and `lᵀPk` must subsequently be substituted on this same chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_pencil_twoTimePhase_transport {d : ℕ} {ι : Type*} [Fintype ι]
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (z : RootState (Euclidean d)) (τ : ℝ) (hx : e.symm (z.1, z.2.1) ∈ Ω)
    (hξ : e.symm (τ, z.2.2) ≠ 0)
    (hp : determinant (Q (e.symm (z.1, z.2.1))) (e.symm (τ, z.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (τ, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      IsOpen D ∧ z ∈ D ∧ h z = τ ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω ∧ w.2.2 ≠ 0 ∧
        determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
          (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) ∧
      ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
        ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
          ∃ δ > (0 : ℝ),
            let I := ball z.1 δ
            let U := ball z.2 δ
            let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
            IsOpen V ∧ (z.1, z) ∈ V ∧
            (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
            (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
              (twoTimeState Φ (C.symm q)).1 = q.1) ∧
            ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
            (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
            (∀ q ∈ C.target,
              determinant (Q (e.symm (q.1, q.2.2.1)))
                (e.symm (deriv (fun t ↦ twoTimePhase C (t, q.2)) q.1,
                  gradient (fun y ↦ twoTimePhase C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1)) = 0) ∧
            (∀ w ∈ I ×ˢ U, (w.1, w) ∈ V ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
            ∀ (c : TwoTimePoint (Euclidean d) → ℝ) (a₀ : RootState (Euclidean d) → ι → ℝ),
              ContDiffOn ℝ ∞ c C.target → ContDiffOn ℝ ∞ a₀ (I ×ˢ U) →
              ContDiffOn ℝ ∞ (twoTimeRowTransport C c a₀) V ∧
              (∀ w ∈ I ×ˢ U, twoTimeRowTransport C c a₀ (w.1, w) = a₀ w) ∧
              (∀ q ∈ V, fderiv ℝ (twoTimeRowTransport C c a₀) q
                (1, (0, (-rootMomentumGradient h (twoTimeState Φ (C.symm q)), 0))) =
                  -c q • twoTimeRowTransport C c a₀ q) := by
  obtain ⟨D, h, hD, hz, hbase, hh, hroot, hscale⟩ :=
    exists_pencilRoot_domain e hΩ hQ z τ hx hξ hp hgap
  have hhom : ∀ w ∈ D, ∀ᶠ a : ℝ in 𝓝 1,
      h (w.1, (w.2.1, a • w.2.2)) = a * h w := by
    intro w hw
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    exact (hscale w hw a ha).2
  obtain ⟨Φ, C, δ, hδ, hV, hzV, hC, hstate, hphase, hdiff, hdiag, hrow⟩ :=
    exists_localTwoTimePhase_transport (ι := ι) hD hh hhom hz
  refine ⟨D, h, hD, hz, hbase, hh, hroot, Φ, C, δ, hδ, hV, hzV, hC, hstate,
    hphase, hdiff, ?_, hdiag, hrow⟩
  intro q hq
  have hg : HasGradientAt
      (fun y ↦ twoTimePhase C (q.1, (q.2.1, (y, q.2.2.2))))
      (twoTimeState Φ (C.symm q)).2.2 q.2.2.1 :=
    hasFDerivAt_twoTimePhase_position (hdiff q hq)
  rw [(hasDerivAt_twoTimePhase_outputTime (hdiff q hq)).deriv, hg.gradient]
  have hs : twoTimeState Φ (C.symm q) =
      (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) := by
    exact Prod.ext (hstate q hq).2
      (Prod.ext (twoTimeChart_inverse_coordinates hC hq).2.2.2 rfl)
  have hdet := (hroot _ (hstate q hq).1).2.2.1
  rw [hs] at hdet
  exact hdet

end JanetCartan.RegularSector.Characteristic
