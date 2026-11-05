module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilRoot
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse

/-!
# Normalized nullvectors for the actual root pencil

The fixed-minor normalization in `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel`, is applied to the literal
stress pencil at the constructed root. Its time coefficient is the same
pencil evaluated on the adapted time direction. The determinant derivative
produces the transport denominator and a nonzero minor; no normalized
nullvectors or complement inverse are assumed.

The contraction identity identifies the spatial transport coefficient with
the negative derivative of the root. Its consumer is the signed row equation
and the compatibility `lᵀPW₀ = 0` in the direct two-term cancellation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic

open ActualCarriers

variable {n d : ℕ}

/-- The actual characteristic matrix at `τ = h(t,y,η)`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rootPencil (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (w : RootState (Euclidean d)) : MetricTensor n :=
  pencil (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2))

/-- The literal coefficient of the adapted time derivative
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rootTimeCoefficient (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (w : RootState (Euclidean d)) : MetricTensor n :=
  pencil (Q (e.symm (w.1, w.2.1))) (e.symm (1, 0))

/-- Smoothness of the literal matrix at the root follows from the frame and
the constructed scalar root (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_rootPencil
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω)
    {D : Set (RootState (Euclidean d))} {h : RootState (Euclidean d) → ℝ}
    (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω) :
    ContDiffOn ℝ ∞ (rootPencil e Q h) D :=
  contDiff_pencil.comp_contDiffOn
    ((hQ.comp (e.symm.contDiff.comp_contDiffOn
      (contDiffOn_fst.prodMk contDiffOn_snd.fst)) hmap).prodMk
      (e.symm.contDiff.comp_contDiffOn (hh.prodMk contDiffOn_snd.snd)))

/-- The actual adapted time coefficient is smooth on the same physical
domain (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_rootTimeCoefficient
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω) {D : Set (RootState (Euclidean d))}
    (hmap : ∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω) :
    ContDiffOn ℝ ∞ (rootTimeCoefficient e Q) D :=
  contDiff_pencil.comp_contDiffOn
    ((hQ.comp (e.symm.contDiff.comp_contDiffOn
      (contDiffOn_fst.prodMk contDiffOn_snd.fst)) hmap).prodMk contDiffOn_const)

/-- The original covector derivative is exactly the matrix determinant
derivative on the actual time coefficient
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootPencil_time_derivative
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (w : RootState (Euclidean d)) :
    fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) =
      fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
        (e.symm (h w, w.2.2)) (e.symm (1, 0)) := by
  rw [(hasFDerivAt_determinant _ _).fderiv]
  rfl

/-- A simple root produces a nonvanishing minor of this actual pencil
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_rootPencil_minor
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (w : RootState (Euclidean d))
    (hgap : fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
      (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ r c : Fin n, (rootPencil e Q h w).adjugate r c ≠ 0 := by
  by_contra! hn
  have hzero : (rootPencil e Q h w).adjugate = 0 := by
    ext r c
    exact hn r c
  apply hgap
  rw [← rootPencil_time_derivative e Q h w, Matrix.fderiv_det_apply, hzero,
    Matrix.zero_mul, Matrix.trace_zero]

/-- The normalized left/right contraction is the ratio of the original
determinant differentials. This keeps the oblique normalization and every
orientation sign of the selected minor
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minorLeft_mulVec_minorRight_eq_det_ratio
    {H A : MetricTensor n} {r c : Fin n} (hH : H.det = 0)
    (hm : H.adjugate r c ≠ 0) (hA : fderiv ℝ Matrix.det H A ≠ 0)
    (B : MetricTensor n) :
    minorLeftNullvector H A r c ⬝ᵥ (B *ᵥ minorRightNullvector H r c) =
      fderiv ℝ Matrix.det H B / fderiv ℝ Matrix.det H A := by
  have ht : minorTransportCoefficient H A r c = H.adjugate r c * fderiv ℝ Matrix.det H A :=
    (NullTransport.minor_mul_fderiv_det hH hm A).symm
  simp only [minorLeftNullvector, minorRightNullvector, mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← NullTransport.minor_mul_fderiv_det hH hm B, ht]
  field_simp

/-- Differentiate the actual characteristic equation with physical position
fixed. The resulting implicit derivative retains the time coefficient and
the sign of the spatial covector direction
(`app:ch_regular_base:lem:characteristic-kernel`, transport step). -/
theorem pencilRoot_covector_derivative
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D,
      determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0)
    {w : RootState (Euclidean d)} (hw : w ∈ D) (v : Euclidean d) :
    fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
        (e.symm (h w, w.2.2)) (e.symm (0, v)) =
      -fderiv ℝ h w (0, (0, v)) *
        fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
          (e.symm (h w, w.2.2)) (e.symm (1, 0)) := by
  let j : Euclidean d → RootState (Euclidean d) := fun η ↦ (w.1, (w.2.1, η))
  have hj : HasFDerivAt j
      ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d × Euclidean d)).comp
        (ContinuousLinearMap.inr ℝ (Euclidean d) (Euclidean d))) w.2.2 := by
    convert!
      (hasFDerivAt_const (𝕜 := ℝ) w.1 w.2.2).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) w.2.1 w.2.2).prodMk
          (hasFDerivAt_id (𝕜 := ℝ) w.2.2)) using 1
  have hh' : HasFDerivAt h (fderiv ℝ h w) (j w.2.2) :=
    ((hh.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hη := hh'.comp w.2.2 hj
  have hξ := e.symm.hasFDerivAt.comp w.2.2 (hη.prodMk (hasFDerivAt_id w.2.2))
  have hf := (hasFDerivAt_determinant (Q (e.symm (w.1, w.2.1)))
    (e.symm (h w, w.2.2))).differentiableAt.hasFDerivAt.comp w.2.2 hξ
  have heq : (fun η ↦ determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h (j η), η)))
      =ᶠ[𝓝 w.2.2] (fun _ ↦ (0 : ℝ)) := by
    have hjcont : Continuous j := continuous_const.prodMk (continuous_const.prodMk continuous_id)
    filter_upwards [hjcont.continuousAt.preimage_mem_nhds (hD.mem_nhds hw)] with η hηD
    exact hroot (j η) hηD
  have he := (hf.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_const (0 : ℝ) w.2.2)
  have hev := congrArg (fun L : Euclidean d →L[ℝ] ℝ ↦ L v) he
  change fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
    (e.symm (h w, w.2.2)) (e.symm (fderiv ℝ h w (0, (0, v)), v)) = 0 at hev
  have hsplit : (fderiv ℝ h w (0, (0, v)), v) =
      fderiv ℝ h w (0, (0, v)) • (1, (0 : Euclidean d)) + (0, v) := by simp
  rw [hsplit, map_add, map_smul, map_add, map_smul] at hev
  change fderiv ℝ h w (0, (0, v)) *
      fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
        (e.symm (h w, w.2.2)) (e.symm (1, 0)) + _ = 0 at hev
  linarith

/-- The actual normalized minor coefficients have spatial velocity `-h_η`,
as required by the row transport on `twoTimePhase`'s Hamilton flow. This
derives the coefficient premise of `firstOrder_left_smul` from the pencil
root, rather than assuming the transport direction
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootPencil_normalized_spatial_coefficient
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hroot : ∀ w ∈ D,
      determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0)
    {w : RootState (Euclidean d)} (hw : w ∈ D) {r c : Fin n}
    (hm : (rootPencil e Q h w).adjugate r c ≠ 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
      (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) (v : Euclidean d) :
    minorLeftNullvector (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ⬝ᵥ
      (pencil (Q (e.symm (w.1, w.2.1))) (e.symm (0, v)) *ᵥ
        minorRightNullvector (rootPencil e Q h w) r c) =
      -⟪rootMomentumGradient h w, v⟫_ℝ := by
  have hA : fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 := by
    rwa [rootPencil_time_derivative]
  rw [minorLeft_mulVec_minorRight_eq_det_ratio (H := rootPencil e Q h w) (hroot w hw) hm hA,
    rootPencil_time_derivative, inner_rootMomentumGradient]
  have hB : fderiv ℝ Matrix.det (rootPencil e Q h w)
      (pencil (Q (e.symm (w.1, w.2.1))) (e.symm (0, v))) =
    fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
      (e.symm (h w, w.2.2)) (e.symm (0, v)) := by
    rw [(hasFDerivAt_determinant _ _).fderiv]
    rfl
  rw [hB, pencilRoot_covector_derivative e Q hD hh hroot hw v,
    mul_div_cancel_right₀ _ hgap]

/-- Choose a single minor and retain it on an open neighborhood of the actual
root. Both normalized nullvectors are smooth and satisfy the exact kernel and
transport normalization identities throughout that neighborhood. The original
simple-root condition produces both nonzero denominators at the base point;
continuity supplies the neighborhood. The phase constructor can now be applied
to this smaller root domain, so its entire flow uses these same nullvectors
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_rootPencil_minor_neighborhood
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, e.symm (w.1, w.2.1) ∈ Ω)
    (hroot : ∀ w ∈ D,
      determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0)
    {z : RootState (Euclidean d)} (hz : z ∈ D)
    (hgap : fderiv ℝ (determinant (Q (e.symm (z.1, z.2.1))))
      (e.symm (h z, z.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ r c : Fin n, ∃ V : Set (RootState (Euclidean d)),
      IsOpen V ∧ z ∈ V ∧ V ⊆ D ∧
      ContDiffOn ℝ ∞ (fun w ↦ minorRightNullvector (rootPencil e Q h w) r c) V ∧
      ContDiffOn ℝ ∞ (fun w ↦ minorLeftNullvector (rootPencil e Q h w)
        (rootTimeCoefficient e Q w) r c) V ∧
      ∀ w ∈ V,
        let H := rootPencil e Q h w
        let A := rootTimeCoefficient e Q w
        let k := minorRightNullvector H r c
        let l := minorLeftNullvector H A r c
        H.adjugate r c ≠ 0 ∧ minorTransportCoefficient H A r c ≠ 0 ∧
        H *ᵥ k = 0 ∧ l ᵥ* H = 0 ∧ l ⬝ᵥ (A *ᵥ k) = 1 ∧
        (∀ v, H *ᵥ v = 0 → ∃ a : ℝ, v = a • k) := by
  obtain ⟨r, c, hm⟩ := exists_rootPencil_minor e Q h z hgap
  have hHs := contDiffOn_rootPencil e hQ hh hmap
  have hAs := contDiffOn_rootTimeCoefficient e hQ hmap
  have hHentry (i j : Fin n) : ContDiffOn ℝ ∞ (fun w ↦ rootPencil e Q h w i j) D :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn hHs
  have hAentry (i j : Fin n) : ContDiffOn ℝ ∞ (fun w ↦ rootTimeCoefficient e Q w i j) D :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn hAs
  have hminor := NullTransport.contDiffOn_adjugate_entry hHentry r c
  have htransport := contDiffOn_minorTransportCoefficient r c hHentry hAentry
  let V := D ∩ {w | (rootPencil e Q h w).adjugate r c ≠ 0} ∩
    {w | minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c ≠ 0}
  have hV : IsOpen V := by
    convert! (hminor.continuousOn.isOpen_inter_preimage hD isOpen_ne).inter
      (htransport.continuousOn.isOpen_inter_preimage hD isOpen_ne) using 1
    ext w
    simp only [V, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    tauto
  have ht : minorTransportCoefficient (rootPencil e Q h z) (rootTimeCoefficient e Q z) r c ≠ 0 :=
    minorTransportCoefficient_ne_zero_of_root (hroot z hz) hm
      (by rwa [rootPencil_time_derivative])
  refine ⟨r, c, V, ?_, ⟨⟨hz, hm⟩, ht⟩, fun _ hw ↦ hw.1.1, ?_, ?_, ?_⟩
  · exact hV
  · exact contDiffOn_minorRightNullvector r c (fun i j ↦ (hHentry i j).mono
      (fun _ hw ↦ hw.1.1)) (fun _ hw ↦ hw.1.2)
  · exact contDiffOn_minorLeftNullvector r c (fun i j ↦ (hHentry i j).mono
      (fun _ hw ↦ hw.1.1)) (fun i j ↦ (hAentry i j).mono (fun _ hw ↦ hw.1.1))
        (fun _ hw ↦ hw.2)
  · intro w hw
    exact ⟨hw.1.2, hw.2, minor_normalization (hroot w hw.1.1) hw.1.2 hw.2⟩

/-- Applying the existing complement constructor to the actual root pencil
discharges its characteristic, minor and simple-root inputs. This gives the
literal off-root inverse identities for `H(x,τ,η)` on a positive interval,
with the same normalized nullvectors
(`app:ch_regular_base:eq:complement-symbol`). -/
theorem exists_rootPencil_complement
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (h : RootState (Euclidean d) → ℝ)
    (w : RootState (Euclidean d))
    (hp : determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
      (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) :
    ∃ r c : Fin n, ∃ ε > (0 : ℝ),
      let H := rootPencil e Q h w
      let A := rootTimeCoefficient e Q w
      let k := minorRightNullvector H r c
      let l := minorLeftNullvector H A r c
      H *ᵥ k = 0 ∧ l ᵥ* H = 0 ∧ l ⬝ᵥ (A *ᵥ k) = 1 ∧
      ContDiffOn ℝ ∞ (minorComplementInverse H A r c) (ball 0 ε) ∧
      ∀ t : ℝ, |t - h w| < ε →
        pencil (Q (e.symm (w.1, w.2.1))) (e.symm (t, w.2.2)) *
            minorComplementInverse H A r c (t - h w) = complementProjection A k l ∧
        (l ᵥ* A) ᵥ* minorComplementInverse H A r c (t - h w) = 0 := by
  obtain ⟨r, c, hm⟩ := exists_rootPencil_minor e Q h w hgap
  have hH : (rootPencil e Q h w).det = 0 := hp
  have hA : fderiv ℝ Matrix.det (rootPencil e Q h w) (rootTimeCoefficient e Q w) ≠ 0 := by
    rwa [rootPencil_time_derivative]
  obtain ⟨hk, hl, hn, _⟩ := minor_normalization hH hm
    (minorTransportCoefficient_ne_zero_of_root hH hm hA)
  obtain ⟨ε, hε, hsmooth, hspec⟩ := exists_smooth_minorComplementInverse
    (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c hH hm hA
  refine ⟨r, c, ε, hε, hk, hl, hn, hsmooth, ?_⟩
  intro t ht
  have he : pencil (Q (e.symm (w.1, w.2.1))) (e.symm (t, w.2.2)) =
      rootPencil e Q h w + (t - h w) • rootTimeCoefficient e Q w := by
    have hξ : (t, w.2.2) = (h w, w.2.2) + (t - h w) • (1, (0 : Euclidean d)) := by
      ext <;> simp
    rw [hξ, map_add, map_smul]
    exact (pencilContinuousLinearMap _).map_add _ _ |>.trans
      (congrArg (fun M ↦ rootPencil e Q h w + M) ((pencilContinuousLinearMap _).map_smul _ _))
  rw [he]
  exact ⟨(hspec _ ht).1, (hspec _ ht).2.1⟩

end JanetCartan.RegularSector.Characteristic
