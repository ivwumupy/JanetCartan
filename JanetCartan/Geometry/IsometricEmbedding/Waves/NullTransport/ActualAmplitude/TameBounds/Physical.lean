module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Forward

/-!
# Joint amplitude estimate in physical coordinates

The literal characteristic formula and its nullvector product are controlled
on the physical image of the retained compact working cylinder. The reserve
eight comes from two varying compositions and two products. Only fixed low
budgets on the physical coefficient, forward/inverse flow, initial scalar and
nullvector occur. The next specialization derives these budgets from the
producer's coefficient/flow estimates and a fixed immersion budget.
Source: `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame

variable {E X V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The joint scalar/vector estimate on the prescribed physical compact set.
All low inputs are estimates of primitive functions; no integral, exponential
or amplitude bound is assumed. The larger initial domain contains its closed
norm ball (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_physicalTransport_bounds
    (C : X ≃L[ℝ] ℝ × E) (a : X) (p : E) {ρ τ R : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hR : 0 < R) (hτR : τ ≤ R / 16)
    (hcenter : C.symm (0, p) = a)
    (hbuffer : MapsTo C.symm (closedBall (0, p) R) (closedBall a ρ))
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (Φ Y : ℝ × E → E) (c : X → ℝ) (k : X → V) (r : E → ℝ),
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)) →
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ c x) →
      (∀ x ∈ closedBall a ρ, ContDiffAt ℝ ∞ k x) → ContDiffOn ℝ ∞ r (ball p (R / 4)) →
      MapsTo (fun q ↦ (q.1, Φ q))
        (Ioo (-τ) τ ×ˢ ball p (R / 8)) (Ioo (-τ) τ ×ˢ ball p (R / 4)) →
      MapsTo (fun q ↦ (q.1, Y q)) (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p (R / 64))
        (Icc (-τ) τ ×ˢ closedBall p (R / 8)) →
      cNorm (Icc (-τ) τ ×ˢ closedBall p (R / 8)) 7 Φ ≤ M →
      cNorm (Icc (-τ) τ ×ˢ closedBall p (R / 8)) 5 Y ≤ M →
      cNorm (closedBall a ρ) 7 c ≤ M → cNorm (closedBall a ρ) 1 k ≤ M →
      cNorm (closedBall p (R / 8)) 5 r ≤ M →
      let K := Icc (-τ / 2) (τ / 2) ×ˢ closedBall p (R / 64)
      let J := Icc (-τ) τ ×ˢ closedBall p (R / 8)
      let α := transportFromFootpoint (flowTransportCoefficient (c ∘ C.symm) Φ) 0 r Y ∘ C
      ∀ j, cNorm (C.symm '' K) j α + cNorm (C.symm '' K) j (fun x ↦ α x • k x) ≤
        B j * (1 + cNorm J (j + 8) Φ + cNorm J (j + 8) Y +
          cNorm (closedBall a ρ) (j + 8) c + cNorm (closedBall a ρ) (j + 8) k +
          cNorm (closedBall p (R / 8)) (j + 8) r) := by
  let K := Icc (-τ / 2) (τ / 2) ×ˢ closedBall p (R / 64)
  let J := Icc (-τ) τ ×ˢ closedBall p (R / 8)
  let U := Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)
  let e := timeDilation (E := E) ((τ / 2) / (R / 64))
    (div_pos (by positivity : 0 < τ / 2) (by positivity)).ne'
  have he : e '' closedBall (0, p) (R / 64) = K := by
    simpa only [e, K, neg_div] using timeDilation_image_closedBall p
      (by positivity : 0 < τ / 2) (by positivity : 0 < R / 64)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_ball
  have hJ : IsCompact J := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKJ : K ⊆ J := (workingCylinder_subsets p hτ hR).2
  have hJU : J ⊆ U := coefficientCylinder_subset_buffer p hτ hR
  have hKU := hKJ.trans hJU
  have hhalf : MapsTo C.symm K (closedBall a (ρ / 2)) := by
    apply (mapsTo_half_closedBall C.symm.toContinuousLinearMap (0, p) a hcenter hbuffer).mono_left
    intro q hq
    rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, sub_zero]
    refine ⟨?_, (mem_closedBall.mp hq.2).trans (by linarith)⟩
    rw [abs_le]
    constructor <;> linarith [hq.1.1, hq.1.2]
  let L := fun j ↦ linearNormCost C.symm.toContinuousLinearMap j
  have hL j : 0 < L j := linearNormCost_pos _ _
  obtain ⟨A, hA, hforward⟩ := exists_cNorm_forwardCoefficient_bounds C a p hρ hτ hR hτR hcenter hbuffer hM
  let M' := M + A 5 * (1 + 2 * M) + L 1 * M
  have hM' : 0 ≤ M' := by
    dsimp [M']
    have := hA 5
    have := hL 1
    positivity
  obtain ⟨B, hB, hvector⟩ := exists_cNorm_transportAmplitude_bounds (F := V)
    e (0, p) p (by positivity : 0 < R / 64) hτ (by positivity : 0 < R / 8) hM'
  let P := fun j ↦ linearNormCost C.toContinuousLinearMap j
  have hP j : 0 < P j := linearNormCost_pos _ _
  let H := fun j ↦ P j * B j * (1 + A (j + 6) + L (j + 6))
  refine ⟨H, fun j ↦ mul_pos (mul_pos (hP j) (hB j))
    (by linarith [hA (j + 6), hL (j + 6)]), ?_⟩
  intro Φ Y c k r hΦ hY hc hk hr hmΦ hmY hΦlow hYlow hclow hklow hrlow
  let c' := flowTransportCoefficient (c ∘ C.symm) Φ
  let k' := k ∘ C.symm
  have hcball : ContDiffOn ℝ ∞ c (ball a ρ) :=
    fun x hx ↦ (hc x (ball_subset_closedBall hx)).contDiffWithinAt
  have hkball : ContDiffOn ℝ ∞ k (ball a ρ) :=
    fun x hx ↦ (hk x (ball_subset_closedBall hx)).contDiffWithinAt
  have hk' : ContDiffOn ℝ ∞ k' (C.symm ⁻¹' ball a ρ) :=
    hkball.comp C.symm.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hKk : K ⊆ C.symm ⁻¹' ball a ρ :=
    fun q hq ↦ closedBall_subset_ball (by linarith) (hhalf hq)
  have hkn (i) : cNorm K i k' ≤ L i * cNorm (closedBall a ρ) i k := by
    apply (cNorm_comp_linear_le C.symm.toContinuousLinearMap (isCompact_closedBall _ _)
      isOpen_ball (closedBall_subset_ball (by linarith : ρ / 2 < ρ)) hkball hhalf i).trans
    exact mul_le_mul_of_nonneg_left
      (cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ))
        (isCompact_closedBall _ _) (fun x hx ↦ (hk x hx).of_le (by simp))) (hL i).le
  have hYn (i) : cNorm K i Y ≤ cNorm J i Y := cNorm_mono_set_of_contDiffAt hKJ hJ
    (fun q hq ↦ (hY.contDiffAt (hU.mem_nhds (hJU hq))).of_le (by simp))
  have hcn (i) : cNorm J i c' ≤ A i * (1 + cNorm J (i + 2) Φ + cNorm (closedBall a ρ) (i + 2) c) :=
    hforward Φ c hΦ hc hmΦ
      ((cNorm_mono_order (by omega : 1 ≤ 7)).trans hΦlow)
      ((cNorm_mono_order (by omega : 1 ≤ 7)).trans hclow) i
  obtain ⟨Vc, hVc, hJVc, hc'⟩ := exists_forwardCoefficient_smooth_near
    C a p hρ hτ hR hτR hcenter hbuffer hΦ hc hmΦ
  have hMle : M ≤ M' := by
    dsimp [M']
    have := hA 5
    have := hL 1
    nlinarith
  have hc5 : cNorm J 5 c' ≤ M' := by
    have hh := hcn 5
    change _ ≤ A 5 * (1 + cNorm J 7 Φ + cNorm (closedBall a ρ) 7 c) at hh
    apply hh.trans
    dsimp [M']
    nlinarith [hA 5, hL 1]
  have hk1 : cNorm K 1 k' ≤ M' := by
    apply ((hkn 1).trans (mul_le_mul_of_nonneg_left hklow (hL 1).le)).trans
    dsimp [M']
    nlinarith [hA 5]
  have hBL : closedBall p (R / 8) ⊆ ball p (R / 4) := closedBall_subset_ball (by linarith)
  have hv (j) := hvector U Vc (C.symm ⁻¹' ball a ρ) (ball p (R / 4))
    hU hVc (isOpen_ball.preimage C.symm.continuous) isOpen_ball
    (he ▸ hKU) hJVc (he ▸ hKk) hBL Y c' r k' hY hc' hr hk'
    (he ▸ hmY) (he ▸ ((hYn 5).trans (hYlow.trans hMle))) hc5
    (hrlow.trans hMle) (he ▸ hk1) j
  have hscalar := exists_transportFromFootpoint_smooth_near hτ (by positivity : 0 < R / 8)
    hU hVc isOpen_ball hKU hJVc hBL hY hc' hr hmY
  obtain ⟨W, hW, hKW, hα⟩ := hscalar
  let α := transportFromFootpoint c' 0 r Y
  have hαphys (j) : cNorm (C.symm '' K) j (α ∘ C) ≤ P j * cNorm K j α :=
    cNorm_comp_linear_le C.toContinuousLinearMap hK hW hKW hα
      (by rintro _ ⟨q, hq, rfl⟩; simpa using hq) j
  have hbreg : ContDiffOn ℝ ∞ (fun q ↦ α q • k' q) (W ∩ C.symm ⁻¹' ball a ρ) :=
    (hα.mono inter_subset_left).smul (hk'.mono inter_subset_right)
  have hbphys (j) : cNorm (C.symm '' K) j (fun x ↦ α (C x) • k x) ≤
      P j * cNorm K j (fun q ↦ α q • k' q) := by
    have hh := cNorm_comp_linear_le C.toContinuousLinearMap hK
      (hW.inter (isOpen_ball.preimage C.symm.continuous)) (fun q hq ↦ ⟨hKW hq, hKk hq⟩)
      hbreg (S := C.symm '' K) (by rintro _ ⟨q, hq, rfl⟩; simpa using hq) j
    simpa only [Function.comp_def, k', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hh
  dsimp only
  intro j
  have hvj := hv j
  rw [he] at hvj
  apply (add_le_add (hαphys j) (hbphys j)).trans
  rw [← mul_add]
  apply (mul_le_mul_of_nonneg_left hvj (hP j).le).trans
  let Z := 1 + cNorm J (j + 8) Φ + cNorm J (j + 8) Y +
    cNorm (closedBall a ρ) (j + 8) c + cNorm (closedBall a ρ) (j + 8) k +
    cNorm (closedBall p (R / 8)) (j + 8) r
  have hzY : cNorm K (j + 6) Y ≤ cNorm J (j + 8) Y :=
    (hYn _).trans (cNorm_mono_order (by omega))
  have hzC := hcn (j + 6)
  simp only [Nat.add_assoc] at hzC
  have hzK : cNorm K (j + 6) k' ≤ L (j + 6) * cNorm (closedBall a ρ) (j + 8) k :=
    (hkn _).trans (mul_le_mul_of_nonneg_left (cNorm_mono_order (by omega)) (hL _).le)
  have hzR := cNorm_mono_order (s := closedBall p (R / 8)) (f := r) (by omega : j + 6 ≤ j + 8)
  have hi : 1 + cNorm K (j + 6) Y + cNorm J (j + 6) c' +
      cNorm (closedBall p (R / 8)) (j + 6) r + cNorm K (j + 6) k' ≤
      (1 + A (j + 6) + L (j + 6)) * Z := by
    have hy0 := cNorm_nonneg J (j + 8) Y
    have hf0 := cNorm_nonneg J (j + 8) Φ
    have hc0 := cNorm_nonneg (closedBall a ρ) (j + 8) c
    have hk0 := cNorm_nonneg (closedBall a ρ) (j + 8) k
    have hr0 := cNorm_nonneg (closedBall p (R / 8)) (j + 8) r
    dsimp [Z]
    nlinarith [hA (j + 6), hL (j + 6),
      mul_nonneg (hA (j + 6)).le hy0, mul_nonneg (hA (j + 6)).le hk0,
      mul_nonneg (hA (j + 6)).le hr0, mul_nonneg (hL (j + 6)).le hy0,
      mul_nonneg (hL (j + 6)).le hf0, mul_nonneg (hL (j + 6)).le hc0,
      mul_nonneg (hL (j + 6)).le hr0]
  have hh := mul_le_mul_of_nonneg_left hi (mul_nonneg (hP j).le (hB j).le)
  simpa only [H, mul_assoc] using hh

end JanetCartan.NullTransport.AmplitudeTame
