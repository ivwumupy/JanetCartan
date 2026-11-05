module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.Refinement

/-!
# Fixed retained inverse targets from primitive transport differences

After refining the reference to a quarter-gap, the primitive order-two
transport comparison constructs smooth inverses on one fixed target. The
whole augmented differential, including positions and spectator, has a half-gap.
Uniqueness identifies these inverses with any source inverse on the overlap.

Consumer: `exists_retained_conic_primitives_sub_tolerance`, with the primitive
difference supplied by `RetainedLeading.exists_originalScalar_immersion_sub_tolerance`.
Sources: `app:ch_background:eq:bg-Psi` and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts ContinuumRow

/-- Construct genuine inverses, rather than assuming inverse continuity.
The quarter-gap comes from `exists_retained_augmented_refinement`; the
primitive `C²` tolerance is produced by the retained Hamilton comparison.
The compact target and its open buffer are fixed before the perturbation.
The final uniqueness assertion preserves compatibility with the original
source inverse wherever its inverse coordinates lie in `K` (`bg-Psi`). -/
theorem exists_retained_transport_inverse_stability
    {n : ℕ} {Y₀ : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {K W B : Set (InputVariables n)} {p₀ : InputVariables n}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hp₀ : p₀ ∈ interior K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hB : IsCompact B) (hWB : W ⊆ B)
    {V L : Set (Euclidean n × CarrierParameter)}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (hY₀ : ContDiffOn ℝ ∞ Y₀ V)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hgap₀ : ∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y₀) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 4) :
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient Y₀ p₀ ∈ interior Q ∧
    ∃ δ > (0 : ℝ), ∀ Y : Euclidean n × CarrierParameter → Euclidean (n - 1),
      ContDiffOn ℝ ∞ Y V → cNorm L 2 (Y - Y₀) < δ →
    ∃ u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ContDiffOn ℝ ∞ u Ω ∧ MapsTo (inverseCoordinates u) Ω (interior K) ∧
      MapsTo (inverseCoordinates u) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient Y (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient Y) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      InjOn (augmentedTransportGradient Y) K ∧
      (∀ (v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (q),
        q ∈ Ω → inverseCoordinates v q ∈ K →
        transportAveragedGradient Y (inverseCoordinates v q) = q.1.2.2 → u q = v q) := by
  let f := fun (Y : Euclidean n × CarrierParameter → Euclidean (n - 1)) ↦
    A.symm ∘ augmentedTransportGradient Y
  have hs (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
      (hY : ContDiffOn ℝ ∞ Y V) : ContDiffOn ℝ ∞ (augmentedTransportGradient Y) W :=
    augmentedTransportGradient_contDiffOn hW hV hIt hIIt hsegT hY
  have hfs (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
      (hY : ContDiffOn ℝ ∞ Y V) : ContDiffOn ℝ ∞ (f Y) W :=
    A.symm.contDiff.comp_contDiffOn (hs Y hY)
  have hdf (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
      (hY : ContDiffOn ℝ ∞ Y V) (p) (hp : p ∈ K) :
      fderiv ℝ (f Y) p = A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient Y) p) :=
    (A.symm.hasFDerivAt.comp p
      (((hs Y hY).contDiffAt (hW.mem_nhds (hKW hp))).differentiableAt (by simp)).hasFDerivAt).fderiv
  obtain ⟨c, hc, e, he, Vt, Lt, hVt, _, _, _, hstable⟩ :=
    exists_common_smooth_phase_inverses (P := ℝ) (f₀ := f Y₀)
      (K := {p₀}) (D₁ := interior K) (D := K)
      isCompact_singleton isOpen_interior (singleton_subset_iff.mpr hp₀)
      interior_subset hconv (ContinuousLinearEquiv.refl ℝ _)
      (fun p hp ↦ ((hfs Y₀ hY₀).contDiffAt (hW.mem_nhds (hKW hp))).differentiableAt (by simp))
      (by intro p hp; simpa only [ContinuousLinearEquiv.refl_symm,
        ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp, hdf Y₀ hY₀ p hp]
        using hgap₀ p hp)
  obtain ⟨C, hC, hforward⟩ := exists_transportForward_sub_le
    hKW hW hB hWB hV hL hLV hIt hIIt hsegT hseg A 1
  let δ := min e (1 / 4) / C
  have hδ : 0 < δ := div_pos (lt_min he (by norm_num)) hC
  have hinv (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
      (hY : ContDiffOn ℝ ∞ Y V) (hsmall : cNorm L 2 (Y - Y₀) < δ) :
      BufferedPhaseInverse (fun _ : ℝ ↦ f Y) univ {p₀} (interior K) K Vt Lt e c
        (ContinuousLinearEquiv.refl ℝ _) ∧
      (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient Y) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) := by
    have hbound : cNorm K 1 (f Y - f Y₀) < min e (1 / 4) :=
      ((hforward Y Y₀ hY hY₀).2.2).trans_lt (by
        have hh := (lt_div_iff₀ hC).mp hsmall
        simpa only [mul_comm] using hh)
    have hdiff (p) (hp : p ∈ K) :
        ‖fderiv ℝ (f Y) p - fderiv ℝ (f Y₀) p‖ ≤ 1 / 4 := by
      have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun q hq ↦ (((hfs Y hY).sub (hfs Y₀ hY₀)).contDiffAt
          (hW.mem_nhds (hKW hq))).of_le (by simp)) hp (le_refl 1)
      rw [norm_iteratedFDeriv_one] at hh
      change ‖fderiv ℝ (f Y - f Y₀) p‖ ≤ cNorm K 1 (f Y - f Y₀) at hh
      rw [fderiv_sub
        (((hfs Y hY).contDiffAt (hW.mem_nhds (hKW hp))).differentiableAt (by simp))
        (((hfs Y₀ hY₀).contDiffAt (hW.mem_nhds (hKW hp))).differentiableAt (by simp))] at hh
      exact hh.trans (hbound.le.trans (min_le_right _ _))
    refine ⟨hstable (fun _ : ℝ ↦ f Y) univ W isOpen_univ hW hKW
      ((hfs Y hY).comp contDiffOn_snd (fun _ hp ↦ hp.2)) ?_ ?_, ?_⟩
    · intro _ _ p hp
      simpa using hdiff p hp
    · intro _ _ p hp
      have hpK : p ∈ K := by
        rw [mem_singleton_iff] at hp
        exact hp ▸ interior_subset hp₀
      have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun q hq ↦ (((hfs Y hY).sub (hfs Y₀ hY₀)).contDiffAt
          (hW.mem_nhds (hKW hq))).of_le (by simp)) hpK (show 0 ≤ 1 by omega)
      rw [norm_iteratedFDeriv_zero] at hh
      exact hh.trans (hbound.le.trans (min_le_left _ _))
    · intro p hp
      apply normalized_derivative_gap_of_perturbation A (hgap₀ p hp)
      rw [ContinuousLinearMap.comp_sub, ← hdf Y hY p hp, ← hdf Y₀ hY₀ p hp]
      exact hdiff p hp
  have hself : cNorm L 2 (Y₀ - Y₀) < δ := by simpa using hδ
  have hInv₀ := (hinv Y₀ hY₀ hself).1
  let a := f Y₀ p₀
  have ha : a ∈ (fun _ : ℝ ↦ f Y₀) 0 '' ({p₀} : Set (InputVariables n)) :=
    ⟨p₀, rfl, rfl⟩
  have hsmall : closedBall a (e / 2) ⊆ Vt := by
    intro v hv
    exact hInv₀.inner_buffer 0 (mem_univ _) ((closedBall_subset_cthickening ha e)
      (closedBall_subset_closedBall (by linarith) hv))
  let Q := A '' closedBall a (e / 2)
  let Ω := A.symm ⁻¹' Vt
  have hQΩ : Q ⊆ Ω := by
    rintro _ ⟨v, hv, rfl⟩
    simpa only [Ω, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hsmall hv
  refine ⟨Q, Ω, (isCompact_closedBall a (e / 2)).image A.continuous,
    hVt.preimage A.symm.continuous, hQΩ, ?_, δ, hδ, ?_⟩
  · apply mem_interior_iff_mem_nhds.mpr
    have hh := A.isOpenMap.image_mem_nhds (closedBall_mem_nhds a (half_pos he))
    simpa only [Q, a, f, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hh
  · intro Y hY hnear
    obtain ⟨hInv, hgap⟩ := hinv Y hY hnear
    let g : Variables n × Euclidean 2 → InputVariables n := fun q ↦
      phaseChartInverse (fun _ : ℝ ↦ f Y) (interior K) 0 (A.symm q)
    let u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1) :=
      fun q ↦ ((g q).2.1.1, (g q).2.2)
    have hg : ContDiffOn ℝ ∞ g Ω := hInv.smooth.comp (f := fun q ↦ ((0 : ℝ), A.symm q))
      (contDiffOn_const.prodMk A.symm.contDiff.contDiffOn) (fun _ hq ↦ ⟨mem_univ _, hq⟩)
    have heq (q) (hq : q ∈ Ω) : augmentedTransportGradient Y (g q) = q :=
      A.symm.injective (hInv.right_inv 0 (mem_univ _) _ hq)
    have hcoords (q) (hq : q ∈ Ω) : inverseCoordinates u q = g q := by
      have hh := heq q hq
      have hx := congrArg (fun a : Variables n × Euclidean 2 ↦ a.1.1) hh
      have hy := congrArg (fun a : Variables n × Euclidean 2 ↦ a.1.2.1) hh
      have hv := congrArg (fun a : Variables n × Euclidean 2 ↦ a.2) hh
      exact Prod.ext (Prod.ext hx.symm hy.symm) (Prod.ext (Prod.ext rfl hv.symm) rfl)
    have hrange : MapsTo (inverseCoordinates u) Ω (interior K) := by
      intro q hq
      rw [hcoords q hq]
      exact hInv.inverse_mem 0 (mem_univ _) _ hq
    have hinj : InjOn (augmentedTransportGradient Y) K :=
      fun p hp q hq he ↦ hInv.injective 0 (mem_univ _) hp hq (congrArg A.symm he)
    refine ⟨u, hg.snd.fst.fst.prodMk hg.snd.snd, hrange,
      fun q hq ↦ interior_subset (hrange (hQΩ hq)), ?_, hgap, hinj, ?_⟩
    · intro q hq
      rw [hcoords q hq]
      exact congrArg (fun a : Variables n × Euclidean 2 ↦ a.1.2.2) (heq q hq)
    · intro v q hq hv he
      have hfull : augmentedTransportGradient Y (inverseCoordinates v q) = q := by
        simp only [augmentedTransportGradient, inverseCoordinates] at he ⊢
        rw [he]
      have hfullu : augmentedTransportGradient Y (inverseCoordinates u q) = q := by
        rw [hcoords q hq]
        exact heq q hq
      have hh : inverseCoordinates u q = inverseCoordinates v q :=
        hinj (interior_subset (hrange hq)) hv (hfullu.trans hfull.symm)
      exact Prod.ext (congrArg (fun p : InputVariables n ↦ p.2.1.1) hh)
        (congrArg (fun p : InputVariables n ↦ p.2.2) hh)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
