module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations

/-!
# The closed accepted initial-state/time carrier

For `app:ch_regular:lem:finite-chain`, the carrier retains both literal factor
supports and every intermediate root and physical point. The parameter `s ∈ [0,1]`
is independent of the elapsed endpoint. Its compactness consumes only the actual
flow's continuity on `U × [0, Δ]`, supplied by `UniformGeometry/RootFlow`, compact
initial and segment buffers, and closed `W`. No coefficient-class compactness is used.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open EvolutionIntegratedLocalization

variable {d : ℕ}

/-- Accepted root states and elapsed times, before either orientation is chosen.
Consumer: compactness of `maskedZeroEnergyRelation`
(`app:ch_regular:lem:finite-chain`, protected finite-chain paragraph). -/
def acceptedRootTimeCarrier
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ) :
    Set (RootState (Euclidean d) × ℝ) :=
  {vr | vr ∈ U ×ˢ Icc 0 Δ ∧
    (∀ s ∈ Icc (0 : ℝ) 1,
      Φ (vr.1, s * vr.2) ∈ K ∧
        e.symm ((Φ (vr.1, s * vr.2)).1, (Φ (vr.1, s * vr.2)).2.1) ∈ W) ∧
    timeSpacePoint vr.1.1 vr.1.2.1 ∈ tsupport χsource ∧
    timeSpacePoint (Φ vr).1 (Φ vr).2.1 ∈ tsupport χout}

private theorem scaledTime_mem {s r Δ : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc 0 Δ) : s * r ∈ Icc 0 Δ :=
  ⟨mul_nonneg hs.1 hr.1, (mul_le_of_le_one_left hr.1 hs.2).trans hr.2⟩

/-- The fixed unit interval describes the entire original elapsed interval,
including zero elapsed time (`app:ch_regular:lem:finite-chain`). -/
theorem forall_elapsed_iff_unitInterval {r : ℝ} (hr : 0 ≤ r) (P : ℝ → Prop) :
    (∀ t ∈ Icc 0 r, P t) ↔ ∀ s ∈ Icc (0 : ℝ) 1, P (s * r) := by
  constructor
  · intro h s hs
    exact h _ (scaledTime_mem hs ⟨hr, le_rfl⟩)
  · intro h t ht
    rcases eq_or_lt_of_le hr with he | hp
    · have ht0 : t = 0 := by linarith [ht.1, ht.2]
      simpa [← he, ht0] using h 0 (by simp)
    · have hs : t / r ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hr, (div_le_one hp).2 ht.2⟩
      simpa [div_mul_cancel₀ _ hp.ne'] using h (t / r) hs

/-- Zero source energy reconstructs the original source itself, rather than
only its spatial projection (`app:ch_regular:lem:finite-chain`). -/
theorem rootSuspensionState_eq_of_zero_energy
    (h : RootState (Euclidean d) → ℝ)
    (a : Euclidean (d + 1) × Euclidean (d + 1)) (ha : rootSuspension h a = 0) :
    rootSuspensionState h 0 (spacetimeRootState a) = a := by
  have ht : a.2 0 = h (spacetimeRootState a) := sub_eq_zero.mp ha
  unfold rootSuspensionState
  rw [zero_add, ← ht]
  simp only [spacetimeRootState, timeSpacePoint_coordinates]

/-- The carrier exactly recovers the original masks and whole-segment condition
after zero-energy suspension (`app:ch_regular:lem:finite-chain`). -/
theorem mem_acceptedRootTimeCarrier_iff
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (vr : RootState (Euclidean d) × ℝ) :
    vr ∈ acceptedRootTimeCarrier e Φ U K W χsource χout Δ ↔
      vr.2 ∈ Icc 0 Δ ∧
      (rootSuspensionState h 0 vr.1, vr.2) ∈ elapsedSegmentCarrier e h Φ U K W ∧
      (rootSuspensionState h 0 vr.1).1 ∈ tsupport χsource ∧
      (rootSuspensionState h 0 (Φ vr)).1 ∈ tsupport χout := by
  simp only [acceptedRootTimeCarrier, mem_ofPred_eq, mem_prod, elapsedSegmentCarrier,
    physicalPencilRootState, rootSuspensionState]
  constructor
  · rintro ⟨⟨hv, hr⟩, hs, hsource, hout⟩
    exact ⟨hr, ⟨hv, (forall_elapsed_iff_unitInterval hr.1 _).2 hs⟩, hsource, hout⟩
  · rintro ⟨hr, ⟨hv, hs⟩, hsource, hout⟩
    exact ⟨⟨hv, hr⟩, (forall_elapsed_iff_unitInterval hr.1 _).1 hs, hsource, hout⟩

/-- The accepted carrier is closed in the ambient initial-state/time space.
Only closed segment buffers and continuity on the fixed time buffer are needed;
there is no endpoint-only replacement of the segment
(`app:ch_regular:lem:finite-chain`). -/
theorem isClosed_acceptedRootTimeCarrier
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hU : IsClosed U) (hK : IsClosed K) (hW : IsClosed W)
    (hΦ : ContinuousOn Φ (U ×ˢ Icc 0 Δ)) :
    IsClosed (acceptedRootTimeCarrier e Φ U K W χsource χout Δ) := by
  let A := U ×ˢ Icc 0 Δ
  have hA : IsClosed A := hU.prod isClosed_Icc
  have hc s (hs : s ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun vr : RootState (Euclidean d) × ℝ ↦ Φ (vr.1, s * vr.2)) A :=
    hΦ.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
      (fun _ hv ↦ ⟨hv.1, scaledTime_mem hs hv.2⟩)
  have hsegment : IsClosed (⋂ s ∈ Icc (0 : ℝ) 1,
      A ∩ {vr | Φ (vr.1, s * vr.2) ∈ K ∧
        e.symm ((Φ (vr.1, s * vr.2)).1, (Φ (vr.1, s * vr.2)).2.1) ∈ W}) := by
    apply isClosed_biInter
    intro s hs
    have hroot := (hc s hs).preimage_isClosed_of_isClosed hA hK
    have hphysical := (e.symm.continuous.comp_continuousOn
      ((hc s hs).fst.prodMk (hc s hs).snd.fst)).preimage_isClosed_of_isClosed hA hW
    convert hroot.inter hphysical using 1
    ext vr
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    tauto
  have hsource : IsClosed (A ∩ {vr : RootState (Euclidean d) × ℝ |
      timeSpacePoint vr.1.1 vr.1.2.1 ∈ tsupport χsource}) :=
    (timeSpacePointCLM.continuous.comp
      (continuous_fst.fst.prodMk continuous_fst.snd.fst)).continuousOn
        |>.preimage_isClosed_of_isClosed hA (isClosed_tsupport χsource)
  have hout : IsClosed (A ∩ {vr | timeSpacePoint (Φ vr).1 (Φ vr).2.1 ∈ tsupport χout}) :=
    (timeSpacePointCLM.continuous.comp_continuousOn (hΦ.fst.prodMk hΦ.snd.fst)).preimage_isClosed_of_isClosed hA (isClosed_tsupport χout)
  convert (hA.inter hsegment).inter (hsource.inter hout) using 1
  ext vr
  simp only [acceptedRootTimeCarrier, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hvr, hs, hsrc, hout⟩
    exact ⟨⟨hvr, fun s hs' ↦ ⟨hvr, hs s hs'⟩⟩, ⟨hvr, hsrc⟩, hvr, hout⟩
  · rintro ⟨⟨hvr, hs⟩, ⟨_, hsrc⟩, _, hout⟩
    exact ⟨hvr, fun s hs' ↦ (hs s hs').2, hsrc, hout⟩

/-- Compactness of the closed accepted carrier, consumed by the continuous
endpoint image proof (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_acceptedRootTimeCarrier
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hU : IsCompact U) (hK : IsCompact K) (hW : IsClosed W)
    (hΦ : ContinuousOn Φ (U ×ˢ Icc 0 Δ)) :
    IsCompact (acceptedRootTimeCarrier e Φ U K W χsource χout Δ) :=
  (hU.prod isCompact_Icc).of_isClosed_subset
    (isClosed_acceptedRootTimeCarrier e χsource χout Δ hU.isClosed hK.isClosed hW hΦ)
    (fun _ hv ↦ hv.1)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
