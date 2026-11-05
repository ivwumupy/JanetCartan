module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.Geometry
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.PhaseProfiles

/-!
# Primitive bounds for the literal full-source modulated phase

Apply the existing retained graph-phase bound to its parameter-independent
part. The two original full-source phase terms are bounded by fixed pullbacks
on the full parameter carrier. This preserves the chart, both orientations,
and all independent covector derivatives, with no additional derivative loss.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.FullSourceStationary
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open ResponseTransfer.DirectEvolution ResponseTransfer.RetainedFactors
open ActualCarriers.ConstructedCarrierJets

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- Both literal full-source phases have the same-order bound in the original
chart phase and original full-source phase. Only the chart contribution is
projected to the old carrier geometry; every source-phase term retains the
independent covector (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_fullSourceJointPhase_cNorm_bound
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (FullSourcePoint d)} {J : Set TC} {KP : Set (E × Param)}
    (hK : IsCompact K) (hJ : IsCompact J) (hKP : IsCompact KP)
    (hpos : ∀ v ∈ K, 0 < ℓ (spatialPart v.2.snd))
    (hmap : MapsTo (normalize ℓ ∘ fullSourceGraphPoint adj) K J)
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ KP)
    (hout : ∀ v ∈ K, v.1.2 ∈ KP) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ C : OpenPartialHomeomorph TC TC, J ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      ∀ φ : E → Param → ℝ,
        (∀ q ∈ KP, ContDiffAt ℝ ∞ (Function.uncurry φ) q) →
      ∀ m, cNorm K m (fullSourceJointPhase adj (curriedPhase ℓ C) φ) ≤
        A m * (1 + cNorm J m (twoTimePhase C) + cNorm KP m (Function.uncurry φ)) := by
  let ψ : FullSourcePoint d → RetainedCarrierPoint d :=
    fun v ↦ ((v.1.1, (v.1.2.1, v.1.2.2.1)), v.2)
  have hψ : ContDiff ℝ ∞ ψ :=
    (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk contDiff_fst.snd.snd.fst)).prodMk contDiff_snd
  let src₀ : RetainedCarrierPoint d → E × Euclidean 3 := fun v ↦ (v.2.fst, v.1.2.2)
  let out₀ : RetainedCarrierPoint d → E × Euclidean 3 := fun v ↦ v.1.2
  have hsrc₀ : Continuous src₀ :=
    ((WithLp.continuous_fst 2 E E).comp continuous_snd).prodMk continuous_fst.snd.snd
  have hout₀ : Continuous out₀ := continuous_fst.snd
  have hK₀ : IsCompact (ψ '' K) := hK.image hψ.continuous
  let KP₀ := src₀ '' (ψ '' K) ∪ out₀ '' (ψ '' K)
  have hKP₀ : IsCompact KP₀ := (hK₀.image hsrc₀).union (hK₀.image hout₀)
  obtain ⟨B, hB, hb⟩ := exists_jointRetainedCarrierPhase_cNorm_bound adj ℓ hK₀ hJ hKP₀
    (by rintro _ ⟨v, hv, rfl⟩; exact hpos v hv)
    (by rintro _ ⟨v, hv, rfl⟩; exact hmap hv)
    (fun v hv ↦ Or.inl (mem_image_of_mem src₀ hv))
    (fun v hv ↦ Or.inr (mem_image_of_mem out₀ hv))
  obtain ⟨Ag, hAg, hgraph⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK hK₀
    (fun _ _ ↦ hψ.contDiffAt) (fun _ hv ↦ mem_image_of_mem ψ hv)
  let src : FullSourcePoint d → E × Param := fun v ↦ (v.2.fst, v.1.2.2)
  let out : FullSourcePoint d → E × Param := fun v ↦ v.1.2
  have hsrcS : ContDiff ℝ ∞ src :=
    ((WithLp.fstL 2 ℝ E E).contDiff.comp contDiff_snd).prodMk contDiff_fst.snd.snd
  have houtS : ContDiff ℝ ∞ out := contDiff_fst.snd
  obtain ⟨As, hAs, hbS⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK hKP
    (fun _ _ ↦ hsrcS.contDiffAt) hsrc
  obtain ⟨Ao, hAo, hbO⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK hKP
    (fun _ _ ↦ houtS.contDiffAt) hout
  let A := fun m ↦ Ag m * B m + As m + Ao m
  refine ⟨A, fun m ↦ add_pos (add_pos (mul_pos (hAg m) (hB m)) (hAs m)) (hAo m), ?_⟩
  intro C hJC hC φ hφ m
  let f₀ := jointRetainedCarrierPhase adj (curriedPhase ℓ C) (fun _ _ ↦ 0)
  have hf₀ : ∀ v ∈ ψ '' K, ContDiffAt ℝ ∞ f₀ v := by
    rintro _ ⟨v, hv, rfl⟩
    apply contDiffAt_jointRetainedCarrierPhase adj ℓ C hC (fun _ _ ↦ 0)
    · exact ⟨by simpa [carrierGraphPoint, ψ] using hpos v hv, hJC (hmap hv)⟩
    · exact contDiffAt_const
    · exact contDiffAt_const
  have hg : cNorm K m (f₀ ∘ ψ) ≤ Ag m * B m * (1 + cNorm J m (twoTimePhase C)) := by
    have hh := hb C hJC hC (fun _ _ ↦ 0) (fun _ _ ↦ contDiffAt_const) m
    simp only [show Function.uncurry (fun (_ : E) (_ : Euclidean 3) ↦ (0 : ℝ)) = 0 from rfl,
      cNorm_zero, add_zero] at hh
    exact (hgraph f₀ hf₀ m).trans ((mul_le_mul_of_nonneg_left hh (hAg m).le).trans_eq
      (mul_assoc _ _ _).symm)
  have hgs : ∀ v ∈ K, ContDiffAt ℝ m (f₀ ∘ ψ) v :=
    fun v hv ↦ ((hf₀ _ (mem_image_of_mem ψ hv)).comp v hψ.contDiffAt).of_le (by simp)
  have hss : ∀ v ∈ K, ContDiffAt ℝ m (Function.uncurry φ ∘ src) v :=
    fun v hv ↦ ((hφ _ (hsrc v hv)).comp v hsrcS.contDiffAt).of_le (by simp)
  have hos : ∀ v ∈ K, ContDiffAt ℝ m (Function.uncurry φ ∘ out) v :=
    fun v hv ↦ ((hφ _ (hout v hv)).comp v houtS.contDiffAt).of_le (by simp)
  have heq : fullSourceJointPhase adj (curriedPhase ℓ C) φ =
      ((f₀ ∘ ψ) + (Function.uncurry φ ∘ src)) + -(Function.uncurry φ ∘ out) := by
    funext v
    simpa only [Pi.add_apply, Pi.neg_apply, Function.comp_apply, Function.uncurry,
      f₀, ψ, src, out, sub_eq_add_neg] using
      congrFun (fullSourceJointPhase_eq_zero_source adj (curriedPhase ℓ C) φ) v
  rw [heq]
  have hadd := cNorm_add_le_of_contDiffAt
    (f := (f₀ ∘ ψ) + (Function.uncurry φ ∘ src))
    (g := -(Function.uncurry φ ∘ out)) hK
    (fun v hv ↦ (hgs v hv).add (hss v hv)) (fun v hv ↦ (hos v hv).neg)
  rw [cNorm_neg] at hadd
  apply (hadd.trans (add_le_add
    ((cNorm_add_le_of_contDiffAt hK hgs hss).trans (add_le_add hg (hbS _ hφ m)))
    (hbO _ hφ m))).trans
  have h0 := cNorm_nonneg J m (twoTimePhase C)
  have h1 := cNorm_nonneg KP m (Function.uncurry φ)
  have hb0 : Ag m * B m ≤ A m := by dsimp [A]; linarith [hAs m, hAo m]
  have hb1 : As m + Ao m ≤ A m := by
    dsimp [A]; linarith [mul_pos (hAg m) (hB m)]
  calc
    _ = Ag m * B m * (1 + cNorm J m (twoTimePhase C)) +
        (As m + Ao m) * cNorm KP m (Function.uncurry φ) := by ring
    _ ≤ A m * (1 + cNorm J m (twoTimePhase C)) +
        A m * cNorm KP m (Function.uncurry φ) :=
      add_le_add (mul_le_mul_of_nonneg_right hb0 (by linarith))
        (mul_le_mul_of_nonneg_right hb1 h1)
    _ = _ := by ring

/-- Freezing elapsed time costs neither derivatives nor a scale factor. This
is the precise joint spatial/parameter jet needed by both integrated-envelope
orientations, deduced from the full retained joint phase
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_fullSourceJointPhase_fixedTime_jet_le
    (adj : Bool) (Ψ : TwoTimePhase d) (φ : E → (Euclidean 3 × Euclidean d) → ℝ)
    (t : ℝ) {p : (E × (Euclidean 3 × Euclidean d)) × CarrierVariables (d + 1)}
    (hf : ContDiffAt ℝ ∞ (fullSourceJointPhase adj Ψ φ) ((t, p.1), p.2)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : (E × (Euclidean 3 × Euclidean d)) × CarrierVariables (d + 1) ↦
      fullSourceJointPhase adj Ψ φ ((t, q.1), q.2)) p‖ ≤
      ‖iteratedFDeriv ℝ j (fullSourceJointPhase adj Ψ φ) ((t, p.1), p.2)‖ := by
  let L : ((E × (Euclidean 3 × Euclidean d)) × CarrierVariables (d + 1)) →L[ℝ] FullSourcePoint d :=
    ((0 : ((E × (Euclidean 3 × Euclidean d)) × CarrierVariables (d + 1)) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)
  let b : FullSourcePoint d := ((t, 0), 0)
  let f := fullSourceJointPhase adj Ψ φ
  let g := fun v ↦ f (v + b)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun q ↦ by
    simp [L, Prod.norm_def])
  have hg : ContDiffAt ℝ ∞ g (L p) := by
    have he : L p + b = ((t, p.1), p.2) := by simp [L, b]
    exact (he ▸ hf).comp (L p) (contDiffAt_id.add contDiffAt_const)
  obtain ⟨S, hS, hgS⟩ := hg.contDiffOn (m := (j : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨V, hVS, hV, hp⟩ := _root_.mem_nhds_iff.mp hS
  have hpre := hV.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right (hgS.mono hVS)
    hV.uniqueDiffOn hpre.uniqueDiffOn hp (i := j) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hpre hp,
    iteratedFDerivWithin_of_isOpen _ hV hp] at he
  have hb := (iteratedFDeriv ℝ j g (L p)).norm_compContinuousLinearMap_le (fun _ ↦ L)
  have hb' : ‖iteratedFDeriv ℝ j (g ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ j g (L p)‖ := by
    rw [he]
    apply hb.trans
    simpa using mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ j g (L p)))
      (show ∏ _ : Fin j, ‖L‖ ≤ 1 from by
        simpa using pow_le_one₀ (norm_nonneg L) hL (n := j))
  simpa [g, f, Function.comp_def, L, b, iteratedFDeriv_comp_add_right] using hb'

end JanetCartan.FullSourceStationary
