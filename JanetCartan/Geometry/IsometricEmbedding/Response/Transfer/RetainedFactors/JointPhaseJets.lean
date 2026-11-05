module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryPrimaryPhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.KernelIdentity

/-!
# Joint phase jets for the same retained direct factors

The forward and literal-adjoint modulated phases are assembled from the actual
retained conic phase, the same primary phase, and the fixed time/position
pairings. The compact jet estimate is linear in the original phase seminorms
at the same order. Elapsed time is included among the joint variables.

The smooth representative has exactly the same germ on the full supplied
buffer, so this assembly preserves all derivatives, critical equations and
Hessians there. Common-carrier containment and its positive spatial-frequency
gap remain actual geometric obligations. No envelope bound is asserted.
Consumer: the primitive phase input of `IntegratedEnvelope.Assembly`, for
`app:ch_response:eq:direct-envelope-profile` in paper.tex.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution
open DirectEvolution.CompactTransfer ActualCarriers.ConstructedCarrierJets

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- Joint variables of the retained carrier, including elapsed time
(`app:ch_response:eq:direct-envelope-profile`). -/
abbrev RetainedCarrierPoint (d : ℕ) :=
  (ℝ × (Euclidean (d + 1) × Euclidean 3)) × CarrierVariables (d + 1)

/-- The original graph point in each literal orientation; adjunction exchanges
only the physical positions (`app:ch_response:eq:fixed-factor-transfer`). -/
def carrierGraphPoint (adj : Bool) (v : RetainedCarrierPoint d) : T :=
  let x := if adj then v.2.fst else v.1.2.1
  (x 0, (x 0 - v.1.1, (spatialPart x, spatialPart v.2.snd)))

/-- Fixed polynomial part of the elapsed carrier phase, retaining its lower
time endpoint and the adjoint sign (`app:ch_response:eq:direct-envelope-profile`). -/
def carrierPolynomial (adj : Bool) (v : RetainedCarrierPoint d) : ℝ :=
  if adj then inner ℝ v.1.2.1 v.2.snd - (v.2.fst 0 - v.1.1) * v.2.snd 0
  else (v.1.2.1 0 - v.1.1) * v.2.snd 0 - inner ℝ v.2.fst v.2.snd

/-- The actual forward or literal-adjoint phase, with elapsed time included
among the joint variables (`app:ch_response:eq:direct-envelope-profile`). -/
def jointRetainedCarrierPhase (adj : Bool) (Ψ : TwoTimePhase d)
    (φ : E → Euclidean 3 → ℝ) (v : RetainedCarrierPoint d) : ℝ :=
  if adj then adjointCarrierPhase (elapsedPhase Ψ v.1.1) φ v.1.2 v.2
  else elapsedCarrierPhase Ψ v.1.1 φ v.1.2 v.2

/-- The literal graph-point map is smooth in both orientations, including
elapsed time (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_carrierGraphPoint (adj : Bool) :
    ContDiff ℝ ∞ (carrierGraphPoint (d := d) adj) := by
  have hz : ContDiff ℝ ∞ (fun v : RetainedCarrierPoint d ↦ v.2.fst) :=
    (WithLp.fstL 2 ℝ E E).contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun v : RetainedCarrierPoint d ↦ v.2.snd) :=
    (WithLp.sndL 2 ℝ E E).contDiff.comp contDiff_snd
  cases adj
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp
      contDiff_fst.snd.fst).prodMk
      ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp
        contDiff_fst.snd.fst).sub contDiff_fst.fst).prodMk
        ((spatialPartCLM.contDiff.comp contDiff_fst.snd.fst).prodMk
          (spatialPartCLM.contDiff.comp hθ)))
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp hz).prodMk
      ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp hz).sub
        contDiff_fst.fst).prodMk ((spatialPartCLM.contDiff.comp hz).prodMk
          (spatialPartCLM.contDiff.comp hθ)))

private theorem contDiff_carrierPolynomial (adj : Bool) :
    ContDiff ℝ ∞ (carrierPolynomial (d := d) adj) := by
  have hz : ContDiff ℝ ∞ (fun v : RetainedCarrierPoint d ↦ v.2.fst) :=
    (WithLp.fstL 2 ℝ E E).contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun v : RetainedCarrierPoint d ↦ v.2.snd) :=
    (WithLp.sndL 2 ℝ E E).contDiff.comp contDiff_snd
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff (n := ∞)
  cases adj
  · exact (((ht.comp contDiff_fst.snd.fst).sub contDiff_fst.fst).mul
      (ht.comp hθ)).sub (hz.inner ℝ hθ)
  · exact (contDiff_fst.snd.fst.inner ℝ hθ).sub
      (((ht.comp hz).sub contDiff_fst.fst).mul (ht.comp hθ))

private theorem jointRetainedCarrierPhase_eq (adj : Bool)
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (φ : E → Euclidean 3 → ℝ) :
    jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ =
      fun v ↦ carrierPolynomial adj v +
        (if adj then -(phase ℓ C (carrierGraphPoint adj v))
          else phase ℓ C (carrierGraphPoint adj v)) + φ v.2.fst v.1.2.2 - φ v.1.2.1 v.1.2.2 := by
  funext v
  cases adj <;> simp only [jointRetainedCarrierPhase, carrierPolynomial, carrierGraphPoint,
    Bool.false_eq_true, ↓reduceIte, elapsedCarrierPhase, carrierPhase, adjointCarrierPhase,
    elapsedPhase, curriedPhase] <;> ring

/-- The actual demodulated phase has a bound linear in the ORIGINAL chart
and primary-phase jets at the SAME order, in both literal orientations.
Constants depend only on fixed compact carriers and normalization geometry;
no critical-map or modulated-phase estimate is assumed. This is the primitive
phase input of the integrated envelope theorem
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_jointRetainedCarrierPhase_cNorm_bound
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (RetainedCarrierPoint d)} {J : Set T} {P : Set (E × Euclidean 3)}
    (hK : IsCompact K) (hJ : IsCompact J) (hP : IsCompact P)
    (hpos : ∀ v ∈ K, 0 < ℓ (spatialPart v.2.snd))
    (hmap : MapsTo (normalize ℓ ∘ carrierGraphPoint adj) K J)
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ P)
    (hout : ∀ v ∈ K, v.1.2 ∈ P) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ C : OpenPartialHomeomorph T T, J ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      ∀ φ : E → Euclidean 3 → ℝ,
        (∀ q ∈ P, ContDiffAt ℝ ∞ (Function.uncurry φ) q) →
      ∀ m, cNorm K m (jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ) ≤
        A m * (1 + cNorm J m (twoTimePhase C) + cNorm P m (Function.uncurry φ)) := by
  let ψ := carrierGraphPoint (d := d) adj
  let src := fun v : RetainedCarrierPoint d ↦ (v.2.fst, v.1.2.2)
  let out := fun v : RetainedCarrierPoint d ↦ v.1.2
  have hψ := contDiff_carrierGraphPoint (d := d) adj
  have hsrcSmooth : ContDiff ℝ ∞ src :=
    ((WithLp.fstL 2 ℝ E E).contDiff.comp contDiff_snd).prodMk contDiff_fst.snd.snd
  have houtSmooth : ContDiff ℝ ∞ out := contDiff_fst.snd
  have hψK : IsCompact (ψ '' K) := hK.image hψ.continuous
  obtain ⟨Ag, hAg, hg⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK hψK
    (fun _ _ ↦ hψ.contDiffAt) (fun _ hv ↦ mem_image_of_mem ψ hv)
  obtain ⟨As, hAs, hs⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK hP
    (fun _ _ ↦ hsrcSmooth.contDiffAt) hsrc
  obtain ⟨Ao, hAo, ho⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK hP
    (fun _ _ ↦ houtSmooth.contDiffAt) hout
  let Ag' := fun m ↦ Ag m * jetBoundConstant ℓ (ψ '' K) m
  let A := fun m ↦ 1 + cNorm K m (carrierPolynomial adj) + Ag' m + As m + Ao m
  have hAg' m : 0 < Ag' m := mul_pos (hAg m) (jetBoundConstant_pos _ _ _)
  refine ⟨A, fun m ↦ by
    have hp := cNorm_nonneg K m (carrierPolynomial adj)
    have hg := hAg' m
    have hs := hAs m
    have ho := hAo m
    dsimp [A]
    positivity, ?_⟩
  intro C hJC hC φ hφ m
  have hψpos : ∀ q ∈ ψ '' K, 0 < ℓ q.2.2.2 := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [ψ, carrierGraphPoint] using hpos v hv
  have hψmap : MapsTo (normalize ℓ) (ψ '' K) J := by
    rintro _ ⟨v, hv, rfl⟩
    exact hmap hv
  have hc : ∀ q ∈ ψ '' K, ContDiffAt ℝ ∞ (phase ℓ C) q := fun q hq ↦
    (contDiffOn_phase ℓ hC).contDiffAt ((isOpen_domain ℓ C.open_target).mem_nhds
      ⟨hψpos q hq, hJC (hψmap hq)⟩)
  have hgb : cNorm K m (phase ℓ C ∘ ψ) ≤ Ag' m * cNorm J m (twoTimePhase C) :=
    (hg (phase ℓ C) hc m).trans ((mul_le_mul_of_nonneg_left
      (cNorm_extend_le ℓ hψK hJ C.open_target hJC hψpos hψmap hC m)
      (hAg m).le).trans_eq (by dsimp [Ag']; ring))
  let g := fun v ↦ if adj then -(phase ℓ C (ψ v)) else phase ℓ C (ψ v)
  have hgs : ∀ v ∈ K, ContDiffAt ℝ m g v := by
    intro v hv
    have hh := ((hc _ (mem_image_of_mem ψ hv)).comp v hψ.contDiffAt).of_le
      (by simp : (m : ℕ∞ω) ≤ ∞)
    cases adj
    · exact hh
    · exact hh.neg
  have hgn : cNorm K m g ≤ Ag' m * cNorm J m (twoTimePhase C) := by
    cases adj
    · exact hgb
    · change cNorm K m (-(phase ℓ C ∘ ψ)) ≤ _
      rw [cNorm_neg]
      exact hgb
  have hss : ∀ v ∈ K, ContDiffAt ℝ m (Function.uncurry φ ∘ src) v :=
    fun v hv ↦ ((hφ _ (hsrc v hv)).comp v hsrcSmooth.contDiffAt).of_le (by simp)
  have hos : ∀ v ∈ K, ContDiffAt ℝ m (Function.uncurry φ ∘ out) v :=
    fun v hv ↦ ((hφ _ (hout v hv)).comp v houtSmooth.contDiffAt).of_le (by simp)
  have hps : ∀ v ∈ K, ContDiffAt ℝ m (carrierPolynomial adj) v :=
    fun _ _ ↦ (contDiff_carrierPolynomial adj).contDiffAt.of_le (by simp)
  have hn := cNorm_add_le_of_contDiffAt (f := (carrierPolynomial adj + g) +
      (Function.uncurry φ ∘ src)) (g := -(Function.uncurry φ ∘ out)) hK
    (fun v hv ↦ ((hps v hv).add (hgs v hv)).add (hss v hv))
    (fun v hv ↦ (hos v hv).neg)
  have hn' := cNorm_add_le_of_contDiffAt (f := carrierPolynomial adj + g)
    (g := Function.uncurry φ ∘ src) hK
    (fun v hv ↦ (hps v hv).add (hgs v hv)) hss
  have hn'' := cNorm_add_le_of_contDiffAt hK hps hgs
  have heq : jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ =
      ((carrierPolynomial adj + g) + (Function.uncurry φ ∘ src)) +
        -(Function.uncurry φ ∘ out) := by
    funext v
    simpa only [Pi.add_apply, Pi.neg_apply, Function.comp_apply, Function.uncurry,
      src, out, g, ψ, sub_eq_add_neg] using congrFun (jointRetainedCarrierPhase_eq adj ℓ C φ) v
  rw [heq]
  rw [cNorm_neg] at hn
  have hbS := hs (Function.uncurry φ) hφ m
  have hbO := ho (Function.uncurry φ) hφ m
  have hpN := cNorm_nonneg K m (carrierPolynomial adj)
  have hcN := cNorm_nonneg J m (twoTimePhase C)
  have hφN := cNorm_nonneg P m (Function.uncurry φ)
  have hb := hn.trans (add_le_add (hn'.trans (add_le_add hn'' hbS)) hbO)
  apply hb.trans
  have hpoly : cNorm K m (carrierPolynomial adj) ≤ A m := by
    dsimp only [A]
    linarith only [hAg' m, hAs m, hAo m]
  have hgraph : Ag' m ≤ A m := by
    dsimp only [A]
    linarith only [hpN, hAs m, hAo m]
  have hprimary : As m + Ao m ≤ A m := by
    dsimp only [A]
    linarith only [hpN, hAg' m]
  calc
    _ ≤ cNorm K m (carrierPolynomial adj) + Ag' m * cNorm J m (twoTimePhase C) +
        As m * cNorm P m (Function.uncurry φ) + Ao m * cNorm P m (Function.uncurry φ) :=
      add_le_add (add_le_add (add_le_add le_rfl hgn) le_rfl) le_rfl
    _ = cNorm K m (carrierPolynomial adj) + Ag' m * cNorm J m (twoTimePhase C) +
        (As m + Ao m) * cNorm P m (Function.uncurry φ) := by ring
    _ ≤ A m + A m * cNorm J m (twoTimePhase C) +
        A m * cNorm P m (Function.uncurry φ) :=
      add_le_add (add_le_add hpoly (mul_le_mul_of_nonneg_right hgraph hcN))
        (mul_le_mul_of_nonneg_right hprimary hφN)
    _ = _ := by ring

/-- Joint smoothness of the literal retained carrier phase on the ORIGINAL
nonzero-frequency overlap, before smoothing the phase globally. This supplies
the regularity used to turn compact seminorms into pointwise primitive jets
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiffAt_jointRetainedCarrierPhase
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (φ : E → Euclidean 3 → ℝ) {v : RetainedCarrierPoint d}
    (hv : carrierGraphPoint adj v ∈ domain ℓ C.target)
    (hs : ContDiffAt ℝ ∞ (Function.uncurry φ) (v.2.fst, v.1.2.2))
    (ho : ContDiffAt ℝ ∞ (Function.uncurry φ) v.1.2) :
    ContDiffAt ℝ ∞ (jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ) v := by
  have hg := ((contDiffOn_phase ℓ hC).contDiffAt
    ((isOpen_domain ℓ C.open_target).mem_nhds hv)).comp v
      (contDiff_carrierGraphPoint adj).contDiffAt
  have hsrc := hs.comp v (((WithLp.fstL 2 ℝ E E).contDiff.contDiffAt.comp v
    contDiffAt_snd).prodMk contDiffAt_fst.snd.snd)
  have hout := ho.comp v contDiffAt_fst.snd
  have hp := (contDiff_carrierPolynomial (d := d) adj).contDiffAt (x := v)
  rw [jointRetainedCarrierPhase_eq]
  cases adj
  · exact ((hp.add hg).add hsrc).sub hout
  · exact ((hp.add hg.neg).add hsrc).sub hout

/-- The smooth representative has the SAME full carrier-phase germ, including
elapsed time and both physical positions. The full normalized carrier inclusion
and the original fixed spatial-frequency gap are retained. This transfers all
primitive jets and critical/Hessian identities without changing the operator
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem jointRetainedCarrierPhase_representative_eventuallyEq
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {J : Set T}
    (he : ∀ q ∈ J, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    (φ : E → Euclidean 3 → ℝ) {v : RetainedCarrierPoint d}
    (hv : carrierGraphPoint adj v ∈ domain ℓ J)
    (hfreq : δ ≤ ‖spatialPart v.2.snd‖) :
    jointRetainedCarrierPhase adj
      (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) φ =ᶠ[𝓝 v]
      jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ := by
  have hf : δ ≤ ‖(carrierGraphPoint adj v).2.2.2‖ := by
    simpa [carrierGraphPoint] using hfreq
  have hg := (SmoothRepresentative.representative_eventuallyEq_phase ℓ C hδ he hv hf).comp_tendsto
    (contDiff_carrierGraphPoint adj).continuous.continuousAt.tendsto
  filter_upwards [hg] with w hw
  cases adj <;> simp only [jointRetainedCarrierPhase, Bool.false_eq_true, ↓reduceIte,
    elapsedCarrierPhase, carrierPhase, adjointCarrierPhase, elapsedPhase,
    SmoothRepresentative.curriedRepresentative, curriedPhase, Function.comp_apply, carrierGraphPoint] at hw ⊢ <;>
    rw [hw]

/-- No derivative loss is incurred by applying the smooth representative on
this same compact carrier. The equality covers forward and literal-adjoint
jets and all elapsed-time/parameter words
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem cNorm_jointRetainedCarrierPhase_representative_eq
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {J : Set T}
    (he : ∀ q ∈ J, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    (φ : E → Euclidean 3 → ℝ) {K : Set (RetainedCarrierPoint d)}
    (hmap : MapsTo (carrierGraphPoint adj) K (domain ℓ J))
    (hfreq : ∀ v ∈ K, δ ≤ ‖spatialPart v.2.snd‖) (m : ℕ) :
    cNorm K m (jointRetainedCarrierPhase adj
      (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) φ) =
    cNorm K m (jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ) :=
  GeometricProfile.cNorm_eq_of_eventuallyEq (fun v hv ↦
    jointRetainedCarrierPhase_representative_eventuallyEq adj ℓ C hδ he φ (hmap hv) (hfreq v hv)) m

/-- Freezing elapsed time costs neither derivatives nor a scale factor. This
is the precise joint spatial/parameter jet needed by both integrated-envelope
orientations, deduced from the full retained joint phase
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jointRetainedCarrierPhase_fixedTime_jet_le
    (adj : Bool) (Ψ : TwoTimePhase d) (φ : E → Euclidean 3 → ℝ)
    (t : ℝ) {p : (E × Euclidean 3) × CarrierVariables (d + 1)}
    (hf : ContDiffAt ℝ ∞ (jointRetainedCarrierPhase adj Ψ φ) ((t, p.1), p.2)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : (E × Euclidean 3) × CarrierVariables (d + 1) ↦
      jointRetainedCarrierPhase adj Ψ φ ((t, q.1), q.2)) p‖ ≤
      ‖iteratedFDeriv ℝ j (jointRetainedCarrierPhase adj Ψ φ) ((t, p.1), p.2)‖ := by
  let L : ((E × Euclidean 3) × CarrierVariables (d + 1)) →L[ℝ] RetainedCarrierPoint d :=
    ((0 : ((E × Euclidean 3) × CarrierVariables (d + 1)) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)
  let b : RetainedCarrierPoint d := ((t, 0), 0)
  let f := jointRetainedCarrierPhase adj Ψ φ
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

end JanetCartan.ResponseTransfer.RetainedFactors
