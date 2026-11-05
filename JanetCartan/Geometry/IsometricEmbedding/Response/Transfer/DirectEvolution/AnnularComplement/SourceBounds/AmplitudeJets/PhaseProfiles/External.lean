module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.PhaseProfiles.Elapsed
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Regularity

/-!
# Joint external/source derivatives of the entire annular phase

The external variable is literally `(c,x)`. In particular the output carrier
is differentiated along with the source carrier. These estimates are consumed
by the original two-time profile producer in `PhaseProfiles`, for
`app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.PhaseProfiles
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
variable {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C] {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "D" => (C × E) × E

private def positionProjection (source : Bool) : D →L[ℝ] E :=
  if source then ContinuousLinearMap.snd ℝ (C × E) E
  else (ContinuousLinearMap.snd ℝ C E).comp (ContinuousLinearMap.fst ℝ (C × E) E)

private theorem norm_positionProjection_le (source : Bool) :
    ‖positionProjection (C := C) (d := d) source‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simp only [one_mul]
  cases source
  · exact (norm_snd_le q.1).trans (norm_fst_le q)
  · exact norm_snd_le q

private def carrierProjection (source : Bool) : D →L[ℝ] C × E :=
  ((ContinuousLinearMap.fst ℝ C E).comp (ContinuousLinearMap.fst ℝ (C × E) E)).prod
    (positionProjection source)

private theorem norm_carrierProjection_le (source : Bool) :
    ‖carrierProjection (C := C) (d := d) source‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖q.1.1‖ ‖positionProjection source q‖ ≤ 1 * ‖q‖
  rw [one_mul]
  apply max_le ((norm_fst_le q.1).trans (norm_fst_le q))
  exact ((positionProjection source).le_opNorm q).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_positionProjection_le source) (norm_nonneg q))

private theorem norm_iteratedFDeriv_comp_contraction_le
    {D₁ D₂ : Type} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
    [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    (T : D₁ →L[ℝ] D₂) (hT : ‖T‖ ≤ 1) {O : Set D₂} (hO : IsOpen O)
    {f : D₂ → ℝ} (hf : ContDiffOn ℝ ∞ f O) {q : D₁} (hq : T q ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (T y)) q‖ ≤ ‖iteratedFDeriv ℝ m f (T q)‖ := by
  have h := norm_iteratedFDeriv_preAffine_le T 0 hO hf (by simpa using hq) m
  simp only [add_zero] at h
  exact h.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg T) hT (n := m)) (norm_nonneg (iteratedFDeriv ℝ m f (T q))))

set_option maxHeartbeats 800000 in
/-- Both graph orientations and both observations have the same primitive
joint phase budget. The graph-phase premise is discharged from ORIGINAL
two-time data in `norm_iteratedFDeriv_normalizedAnnularExternalPhase_elapsed_le`.
The two carrier terms retain joint `(c,x,z)` derivatives, including order zero.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_annularExternalPhase_le
    {V : Set C} {U X : Set E} (hV : IsOpen V) (hU : IsOpen U) (hX : IsOpen X)
    (adjoint demodulated : Bool) (Θ : E → E → ℝ) (φ : C → E → ℝ)
    {lam L K R BΘ Bφ : ℝ} (hlam : 1 ≤ lam) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hR : 0 ≤ R) (hBΘ : 0 ≤ BΘ) (hBφ : 0 ≤ Bφ) (ξ : E)
    (hΘ : ContDiffOn ℝ ∞ (fun y => Θ y ξ) (U ∪ X))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X)))
    (p : C × E) (z : E) (hp : p ∈ V ×ˢ X) (hz : z ∈ U)
    (hxR : ‖p.2‖ ≤ R) (hzR : ‖z‖ ≤ R) (m : ℕ)
    (hΘb : ∀ y ∈ ({p.2, z} : Set E),
      ‖iteratedFDeriv ℝ m (fun y => Θ y ξ) y‖ ≤ BΘ * (1 + ‖ξ‖) * L ^ m)
    (hφb : ∀ y ∈ ({p.2, z} : Set E),
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (p.1, y)‖ ≤ Bφ * L ^ m) :
    ‖iteratedFDeriv ℝ m
      (Function.uncurry (annularExternalPhase adjoint demodulated Θ φ lam ξ)) (p, z)‖ ≤
      (BΘ + (R + 1) + 2 * Bφ) * (lam + ‖ξ‖) * K ^ m := by
  let q : D := (p, z)
  let g (s : Bool) : D → ℝ := fun y => Θ (positionProjection s y) ξ
  let b (s : Bool) : D → ℝ := fun y => inner ℝ (positionProjection s y) ξ
  let a (s : Bool) : D → ℝ := fun y => lam • Function.uncurry φ (carrierProjection s y)
  have hpos (s : Bool) : positionProjection s q ∈ U ∪ X := by
    cases s
    · exact Or.inr hp.2
    · exact Or.inl hz
  have hcar (s : Bool) : carrierProjection s q ∈ V ×ˢ (U ∪ X) := ⟨hp.1, hpos s⟩
  have hmem (s : Bool) : positionProjection s q ∈ ({p.2, z} : Set E) := by
    cases s <;> simp [q, positionProjection]
  have hrad (s : Bool) : ‖positionProjection s q‖ ≤ R := by
    cases s
    · exact hxR
    · exact hzR
  have hg (s : Bool) : ContDiffAt ℝ ∞ (g s) q :=
    (hΘ.contDiffAt ((hU.union hX).mem_nhds (hpos s))).comp q
      (positionProjection (C := C) (d := d) s).contDiff.contDiffAt
  have hb (s : Bool) : ContDiff ℝ ∞ (b s) :=
    (positionProjection (C := C) (d := d) s).contDiff.inner ℝ contDiff_const
  have ha (s : Bool) : ContDiffAt ℝ ∞ (a s) q :=
    ((hφ.contDiffAt ((hV.prod (hU.union hX)).mem_nhds (hcar s))).comp q
      (carrierProjection (C := C) (d := d) s).contDiff.contDiffAt).const_smul lam
  have hK : 0 ≤ K := (by linarith : 0 ≤ L).trans hLK
  have hpow : L ^ m ≤ K ^ m := pow_le_pow_left₀ (by linarith) hLK m
  have hpow1 : 1 ≤ K ^ m := one_le_pow₀ (hL.trans hLK)
  have hρ : 0 ≤ lam + ‖ξ‖ := by positivity
  have hgB (s : Bool) : ‖iteratedFDeriv ℝ m (g s) q‖ ≤ BΘ * (lam + ‖ξ‖) * K ^ m := by
    apply (norm_iteratedFDeriv_comp_contraction_le (positionProjection (C := C) (d := d) s)
      (norm_positionProjection_le (C := C) (d := d) s) (hU.union hX) hΘ (hpos s) m).trans
    apply (hΘb _ (hmem s)).trans
    gcongr
  have hbB (s : Bool) : ‖iteratedFDeriv ℝ m (b s) q‖ ≤ (R + 1) * (lam + ‖ξ‖) * K ^ m := by
    apply (norm_iteratedFDeriv_comp_contraction_le (positionProjection (C := C) (d := d) s)
      (norm_positionProjection_le (C := C) (d := d) s) isOpen_univ
      (contDiff_id.inner ℝ contDiff_const).contDiffOn (mem_univ _) m).trans
    apply (norm_iteratedFDeriv_frequencyPairing_le hR ξ _ (hrad s) m).trans
    calc
      _ ≤ (R + 1) * (lam + ‖ξ‖) := by gcongr; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow1
  have haB (s : Bool) : ‖iteratedFDeriv ℝ m (a s) q‖ ≤ Bφ * (lam + ‖ξ‖) * K ^ m := by
    have hsmooth : ContDiffAt ℝ ∞ (fun y : D => Function.uncurry φ (carrierProjection s y)) q :=
      (hφ.contDiffAt ((hV.prod (hU.union hX)).mem_nhds (hcar s))).comp q
        (carrierProjection (C := C) (d := d) s).contDiff.contDiffAt
    change ‖iteratedFDeriv ℝ m (fun y : D => lam • Function.uncurry φ (carrierProjection s y)) q‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hsmooth.of_le (by simp)), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ lam)]
    have hr := norm_iteratedFDeriv_comp_contraction_le (carrierProjection (C := C) (d := d) s)
      (norm_carrierProjection_le (C := C) (d := d) s) (hV.prod (hU.union hX)) hφ (hcar s) m
    have hr' := hr.trans (hφb _ (hmem s))
    calc
      _ ≤ lam * (Bφ * L ^ m) := mul_le_mul_of_nonneg_left hr' (by linarith)
      _ ≤ (lam + ‖ξ‖) * (Bφ * K ^ m) := by gcongr; exact le_add_of_nonneg_right (norm_nonneg ξ)
      _ = _ := by ring
  let physical : D → ℝ := if adjoint then b false - g true else g false - b true
  have hphysical : ContDiffAt ℝ ∞ physical q := by
    cases adjoint
    · exact (hg false).sub (hb true).contDiffAt
    · exact (hb false).contDiffAt.sub (hg true)
  have hphysicalB : ‖iteratedFDeriv ℝ m physical q‖ ≤
      (BΘ + (R + 1)) * (lam + ‖ξ‖) * K ^ m := by
    cases adjoint with
    | false =>
      change ‖iteratedFDeriv ℝ m (g false - b true) q‖ ≤ _
      rw [iteratedFDeriv_sub_apply ((hg false).of_le (by simp))
        ((hb true).contDiffAt.of_le (by simp))]
      exact (norm_sub_le _ _).trans ((add_le_add (hgB false) (hbB true)).trans_eq (by ring))
    | true =>
      change ‖iteratedFDeriv ℝ m (b false - g true) q‖ ≤ _
      rw [iteratedFDeriv_sub_apply ((hb false).contDiffAt.of_le (by simp))
        ((hg true).of_le (by simp))]
      exact (norm_sub_le _ _).trans ((add_le_add (hbB false) (hgB true)).trans_eq (by ring))
  let output : D → ℝ := if demodulated then a false else 0
  have houtput : ContDiffAt ℝ ∞ output q := by
    cases demodulated
    · exact contDiffAt_const
    · exact ha false
  have houtputB : ‖iteratedFDeriv ℝ m output q‖ ≤ Bφ * (lam + ‖ξ‖) * K ^ m := by
    cases demodulated
    · change ‖iteratedFDeriv ℝ m (fun _ : D => (0 : ℝ)) q‖ ≤ _
      have hzero : iteratedFDeriv ℝ m (fun _ : D => (0 : ℝ)) q = 0 := by
        cases m <;> simp
      rw [hzero, norm_zero]
      exact mul_nonneg (mul_nonneg hBφ hρ) (pow_nonneg hK m)
    · exact haB false
  have he : Function.uncurry (annularExternalPhase adjoint demodulated Θ φ lam ξ) =
      physical + a true - output := by
    funext y
    cases adjoint <;> cases demodulated <;>
      simp [Function.uncurry, annularExternalPhase, forwardCarrierSourcePhase, adjointCarrierSourcePhase,
        physical, output, a, b, g, positionProjection, carrierProjection, smul_eq_mul]
  rw [he]
  change ‖iteratedFDeriv ℝ m (physical + a true - output) q‖ ≤ _
  rw [iteratedFDeriv_sub_apply (f := physical + a true) (g := output)
    ((hphysical.add (ha true)).of_le (by simp)) (houtput.of_le (by simp)),
    iteratedFDeriv_add_apply (f := physical) (g := a true)
      (hphysical.of_le (by simp)) ((ha true).of_le (by simp))]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  exact (add_le_add (add_le_add hphysicalB (haB true)) houtputB).trans_eq (by ring)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.PhaseProfiles
