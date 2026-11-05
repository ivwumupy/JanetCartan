module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.UniformDirections
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Words
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Leibniz.Splittings

/-!
# Reapply a one-letter estimate to its actual smooth output

The fixed smooth realization supplies a jointly smooth, supported representative
of a residual letter. Its proved ordered L² envelope estimates become the exact
uniform mixed-source Fourier bounds used by the next selected characteristic
or elliptic factor. No change of representative can change the L² derivative:
the compact-family lift and local equality identify every derivative class.

Consumer: finite residual-word induction for
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.ParameterRealization.L2Family
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly

variable {d r : ℕ} {I : Type*}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem exists_smooth_l2_family_of_supported_joint
    {S : Set E} (hS : IsCompact S) (b : E × Par → F) (hb : ContDiff ℝ ∞ b)
    (hs : ∀ q, q.1 ∉ S → b q = 0) :
    ∃ g : Par → H, ContDiff ℝ ∞ g ∧ ∀ l (w : Fin l → Par) c,
      iteratedFDeriv ℝ l g c w =ᵐ[volume]
        fun x ↦ iteratedFDeriv ℝ l (fun q ↦ b (x,q)) c w := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let B : Par → C(S,F) := compactFamily (K := S) (fun c x ↦ b (x,c))
  let g : Par → H := (compactToL2Vector hS) ∘ B
  have hflip : ContDiffOn ℝ ∞ (fun q : Par × E ↦ b (q.2,q.1)) (univ ×ˢ univ) :=
    (hb.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have hB (l : ℕ) (c : Par) : ContDiffAt ℝ l B c :=
    compactFamily_contDiffAt l isOpen_univ hflip (mem_univ c)
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_infty.mpr
    intro l
    exact contDiff_iff_contDiffAt.mpr fun c ↦
      (compactToL2Vector hS).contDiff.contDiffAt.comp c (hB l c)
  refine ⟨g,hg,?_⟩
  intro l w c
  have he := (compactToL2Vector hS).iteratedFDeriv_comp_left (hB l c)
    (le_refl (l : ℕ∞ω))
  change iteratedFDeriv ℝ l g c = _ at he
  rw [he]
  change (extendZeroVector_memLp hS _).toLp _ =ᵐ[volume] _
  filter_upwards [(extendZeroVector_memLp hS
    (iteratedFDeriv ℝ l B c w)).coeFn_toLp] with x hx
  apply hx.trans
  by_cases hxS : x ∈ S
  · rw [extendZeroVector_mem _ hxS]
    have heval := (ContinuousMap.evalCLM ℝ (⟨x,hxS⟩ : S) (M := F)).iteratedFDeriv_comp_left
      (hB l c) (le_refl (l : ℕ∞ω))
    have heq : ((ContinuousMap.evalCLM ℝ (⟨x,hxS⟩ : S) (M := F)) ∘ B) =
        fun q ↦ b (x,q) := by
      funext q
      exact compactFamily_apply hflip (mem_univ q) ⟨x,hxS⟩
    rw [heq] at heval
    exact (congrArg (fun m ↦ m w) heval).symm
  · rw [extendZeroVector_notMem _ hxS]
    have heq : (fun q ↦ b (x,q)) = fun _ : Par ↦ (0 : F) :=
      funext fun q ↦ hs (x,q) hxS
    rw [heq]
    cases l with
    | zero => simp
    | succ l => simp

/-- A jointly smooth representative on one fixed compact spatial support
makes the SAME L² family smooth in all original source parameters. This is
the parameter regularity needed to split the full PDO into its annular and
complementary parts (`app:ch_response:cor:finite-jets`). -/
theorem contDiffOn_l2_of_supported_joint_representative
    {V : Set Par} (hV : IsOpen V) {S : Set E} (hS : IsCompact S)
    (b : E × Par → F) (hb : ContDiff ℝ ∞ b)
    (hs : ∀ q, q.1 ∉ S → b q = 0) (u : Par → H)
    (hu : ∀ c ∈ V, u c =ᵐ[volume] fun x ↦ b (x,c)) :
    ContDiffOn ℝ ∞ u V := by
  obtain ⟨g,hg,hgjet⟩ := exists_smooth_l2_family_of_supported_joint hS b hb hs
  intro c hc
  have hsame : u =ᶠ[𝓝 c] g := by
    filter_upwards [hV.mem_nhds hc] with a ha
    apply Lp.ext
    exact (hu a ha).trans (by simpa using (hgjet 0 (fun j ↦ j.elim0) a).symm)
  exact (hg.contDiffAt.congr_of_eventuallyEq hsame).contDiffWithinAt

/-- The same smooth residual representative satisfies the next factor's
source hypothesis, uniformly in every unit direction tuple. Only already
proved ordered envelopes are used; their constants are made direction-uniform
by finite basis expansion. In particular no power of the carrier frequency is
introduced (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_supported_source_profile_of_ordered_envelopes
    {V : Set Par} (hV : IsOpen V) {S : Set E} (hS : IsCompact S)
    (b : I → E × Par → F) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hs : ∀ i q, q.1 ∉ S → b i q = 0)
    (u : I → Par → H)
    (hu : ∀ i c, c ∈ V → u i c =ᵐ[volume] fun x ↦ b i (x,c))
    (A K : I → ℝ)
    (hword : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v)
          ps (u q.1) q.2)
        (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) :
    ∃ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) ∧
      ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun x ↦ iteratedFDeriv ℝ l (fun q ↦ b i (x,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Csource l s * A i * K i ^ (s+l) := by
  classical
  choose g hgregular hgjets using fun i ↦
    exists_smooth_l2_family_of_supported_joint hS (b i) (hb i) (hs i)
  have hregular i : ContDiffOn ℝ ∞ (g i) V := (hgregular i).contDiffOn
  have hsame i {c : Par} (hc : c ∈ V) : u i =ᶠ[𝓝 c] g i := by
    filter_upwards [hV.mem_nhds hc] with a ha
    apply Lp.ext
    exact (hu i a ha).trans (by simpa using (hgjets i 0 (fun j ↦ j.elim0) a).symm)
  let D (l : ℕ) : I × V → ContinuousMultilinearMap ℝ (fun _ : Fin l ↦ Par) H :=
    fun q ↦ iteratedFDeriv ℝ l (g q.1) q.2
  have hD l (w : Fin l → Par) (hw : ∀ j, ‖w j‖ ≤ 1) :
      HasEnvelopeProfile vectorFourierSobolevScale (fun q ↦ D l q w)
        (fun q ↦ A q.1 * K q.1 ^ l) (fun q ↦ K q.1) := by
    have hwlist : ∀ v ∈ List.ofFn w, ‖v‖ ≤ 1 := by
      intro v hv
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      exact hw j
    have hp := hword (List.ofFn w) hwlist
    simp only [List.length_ofFn] at hp
    apply (hasEnvelopeProfile_congr (f := fun q : I × V ↦
      orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) (List.ofFn w) (u q.1) q.2) ?_).mp hp
    intro q
    rw [orderedParameterWord_congr_nhds (hsame q.1 q.2.property),
      orderedParameterWord_eq_iteratedFDeriv hV (hregular q.1) _ q.2.property]
    exact parameterListJet_ofFn (g q.1) l w q.2
  choose C hC hbound using fun l s ↦
    exists_uniform_parameter_jet_envelope_constant vectorFourierSobolevScale l (D l)
      (fun q ↦ A q.1 * K q.1 ^ l) (fun q ↦ K q.1) (hD l) s
  refine ⟨C,hC,?_⟩
  intro i c hc l w hw s f
  have hae : D l (i,⟨c,hc⟩) w =ᵐ[volume] f := hgjets i l w c
  let hm : MemLp f 2 volume := MemLp.ae_eq hae (Lp.memLp (D l (i,⟨c,hc⟩) w))
  have he : D l (i,⟨c,hc⟩) w = hm.toLp f := Lp.ext (hae.trans hm.coeFn_toLp.symm)
  obtain ⟨hmem,hest⟩ := hbound l s (i,⟨c,hc⟩) w hw
  rw [he] at hmem hest
  refine ⟨hm,hmem,?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hmem] at hest
  exact hest.trans_eq (by simp only [pow_add]; ring)


/-- Preserve the exact natural reserve in the next factor's source profile.
The low orders have weight one; no negative power is extracted from the
amplitude. The same compact-family lift identifies all parameter derivatives,
and the finite-basis argument changes only their uniform constant.
Consumer: reserved finite residual chains in `app:ch_response:cor:current-atoms`.
The reserved one-letter estimates remain the analytic producer of `hword`. -/
theorem exists_supported_reserved_source_profile_of_ordered_bounds
    {V : Set Par} (hV : IsOpen V) {S : Set E} (hS : IsCompact S)
    (b : I → E × Par → F) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hs : ∀ i q, q.1 ∉ S → b i q = 0)
    (u : I → Par → H)
    (hu : ∀ i c, c ∈ V → u i c =ᵐ[volume] fun x ↦ b i (x,c))
    (A K : I → ℝ) (reserve : ℕ)
    (hword : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (u q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C*A q.1*K q.1^(s+ps.length-reserve)) :
    ∃ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) ∧
      ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun x ↦ iteratedFDeriv ℝ l (fun q ↦ b i (x,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Csource l s*A i*K i^(s+l-reserve) := by
  classical
  choose g hgregular hgjets using fun i ↦
    exists_smooth_l2_family_of_supported_joint hS (b i) (hb i) (hs i)
  have hsame i {c : Par} (hc : c ∈ V) : u i =ᶠ[𝓝 c] g i := by
    filter_upwards [hV.mem_nhds hc] with a ha
    apply Lp.ext
    exact (hu i a ha).trans (by simpa using (hgjets i 0 (fun j ↦ j.elim0) a).symm)
  let D (l : ℕ) : I × V → ContinuousMultilinearMap ℝ (fun _ : Fin l ↦ Par) H :=
    fun q ↦ iteratedFDeriv ℝ l (g q.1) q.2
  have hD l s (w : Fin l → Par) (hw : ∀ j, ‖w j‖ ≤ 1) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        D l q w ∈ vectorFourierSobolevScale.level s ∧
        vectorFourierSobolevScale.gradeNorm s (D l q w) ≤ C*(A q.1*K q.1^(s+l-reserve)) := by
    have hwlist : ∀ v ∈ List.ofFn w, ‖v‖ ≤ 1 := by
      intro v hv
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
      exact hw j
    obtain ⟨C,hC,hbound⟩ := hword (List.ofFn w) hwlist s
    refine ⟨C,hC,?_⟩
    intro q
    have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v)
        (List.ofFn w) (u q.1) q.2 = D l q w := by
      rw [orderedParameterWord_congr_nhds (hsame q.1 q.2.property),
        orderedParameterWord_eq_iteratedFDeriv hV (hgregular q.1).contDiffOn _ q.2.property]
      exact parameterListJet_ofFn (g q.1) l w q.2
    obtain ⟨hm,hbnd⟩ := hbound q
    rw [he] at hm hbnd
    refine ⟨hm,?_⟩
    rw [vectorFourierSobolevScale_gradeNorm s hm]
    simpa only [List.length_ofFn,mul_assoc] using hbnd
  choose C hC hbound using fun l s ↦
    exists_uniform_parameter_jet_grade_constant vectorFourierSobolevScale l s (D l)
      (fun q ↦ A q.1*K q.1^(s+l-reserve)) (hD l s)
  refine ⟨C,hC,?_⟩
  intro i c hc l w hw s f
  have hae : D l (i,⟨c,hc⟩) w =ᵐ[volume] f := hgjets i l w c
  let hm : MemLp f 2 volume := MemLp.ae_eq hae (Lp.memLp (D l (i,⟨c,hc⟩) w))
  have he : D l (i,⟨c,hc⟩) w = hm.toLp f := Lp.ext (hae.trans hm.coeFn_toLp.symm)
  obtain ⟨hmem,hest⟩ := hbound l s (i,⟨c,hc⟩) w hw
  rw [he] at hmem hest
  refine ⟨hm,hmem,?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hmem] at hest
  simpa only [mul_assoc] using hest

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
