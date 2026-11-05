module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Leibniz.Splittings
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.OrderedSpatial

/-!
# Finite mixed Leibniz calculus for the original annular amplitude

The external list is split before source differentiation. Thus the original
envelope receives at most the external order of carrier derivatives, for
all source orders. Consumer: the original mixed profile in
`app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
open Complement.ParameterDerivatives Complement.ParameterDerivatives.MixedGrades
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem parameterListJet_cons (f : P → F) (v : P) (vs : List P) {c : P}
    (hf : ContDiffAt ℝ ∞ f c) :
    parameterListJet f (v :: vs) c =
      fderiv ℝ (parameterListJet f vs) c v := by
  have hd := hf.differentiableAt_iteratedFDeriv (m := vs.length) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl _)
  have ht : Fin.tail (v :: vs).get = vs.get := by
    funext i
    change (v :: vs).get i.succ = vs.get i
    exact List.get_cons_succ
  change iteratedFDeriv ℝ (vs.length + 1) f c (v :: vs).get =
    fderiv ℝ (fun b ↦ iteratedFDeriv ℝ vs.length f b vs.get) c v
  simpa only [ht, List.get_cons_zero] using
    hd.iteratedFDeriv_succ_apply_left' (m := (v :: vs).get)

private theorem differentiableAt_parameterListJet (f : P → F) (vs : List P) {c : P}
    (hf : ContDiffAt ℝ ∞ f c) : DifferentiableAt ℝ (parameterListJet f vs) c :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin vs.length ↦ P) F vs.get).differentiableAt.comp c
    (hf.differentiableAt_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl _))

private theorem differentiableAt_list_sum {ι : Type*} (l : List ι) (f : ι → P → F) {c : P}
    (hf : ∀ i ∈ l, DifferentiableAt ℝ (f i) c) :
    DifferentiableAt ℝ (fun b ↦ (l.map (fun i ↦ f i b)).sum) c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    exact (hf i (by simp)).add (ih (fun j hj ↦ hf j (by simp [hj])))

private theorem fderiv_list_sum {ι : Type*} (l : List ι) (f : ι → P → F) {c : P}
    (hf : ∀ i ∈ l, DifferentiableAt ℝ (f i) c) (v : P) :
    fderiv ℝ (fun b ↦ (l.map (fun i ↦ f i b)).sum) c v =
      (l.map (fun i ↦ fderiv ℝ (f i) c v)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hsum := differentiableAt_list_sum l f (fun j hj ↦ hf j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add (hf i (by simp)) hsum, add_apply,
      ih (fun j hj ↦ hf j (by simp [hj]))]

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Finite external Leibniz formula for the actual matrix action. The original
splitting lists retain multiplicities and share one total external order.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem parameterListJet_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    (f : P → F) (g : P → G) {U : Set P} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (vs : List P) {c : P} (hc : c ∈ U) :
    parameterListJet (fun q => B (f q) (g q)) vs c =
      ((parameterLeibnizSplittings vs).map (fun s =>
        B (parameterListJet f s.1 c) (parameterListJet g s.2 c))).sum := by
  induction vs generalizing c with
  | nil => simp [parameterListJet, parameterLeibnizSplittings]
  | cons v vs ih =>
    have hf' := hf.contDiffAt (hU.mem_nhds hc)
    have hg' := hg.contDiffAt (hU.mem_nhds hc)
    have hprod : ContDiffAt ℝ ∞ (fun q => B (f q) (g q)) c :=
      (B.contDiff.contDiffAt.comp c hf').clm_apply hg'
    rw [parameterListJet_cons _ _ _ hprod]
    have he : parameterListJet (fun q => B (f q) (g q)) vs =ᶠ[𝓝 c]
        fun q => ((parameterLeibnizSplittings vs).map (fun s =>
          B (parameterListJet f s.1 q) (parameterListJet g s.2 q))).sum :=
      Filter.mem_of_superset (hU.mem_nhds hc) fun q hq => ih hq
    rw [he.fderiv_eq, fderiv_list_sum _ _ (fun s _ =>
      (B.differentiableAt.comp c (differentiableAt_parameterListJet f s.1 hf')).clm_apply
        (differentiableAt_parameterListJet g s.2 hg'))]
    simp only [parameterLeibnizSplittings, List.map_append, List.sum_append,
      List.map_map, Function.comp_def]
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s _
    have hd := B.hasFDerivAt_of_bilinear
      (differentiableAt_parameterListJet f s.1 hf').hasFDerivAt
      (differentiableAt_parameterListJet g s.2 hg').hasFDerivAt
    rw [hd.fderiv, parameterListJet_cons _ _ _ hf', parameterListJet_cons _ _ _ hg']
    simp only [add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply]
    exact add_comm _ _

omit [NormedSpace ℝ P] in
/-- The splitting does not enlarge the unit direction tuples. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem parameterLeibnizSplittings_unit {vs : List P} {s : List P × List P}
    (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (hs : s ∈ parameterLeibnizSplittings vs) :
    (∀ v ∈ s.1, ‖v‖ ≤ 1) ∧ (∀ v ∈ s.2, ‖v‖ ≤ 1) := by
  induction vs generalizing s with
  | nil =>
    simp only [parameterLeibnizSplittings, List.mem_singleton] at hs
    subst s
    simp
  | cons v vs ih =>
    have ht {s : List P × List P} (hs : s ∈ parameterLeibnizSplittings vs) :=
      ih (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hs
    have hv0 := hv v (List.mem_cons_self ..)
    simp only [parameterLeibnizSplittings, List.mem_append, List.mem_map] at hs
    rcases hs with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact ⟨by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hv0 (ht hs).1,
        (ht hs).2⟩
    · exact ⟨(ht hs).1,
        by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hv0 (ht hs).2⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- A fixed external order has exactly `2^l` Leibniz terms, independent of
source differentiation order (`app:ch_response:lem:energy-carrier-jets`). -/
theorem length_parameterLeibnizSplittings (vs : List P) :
    (parameterLeibnizSplittings vs).length = 2 ^ vs.length := by
  induction vs with
  | nil => simp [parameterLeibnizSplittings]
  | cons v vs ih =>
    simp only [parameterLeibnizSplittings, List.length_append, List.length_map,
      List.length_cons, ih, pow_succ]
    omega

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Evaluated external list jets are smooth on the same open product chart.
No extension of the original function is introduced.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_parameterListJet_joint {V : Set P} {U : Set Z}
    (hV : IsOpen V) (hU : IsOpen U) {f : P × Z → F}
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ U)) (vs : List P) :
    ContDiffOn ℝ ∞ (fun p : P × Z =>
      parameterListJet (fun q => f (q, p.2)) vs p.1) (V ×ˢ U) := by
  induction vs with
  | nil => simpa [parameterListJet] using hf
  | cons v vs ih =>
    apply ((hV.prod hU).contDiffOn_iff.mpr ?_)
    intro p hp
    have he : (fun w : P × Z => parameterListJet (fun q => f (q, w.2)) (v :: vs) w.1)
        =ᶠ[𝓝 p] (fun w => fderiv ℝ
          (fun q => parameterListJet (fun b => f (b, w.2)) vs q) w.1 v) := by
      filter_upwards [(hV.prod hU).mem_nhds hp] with w hw
      apply parameterListJet_cons
      exact (hf.contDiffAt ((hV.prod hU).mem_nhds hw)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)
    exact ((Complement.ParameterDerivatives.MixedGrades.contDiffOn_parameterFDeriv hV hU ih v).contDiffAt
      ((hV.prod hU).mem_nhds hp)).congr_of_eventuallyEq he

/-- Mixed source/external jets of an original matrix consume exactly `k+l`
joint symbol derivatives. Unit external directions cost no extra factor.
The envelope will instead use its separate finite-carrier Sobolev estimate.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_jointJet_parameterListJet_le {V : Set P} {U : Set Z}
    (hV : IsOpen V) (hU : IsOpen U) {f : P × Z → F}
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ U)) (vs : List P)
    (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (k : ℕ) {p : P × Z} (hp : p ∈ V ×ˢ U) :
    ‖iteratedFDeriv ℝ k (fun w : P × Z =>
      parameterListJet (fun q => f (q, w.2)) vs w.1) p‖ ≤
        ‖iteratedFDeriv ℝ (k + vs.length) f p‖ := by
  induction vs generalizing k with
  | nil => simp [parameterListJet]
  | cons v vs ih =>
    have he : (fun w : P × Z => parameterListJet (fun q => f (q, w.2)) (v :: vs) w.1)
        =ᶠ[𝓝 p] (fun w => fderiv ℝ
          (fun q => parameterListJet (fun b => f (b, w.2)) vs q) w.1 v) := by
      filter_upwards [(hV.prod hU).mem_nhds hp] with w hw
      apply parameterListJet_cons
      exact (hf.contDiffAt ((hV.prod hU).mem_nhds hw)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    have hb := norm_iteratedFDeriv_parameterFDeriv_le (hV.prod hU)
      (contDiffOn_parameterListJet_joint hV hU hf vs) hp v k
    apply hb.trans
    have hb' := ih (fun w hw => hv w (List.mem_cons_of_mem _ hw)) (k + 1)
    have hv0 := hv v (List.mem_cons_self ..)
    have heorder : k + 1 + vs.length = k + (v :: vs).length := by
      simp only [List.length_cons]
      omega
    rw [heorder] at hb'
    simpa only [one_mul] using mul_le_mul hv0 hb' (norm_nonneg _) zero_le_one

/-- Restrict the previous original joint estimate to the source variable on
the same chart. Consumer: each finite matrix/envelope Leibniz term in
`app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_sourceJet_parameterListJet_le_joint {V : Set P} {U : Set Z}
    (hV : IsOpen V) (hU : IsOpen U) {f : P × Z → F}
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ U)) (vs : List P)
    (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (k : ℕ) {c : P} (hc : c ∈ V)
    {z : Z} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ k (fun y => parameterListJet (fun q => f (q, y)) vs c) z‖ ≤
      ‖iteratedFDeriv ℝ (k + vs.length) f (c, z)‖ := by
  let T : Z →L[ℝ] P × Z := (0 : Z →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Z)
  have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (fun y => by simp [T, Prod.norm_def])
  have h := norm_iteratedFDeriv_affine_contraction_le T hT (c, 0) (hV.prod hU)
    (contDiffOn_parameterListJet_joint hV hU hf vs) k (x := z)
      (by simpa [T] using And.intro hc hz)
  apply le_trans _ (norm_jointJet_parameterListJet_le hV hU hf vs hv k ⟨hc, hz⟩)
  simpa [T] using h

/-- Freezing the spectator output position sends external directions to
their original carrier components, exactly. This is used on the envelope
factor of the finite annular expansion, not as a derivative estimate.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem parameterListJet_comp_continuousLinearMap
    (L : G →L[ℝ] P) {U : Set P} (hU : IsOpen U) {f : P → F}
    (hf : ContDiffOn ℝ ∞ f U) (vs : List G) {c : G} (hc : L c ∈ U) :
    parameterListJet (f ∘ L) vs c = parameterListJet f (vs.map L) (L c) := by
  have hpre := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn
    hc (i := vs.length) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hc,
    iteratedFDerivWithin_of_isOpen _ hU hc] at he
  have hh := congrArg (fun T => T vs.get) he
  have hmap : vs.map L = List.ofFn (fun i : Fin vs.length => L (vs.get i)) := by
    rw [List.ofFn_comp', List.ofFn_get]
  rw [hmap, parameterListJet_ofFn]
  exact hh

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
