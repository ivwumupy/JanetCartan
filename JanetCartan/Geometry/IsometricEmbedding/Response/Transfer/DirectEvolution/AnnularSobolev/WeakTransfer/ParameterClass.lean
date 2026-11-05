module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Distribution
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.Basic

/-!
# Actual parameter derivatives in the original annular L² space

The original output mask and the proved local kernel smoothness give genuine
norm derivatives of the L² output. This uses the existing compact-family lift;
no operator-norm parameter regularity or derivative transfer is assumed.
Consumer: the joint weak expansion in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential CompactTransfer
open JanetCartan.ResponseTransfer.ParameterRealization.L2Family
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The compact output representative lifted to the SAME Euclidean-fiber L²
space. It stores no identity or regularity premise (`new:eq:carrier-ibp`). -/
def supportedJointWordClass (g : E × P → Fin r → ℂ) {X : Set E} (hX : IsCompact X)
    (es : List (E × P)) (c : P) : H :=
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  compactToL2Vector hX (compactFamily (K := X)
    (fun a x => WithLp.toLp 2 (originalDatumDerivative es g (x, a))) c)

private theorem contDiffOn_outputWord_flip
    {g : E × P → Fin r → ℂ} {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) (es : List (E × P)) :
    ContDiffOn ℝ ∞ (fun q : P × E => (WithLp.toLp 2
      (originalDatumDerivative es g (q.2, q.1)) : V)) (C ×ˢ univ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm.contDiff.comp_contDiffOn
    ((contDiffOn_originalDatumDerivative (isOpen_univ.prod hC) hg es).comp
      (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq => ⟨mem_univ _, hq.1⟩))

/-- The compact-family lift is the actual original joint word almost
everywhere. No output class is postulated (`new:eq:carrier-ibp`). -/
theorem supportedJointWordClass_ae
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (hs : ∀ q, q.1 ∉ X → g q = 0)
    (es : List (E × P)) {c : P} (hc : c ∈ C) :
    supportedJointWordClass g hX es c =ᵐ[volume] fun x =>
      WithLp.toLp 2 (originalDatumDerivative es g (x, c)) := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let f := compactFamily (K := X)
    (fun a x => (WithLp.toLp 2 (originalDatumDerivative es g (x, a)) : V)) c
  have he := (extendZeroVector_memLp hX f).coeFn_toLp
  filter_upwards [he] with x hx
  change (extendZeroVector_memLp hX f).toLp (extendZeroVector f) x = _
  rw [hx]
  by_cases hxX : x ∈ X
  · rw [extendZeroVector_mem f hxX]
    exact compactFamily_apply (contDiffOn_outputWord_flip hC hg es) hc ⟨x, hxX⟩
  · rw [extendZeroVector_notMem f hxX]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hxX
      (tsupport_originalDatumDerivative_slice hX.isClosed hs es c h))).symm

/-- Parameter differentiation is a genuine L² norm derivative, obtained by
lifting the proved compact kernel family. Only the carrier parameter varies;
the physical operator, elapsed time and frequency are fixed in `g`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem fderiv_supportedJointWordClass
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (es : List (E × P)) {c : P} (hc : c ∈ C) (v : P) :
    fderiv ℝ (supportedJointWordClass g hX es) c v =
      supportedJointWordClass g hX ((0, v) :: es) c := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let G := fun a x => (WithLp.toLp 2 (originalDatumDerivative es g (x, a)) : V)
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) (C ×ˢ univ) :=
    contDiffOn_outputWord_flip hC hg es
  have hd := ((compactToL2Vector hX).restrictScalars ℝ).hasFDerivAt.comp c
    (compactFamily_hasFDerivAt (K := X) hC hG hc)
  have he := congrArg (fun D : P →L[ℝ] H => D v) hd.fderiv
  change fderiv ℝ (supportedJointWordClass g hX es) c v = _ at he
  rw [he]
  change compactToL2Vector hX _ = compactToL2Vector hX _
  congr 1
  apply ContinuousMap.ext
  intro x
  change (compactFamily (K := X) (fun a x => fderiv ℝ (fun b => G b x) a) c x) v = _
  rw [compactFamily_apply
    (JanetCartan.ResponseTransfer.ParameterRealization.L2Family.contDiffOn_parameterFDeriv hC hG) hc]
  rw [compactFamily_apply (contDiffOn_outputWord_flip hC hg ((0, v) :: es)) hc]
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm
  have hj := ((contDiffOn_originalDatumDerivative (isOpen_univ.prod hC) hg es).contDiffAt
    ((isOpen_univ.prod hC).mem_nhds (show (x.val, c) ∈ univ ×ˢ C from ⟨mem_univ _, hc⟩))).differentiableAt (by simp)
  have hh := (L.hasFDerivAt.comp (x.val, c) hj.hasFDerivAt).comp c
    ((hasFDerivAt_const (𝕜 := ℝ) x.val c).prodMk (hasFDerivAt_id (𝕜 := ℝ) c))
  exact congrArg (fun D : P →L[ℝ] V => D v) hh.fderiv

/-- Any ordered parameter word differentiates the same L² output family,
and agrees with its actual joint classical word. This is the input to the
annular mixed spatial/parameter expansion (`new:eq:carrier-ibp`). -/
theorem orderedParameterDerivative_supportedJointWordClass
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (es : List (E × P)) (ps : List P) {c : P} (hc : c ∈ C) :
    orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
      (supportedJointWordClass g hX es) c =
        supportedJointWordClass g hX ((ps.map fun v => ((0 : E), v)) ++ es) c := by
  induction ps generalizing c with
  | nil => rfl
  | cons v ps ih =>
    have he : orderedTransferAction (fun v F a => fderiv ℝ F a v) ps
        (supportedJointWordClass g hX es) =ᶠ[𝓝 c]
        supportedJointWordClass g hX ((ps.map fun v => ((0 : E), v)) ++ es) := by
      filter_upwards [hC.mem_nhds hc] with a ha
      exact ih ha
    change fderiv ℝ _ c v = _
    rw [he.fderiv_eq]
    exact fderiv_supportedJointWordClass g hC hg hX _ hc v

/-- Literal kernel agreement identifies every ordered parameter derivative
of a realized L² family. Differentiability is proved by the compact-family
lift, not included in the realization premise. Consumer: the annular joint
expansion (`app:ch_response:lem:energy-carrier-jets`). -/
theorem orderedParameterDerivative_eq_supportedJointWordClass
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (hs : ∀ q, q.1 ∉ X → g q = 0)
    (F : P → H) (hF : ∀ c ∈ C, F c =ᵐ[volume] fun x => WithLp.toLp 2 (g (x, c)))
    (ps : List P) {c : P} (hc : c ∈ C) :
    orderedTransferAction (fun v F a => fderiv ℝ F a v) ps F c =
      supportedJointWordClass g hX (ps.map fun v => ((0 : E), v)) c := by
  induction ps generalizing c with
  | nil =>
    exact Lp.ext ((hF c hc).trans (supportedJointWordClass_ae g hC hg hX hs [] hc).symm)
  | cons v ps ih =>
    have he : orderedTransferAction (fun v F a => fderiv ℝ F a v) ps F =ᶠ[𝓝 c]
        supportedJointWordClass g hX (ps.map fun v => ((0 : E), v)) := by
      filter_upwards [hC.mem_nhds hc] with a ha
      exact ih ha
    change fderiv ℝ _ c v = _
    rw [he.fderiv_eq]
    exact fderiv_supportedJointWordClass g hC hg hX _ hc v

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
