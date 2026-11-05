module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Supported
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.HilbertPairing
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Tempered weak derivatives of the actual annular branch sums

The local compact expansion, together with the original compact output mask,
produces actual Schwartz representatives. Their classical derivatives are their
weak derivatives. This supplies the exact distribution identities consumed by
`annular_joint_sobolev_of_expansion`, with no assumed output regularity.
Source: `new:eq:carrier-ibp` and `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral CompactTransfer BranchAmplitudes
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The actual joint word of a locally smooth, spatially supported output,
as a Schwartz function on its unchanged parameter slice. The smoothness
input will be derived from the primitive compact kernel (`new:eq:carrier-ibp`). -/
def supportedOutputWordSchwartz
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (hs : ∀ q, q.1 ∉ X → g q = 0)
    (es : List (E × P)) {c : P} (hc : c ∈ C) : 𝓢(E, V) :=
  (show HasCompactSupport (fun x => (WithLp.toLp 2
    (originalDatumDerivative es g (x, c)) : V)) from
      hX.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_originalDatumDerivative_slice hX.isClosed hs es c)).toSchwartzMap
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm.contDiff.comp
      (contDiffOn_univ.mp ((contDiffOn_originalDatumDerivative (isOpen_univ.prod hC) hg es).comp
        (contDiffOn_id.prodMk contDiffOn_const) (fun _ _ => ⟨mem_univ _, hc⟩))))

/-- A spatial derivative of the supported representative is the next actual
joint word, including any earlier parameter derivatives (`new:eq:carrier-ibp`). -/
theorem lineDeriv_supportedOutputWordSchwartz
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (hs : ∀ q, q.1 ∉ X → g q = 0)
    (es : List (E × P)) {c : P} (hc : c ∈ C) (v : E) :
    lineDerivOp v (supportedOutputWordSchwartz g hC hg hX hs es hc) =
      supportedOutputWordSchwartz g hC hg hX hs ((v, 0) :: es) hc := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm
  have hd := ((contDiffOn_originalDatumDerivative (isOpen_univ.prod hC) hg es).contDiffAt
    ((isOpen_univ.prod hC).mem_nhds (show (x, c) ∈ univ ×ˢ C from ⟨mem_univ x, hc⟩))).differentiableAt (by simp)
  have hh := (L.hasFDerivAt.comp (x, c) hd.hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) c x))
  exact congrArg (fun D : E →L[ℝ] V => D v) hh.fderiv

/-- The compact representative's spatial derivative is its tempered weak
derivative. The realization hypotheses are only almost-everywhere equality
of representatives; the annular expansion supplies both in the next theorem.
Source: the weak-derivative characterization following `new:eq:carrier-ibp`. -/
theorem tempered_spatialDerivative_of_supported_representatives
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (hs : ∀ q, q.1 ∉ X → g q = 0)
    (es : List (E × P)) {c : P} (hc : c ∈ C) (v : E)
    (F D : H)
    (hF : F =ᵐ[volume] fun x => WithLp.toLp 2 (originalDatumDerivative es g (x, c)))
    (hD : D =ᵐ[volume] fun x => WithLp.toLp 2
      (originalDatumDerivative ((v, 0) :: es) g (x, c))) :
    lineDerivOp v (F : 𝓢'(E, V)) = (D : 𝓢'(E, V)) := by
  let f := supportedOutputWordSchwartz g hC hg hX hs es hc
  let d := supportedOutputWordSchwartz g hC hg hX hs ((v, 0) :: es) hc
  have hf : F = f.toLp 2 volume := Lp.ext (hF.trans (f.coeFn_toLp 2 volume).symm)
  have hd : D = d.toLp 2 volume := Lp.ext (hD.trans (d.coeFn_toLp 2 volume).symm)
  rw [hf, hd, MeasureTheory.Lp.toTemperedDistribution_toLp_eq,
    MeasureTheory.Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  rw [show lineDerivOp v f = d from lineDeriv_supportedOutputWordSchwartz g hC hg hX hs es hc v]

variable {ι : Type} [Fintype ι] [FiniteDimensional ℝ P]
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The actual annular branch sum has the exact tempered weak derivative.
Primitive local geometry and the original supported amplitude produce every
smooth representative; the only realization input identifies the SAME bounded
outputs with their literal normalized kernels. Forward and reversed physical
kernel identifications supply this input. This is the weak characterization
consumed by `annular_joint_sobolev_of_expansion` (`new:eq:carrier-ibp`). -/
theorem realizedBranchSum_tempered_spatialDerivative
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (p : ℤ) (es : List (E × P))
    {X : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U) {c : P} (hc : c ∈ C) (v : E)
    (T : JointTransferTerm n P Mat ι → H)
    (hT : ∀ t ∈ jointTransferTerms b es ++ jointTransferTerms b ((v, 0) :: es),
      T t =ᵐ[volume] fun x => WithLp.toLp 2
        (normalizedBranchIntegral b f w₀ α a t lam p (x, c)))
 :
    lineDerivOp v ((((jointTransferTerms b es).map T).sum : H) : 𝓢'(E, V)) =
      ((((jointTransferTerms b ((v, 0) :: es)).map T).sum : H) : 𝓢'(E, V)) := by
  let g := normalizedBranchIntegral b f w₀ α a initialJointTransferTerm lam p
  have hg : ContDiffOn ℝ ∞ g (univ ×ˢ C) :=
    contDiffOn_normalizedBranchIntegral_output_strip b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
      hinv lam p [] initialJointTransferTerm (by simp [jointTransferTerms, orderedTransferAction])
      hX.isClosed houtput hXU
  have hgs (q : E × P) (hq : q.1 ∉ X) : g q = 0 :=
    normalizedBranchIntegral_zero_of_notMem_output b f w₀ α a [] _
      (by simp [jointTransferTerms, orderedTransferAction]) houtput lam p hq
  have he (ds : List (E × P))
      (hds : ∀ (t : JointTransferTerm n P Mat ι), t ∈ jointTransferTerms b ds →
        t ∈ jointTransferTerms b es ++ jointTransferTerms b ((v, 0) :: es)) :
      ((jointTransferTerms b ds).map T).sum =ᵐ[volume]
        fun x => WithLp.toLp 2 (originalDatumDerivative ds g (x, c)) := by
    have hh := coe_list_sum_eq_joint (r := r) (W := (univ : Set E)) (jointTransferTerms b ds) T
      (fun t x => normalizedBranchIntegral b f w₀ α a t lam p (x, c))
      (fun t ht => by simpa only [Measure.restrict_univ] using hT t (hds t ht))
    simp only [Measure.restrict_univ] at hh
    filter_upwards [hh] with x hx
    rw [hx]
    exact congrArg (WithLp.toLp 2)
      (originalDatumDerivative_normalizedIntegral_expansion_of_output_support
        b hU hD hcD hK hKD hf hα ha hs hw₀ hcritical hvalue h₀ hinv lam p ds
          hX.isClosed houtput hXU hc x).symm
  exact tempered_spatialDerivative_of_supported_representatives g hC hg hX hgs es hc v _ _
    (he es (fun _ ht => List.mem_append_left _ ht))
    (he ((v, 0) :: es) (fun _ ht => List.mem_append_right _ ht))

/-- All ordered spatial weak derivatives after a joint word are exactly the
finite sums of the SAME realized branches. Only the finitely required orders
need kernel realizations. This is the precise identity consumed by
`annular_joint_sobolev_of_expansion`, once its parameter output is identified.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem realizedBranchSum_tempered_spatialWords
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (E × P) → CarrierVariables n → ℝ} {w₀ : E × P → CarrierVariables n}
    {U : Set (E × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (E × P) → CarrierVariables n → Mat} {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (lam : ℝ) (p : ℤ) (ps : List (E × P)) (is : List (Fin n))
    {X : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U) {c : P} (hc : c ∈ C)

    (T : JointTransferTerm n P Mat ι → H)
    (hT : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ t ∈ jointTransferTerms b ((js.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++ ps),
        T t =ᵐ[volume] fun x => WithLp.toLp 2
          (normalizedBranchIntegral b f w₀ α a t lam p (x, c))) :
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
      ((((jointTransferTerms b ps).map T).sum : H) : 𝓢'(E, V)) =
    ((((jointTransferTerms b ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++ ps)).map T).sum : H) :
      𝓢'(E, V)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is _) = _
    rw [ih (fun js hj => hT js (hj.trans (Nat.le_succ _)))]
    apply realizedBranchSum_tempered_spatialDerivative b hU hD hcD hK hKD hf hα ha hs hw₀
      hcritical hvalue h₀ hinv lam p _ hX houtput hC hXU hc _ T
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hT is (Nat.le_succ _) t ht
    · exact hT (i :: is) le_rfl t ht

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
