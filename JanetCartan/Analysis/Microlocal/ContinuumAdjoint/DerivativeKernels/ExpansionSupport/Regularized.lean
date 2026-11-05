module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport.Conic

/-!
# Common compact supports for all regularized expansion terms

The sets supplied to `LowBounds.Assembly` are constructed from a closed
primitive support buffer and the existing compact carrier cutoff. They are
independent of the generated amplitude (`app:ch_background:prop:bg-adjoint`).
Continuity of the fixed slice coordinates and their inverse is geometric
input, supplied by the parent's coordinate identification.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol TransportKernel
variable {n : ℕ}

/-- The regularized common chart support, retaining both primitive amplitude
buffers and the literal carrier cutoff (`app:ch_background:prop:bg-adjoint`). -/
def regularizedExpansionChartSupport (g : Chart n) (P : Set (AmplitudeVariables n))
    (k : ℕ) (x y : Euclidean n) : Set (Euclidean 2 × Euclidean n) :=
  {p | (let u := chartCarrierVariable g.coordinates p.1 p.2; (u.1, x, u.2) ∈ P) ∧
    (let u := chartCarrierVariable g.coordinates p.1 p.2; (u.1, y, u.2) ∈ P) ∧
    chartCarrierVariable g.coordinates p.1 p.2 ∈ tsupport (modifiedCarrierCutoff k)}

/-- Source support for all regularized terms, with the same primitive buffer
as the two-position chart support (`app:ch_background:prop:bg-adjoint`). -/
def regularizedExpansionSourceSupport (g : Chart n) (P : Set (AmplitudeVariables n))
    (k : ℕ) (x : Euclidean n) : Set (SourceChartVariables n) :=
  {q | q.2 ∈ regularizedExpansionChartSupport g P k x q.1}

private theorem continuous_chartCarrierVariable (g : Chart n) (he : Continuous g.coordinates) :
    Continuous (fun p : Euclidean 2 × Euclidean n ↦ chartCarrierVariable g.coordinates p.1 p.2) :=
  (((he.comp continuous_snd).fst.prodMk continuous_fst).prodMk
    (he.comp continuous_snd).snd)

private theorem chartCarrierVariable_mem_compact (g : Chart n)
    (he : Continuous g.coordinates.symm) (k : ℕ) :
    IsCompact {p : Euclidean 2 × Euclidean n |
      chartCarrierVariable g.coordinates p.1 p.2 ∈ tsupport (modifiedCarrierCutoff k)} := by
  have hc := (hasCompactSupport_modifiedCarrierCutoff (n := n) k).image
    (continuous_fst.snd.prodMk (he.comp (continuous_fst.fst.prodMk continuous_snd)))
  convert hc using 1
  ext p
  constructor
  · intro hp
    refine ⟨chartCarrierVariable g.coordinates p.1 p.2, hp, ?_⟩
    simp [chartCarrierVariable]
  · rintro ⟨u, hu, rfl⟩
    simpa [chartCarrierVariable] using hu

/-- Compactness of the common regularized chart support follows from the
existing cutoff and the closed primitive buffer
(`app:ch_background:prop:bg-adjoint`). -/
theorem isCompact_regularizedExpansionChartSupport (g : Chart n)
    (he : Continuous g.coordinates) (hei : Continuous g.coordinates.symm)
    {P : Set (AmplitudeVariables n)} (hP : IsClosed P) (k : ℕ) (x y : Euclidean n) :
    IsCompact (regularizedExpansionChartSupport g P k x y) := by
  have hc := continuous_chartCarrierVariable g he
  have hl := hP.preimage (hc.fst.prodMk ((continuous_const (y := x)).prodMk hc.snd))
  have hr := hP.preimage (hc.fst.prodMk ((continuous_const (y := y)).prodMk hc.snd))
  exact (chartCarrierVariable_mem_compact g hei k).of_isClosed_subset
    (hl.inter (hr.inter (isClosed_tsupport _ |>.preimage hc))) (fun _ hp ↦ hp.2.2)

/-- Compact source support follows from the original compact measurement
buffer and the common regularized carrier support, without any new assumption
on a generated amplitude (`app:ch_background:prop:bg-adjoint`). -/
theorem isCompact_regularizedExpansionSourceSupport (g : Chart n)
    (he : Continuous g.coordinates) (hei : Continuous g.coordinates.symm)
    {P : Set (AmplitudeVariables n)} (hP : IsClosed P)
    {X : Set (Euclidean n)} (hX : IsCompact X)
    (hPX : ∀ p ∈ P, p.2.1 ∈ X) (k : ℕ) (x : Euclidean n) :
    IsCompact (regularizedExpansionSourceSupport g P k x) := by
  have hc := (continuous_chartCarrierVariable g he).comp
    (continuous_snd : Continuous (Prod.snd : SourceChartVariables n → _))
  have hl := hP.preimage (hc.fst.prodMk ((continuous_const (y := x)).prodMk hc.snd))
  have hr := hP.preimage (hc.fst.prodMk (continuous_fst.prodMk hc.snd))
  apply (hX.prod (chartCarrierVariable_mem_compact g hei k)).of_isClosed_subset
    (hl.inter (hr.inter (isClosed_tsupport _ |>.preimage hc)))
  intro q hq
  exact ⟨hPX _ hq.2.1, hq.2.2⟩

/-- The source support compatibility required by `LowBounds.Assembly` is
literal membership in the same primitive sets
(`app:ch_background:prop:bg-adjoint`). -/
theorem regularizedExpansionChartSupport_source (g : Chart n)
    (P : Set (AmplitudeVariables n)) (k : ℕ) (x y : Euclidean n)
    (p : Euclidean 2 × Euclidean n)
    (hp : p ∈ regularizedExpansionChartSupport g P k x y) :
    (y, p) ∈ regularizedExpansionSourceSupport g P k x := hp

/-- Every regularized generated density vanishes off the same constructed
compact chart set. In particular this discharges `_hsupp` in
`exists_modifiedAdjoint_L2_bound` from the original amplitude alone
(`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedNormalDensity_expansion_zero_off (L V)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    {P : Set (AmplitudeVariables n)} (hP : IsClosed P)
    (ha : ∀ z x η, a z x η ≠ 0 → (z, x, η) ∈ P)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a)
    (g : Chart n) (k : ℕ) (x y : Euclidean n) (p : Euclidean 2 × Euclidean n)
    (hp : p ∉ regularizedExpansionChartSupport g P k x y) :
    modifiedNormalDensity t.amplitude (modifiedCarrierCutoff k) x y
      (chartCarrierVariable g.coordinates p.1 p.2) = 0 := by
  by_contra hn
  apply hp
  have hl : t.amplitude (chartCarrierVariable g.coordinates p.1 p.2).1 x
      (chartCarrierVariable g.coordinates p.1 p.2).2 ≠ 0 := by
    intro hz
    exact hn (by simp [modifiedNormalDensity, hz])
  have hr : t.amplitude (chartCarrierVariable g.coordinates p.1 p.2).1 y
      (chartCarrierVariable g.coordinates p.1 p.2).2 ≠ 0 := by
    intro hz
    exact hn (by simp [modifiedNormalDensity, hz])
  refine ⟨adjointDerivativeExpansion_mem_closed L V ds a hP ha t ht _ _ _ hl,
    adjointDerivativeExpansion_mem_closed L V ds a hP ha t ht _ _ _ hr, ?_⟩
  apply subset_tsupport _
  intro hz
  exact hn (by simp [modifiedNormalDensity, hz])

/-- The parent chart's domain inclusion for its closed primitive buffer
supplies `_hCD` uniformly for the common compact supports
(`app:ch_background:prop:bg-adjoint`). -/
theorem regularizedExpansionChartSupport_domain (g : Chart n)
    (P : Set (AmplitudeVariables n))
    (hdom : ∀ x y v w,
      ((chartCarrierVariable g.coordinates v w).1, x,
        (chartCarrierVariable g.coordinates v w).2) ∈ P →
      ((chartCarrierVariable g.coordinates v w).1, y,
        (chartCarrierVariable g.coordinates v w).2) ∈ P → w ∈ g.domain x y v)
    (k : ℕ) (x y : Euclidean n) (p : Euclidean 2 × Euclidean n)
    (hp : p ∈ regularizedExpansionChartSupport g P k x y) : p.2 ∈ g.domain x y p.1 :=
  hdom x y p.1 p.2 hp.1 hp.2.1

/-- All compact-set continuity inputs of `LowBounds.Assembly` follow from
one primitive chart regularity proof on the common support geometry. The
sets are the same for every expansion term
(`app:ch_background:prop:bg-adjoint`). -/
theorem regularizedExpansionSupport_continuity
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (hr : PrimitiveRegularity g a m) (P : Set (AmplitudeVariables n))
    (hdom : ∀ x y v w,
      ((chartCarrierVariable g.coordinates v w).1, x,
        (chartCarrierVariable g.coordinates v w).2) ∈ P →
      ((chartCarrierVariable g.coordinates v w).1, y,
        (chartCarrierVariable g.coordinates v w).2) ∈ P → w ∈ g.domain x y v)
    (hf : ContinuousOn g.push g.inputDomain) (k : ℕ) :
    (∀ x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2))
      (regularizedExpansionChartSupport g P k x y)) ∧
    (∀ x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ g.inverse x y p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) ''
        regularizedExpansionChartSupport g P k x y)) ∧
    (∀ x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ g.jacobian x y p.1 p.2)
      (regularizedExpansionChartSupport g P k x y)) ∧
    (∀ x, ContinuousOn
      (fun p : SourceChartVariables n ↦ g.forward x p.1 p.2.1 p.2.2)
      (regularizedExpansionSourceSupport g P k x)) := by
  have hmap (x y : Euclidean n) : MapsTo
      (fun p : Euclidean 2 × Euclidean n ↦ ((x, y, p.2), p.1))
      (regularizedExpansionChartSupport g P k x y) g.inputDomain :=
    fun p hp ↦ regularizedExpansionChartSupport_domain g P hdom k x y p hp
  have hc (x y : Euclidean n) : Continuous
      (fun p : Euclidean 2 × Euclidean n ↦ ((x, y, p.2), p.1)) :=
    (continuous_const.prodMk (continuous_const.prodMk continuous_snd)).prodMk continuous_fst
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    have h := hf.comp (hc x y).continuousOn (hmap x y)
    exact h.snd.prodMk h.fst.snd.snd
  · intro x y
    apply hr.inverse.continuousOn.comp (hc x y).continuousOn
    rintro p ⟨q, hq, rfl⟩
    exact ⟨q.2, hmap x y hq, rfl⟩
  · intro x y
    exact hr.jacobian.continuousOn.comp (hc x y).continuousOn (hmap x y)
  · intro x
    have h := hf.comp
      ((continuous_const.prodMk (continuous_fst.prodMk continuous_snd.snd)).prodMk
        continuous_snd.fst).continuousOn
      (show MapsTo (fun p : SourceChartVariables n ↦ ((x, p.1, p.2.2), p.2.1))
          (regularizedExpansionSourceSupport g P k x) g.inputDomain from
        fun p hp ↦ hmap x p.1 hp)
    exact h.fst.snd.snd

end JanetCartan.ContinuumAdjoint.DerivativeKernels
