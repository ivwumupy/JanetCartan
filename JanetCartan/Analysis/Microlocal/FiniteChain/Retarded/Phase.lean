module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stationary relations of the retarded localized phase

The boundary and interior calculations in `app:ch_regular:lem:finite-chain`,
“Retarded and signed factors”. The normal variable is `d = t - s`; all six
remaining variables are tangential. These are actual partial derivatives of
the phase, not assumed canonical-relation equations. Frequencies are physical.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact localized phase of `app:ch_regular:lem:finite-chain`, in the
coordinates `t = s + d`. `xi` is the input base and `xo` the output base. -/
def phase (xi xo : ℝ × E) (d s : ℝ) (y : E) (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : ℝ :=
  (xo.1 - (s + d)) * κ + inner ℝ (xo.2 - y) ζ +
    (s - xi.1) * τ + inner ℝ (y - xi.2) η

/-- The common-time tangential derivative in `app:ch_regular:lem:finite-chain`. -/
theorem deriv_phase_time (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    deriv (fun r => phase xi xo d r y κ ζ τ η) s = τ - κ := by
  have he : (fun r => phase xi xo d r y κ ζ τ η) = fun r =>
      (xo.1-d)*κ + inner ℝ (xo.2-y) ζ - xi.1*τ + inner ℝ (y-xi.2) η +
        r * (τ-κ) := by funext r; dsimp [phase]; ring
  rw [he]
  simp

/-- The normal derivative in `app:ch_regular:lem:finite-chain`. It is used
only in the interior, never to differentiate the boundary jump. -/
theorem deriv_phase_normal (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    deriv (fun r => phase xi xo r s y κ ζ τ η) d = -κ := by
  have he : (fun r => phase xi xo r s y κ ζ τ η) = fun r =>
      (xo.1-s)*κ + inner ℝ (xo.2-y) ζ + (s-xi.1)*τ + inner ℝ (y-xi.2) η +
        r * (-κ) := by funext r; dsimp [phase]; ring
  rw [he]
  simp

/-- Output time-frequency derivative (`app:ch_regular:lem:finite-chain`). -/
theorem deriv_phase_kappa (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    deriv (fun r => phase xi xo d s y r ζ τ η) κ = xo.1 - (s+d) := by
  simp [phase]

/-- Input time-frequency derivative (`app:ch_regular:lem:finite-chain`). -/
theorem deriv_phase_tau (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    deriv (fun r => phase xi xo d s y κ ζ r η) τ = s - xi.1 := by
  simp [phase]

/-- The transverse base derivative is the frequency difference
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_phase_base (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    fderiv ℝ (fun z => phase xi xo d s z κ ζ τ η) y = innerSL ℝ (η-ζ) := by
  have he : (fun z => phase xi xo d s z κ ζ τ η) = fun z =>
      (xo.1-(s+d))*κ + inner ℝ xo.2 ζ + (s-xi.1)*τ - inner ℝ xi.2 η +
        innerSL ℝ (η-ζ) z := by
    funext z
    simp only [phase, innerSL_apply_apply, inner_sub_left]
    rw [real_inner_comm ζ z, real_inner_comm η z]
    ring
  rw [he]
  exact ((innerSL ℝ (η-ζ)).hasFDerivAt.const_add _).fderiv

/-- Output transverse-frequency derivative (`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_phase_zeta (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    fderiv ℝ (fun z => phase xi xo d s y κ z τ η) ζ = innerSL ℝ (xo.2-y) := by
  exact ((((innerSL ℝ (xo.2-y)).hasFDerivAt.const_add _).add_const _).add_const _).fderiv

/-- Input transverse-frequency derivative (`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_phase_eta (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    fderiv ℝ (fun z => phase xi xo d s y κ ζ τ z) η = innerSL ℝ (y-xi.2) := by
  exact ((innerSL ℝ (y-xi.2)).hasFDerivAt.const_add _).fderiv

/-- Vanishing of all tangential partial derivatives of the actual localized
phase, as used at the boundary in `app:ch_regular:lem:finite-chain`. -/
def TangentialStationary (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : Prop :=
  deriv (fun r => phase xi xo d r y κ ζ τ η) s = 0 ∧
  fderiv ℝ (fun z => phase xi xo d s z κ ζ τ η) y = 0 ∧
  deriv (fun r => phase xi xo d s y r ζ τ η) κ = 0 ∧
  fderiv ℝ (fun z => phase xi xo d s y κ z τ η) ζ = 0 ∧
  deriv (fun r => phase xi xo d s y κ ζ r η) τ = 0 ∧
  fderiv ℝ (fun z => phase xi xo d s y κ ζ τ z) η = 0

/-- Interior stationarity adds the normal derivative
(`app:ch_regular:lem:finite-chain`). -/
def InteriorStationary (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : Prop :=
  TangentialStationary xi xo d s y κ ζ τ η ∧
    deriv (fun r => phase xi xo r s y κ ζ τ η) d = 0

/-- The six exact tangential equations (`app:ch_regular:lem:finite-chain`). -/
theorem tangentialStationary_iff (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    TangentialStationary xi xo d s y κ ζ τ η ↔
      τ = κ ∧ η = ζ ∧ xo.1 = s+d ∧ xo.2 = y ∧ s = xi.1 ∧ y = xi.2 := by
  have hz (v : E) : innerSL ℝ v = 0 ↔ v = 0 := by
    rw [← norm_eq_zero, innerSL_apply_norm, norm_eq_zero]
  simp only [TangentialStationary, deriv_phase_time, fderiv_phase_base,
    deriv_phase_kappa, fderiv_phase_zeta, deriv_phase_tau, fderiv_phase_eta, hz,
    sub_eq_zero]

/-- The full diagonal, including the input-base equation, at `d = 0`
(`app:ch_regular:lem:finite-chain`). -/
theorem boundary_stationary_iff (xi xo : ℝ × E) (s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    TangentialStationary xi xo 0 s y κ ζ τ η ↔
      xo = xi ∧ κ = τ ∧ ζ = η ∧ s = xi.1 ∧ y = xi.2 := by
  rw [tangentialStationary_iff]
  simp only [add_zero, Prod.ext_iff]
  constructor
  · rintro ⟨hτ, hη, ht, hy, hs, hyi⟩
    exact ⟨⟨ht.trans hs, hy.trans hyi⟩, hτ.symm, hη.symm, hs, hyi⟩
  · rintro ⟨⟨ht, hy⟩, hκ, hζ, hs, hyi⟩
    exact ⟨hκ.symm, hζ.symm, ht.trans hs.symm, hy.trans hyi.symm, hs, hyi⟩

/-- The exact interior stationary equations
(`app:ch_regular:lem:finite-chain`). -/
theorem interior_stationary_iff (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    InteriorStationary xi xo d s y κ ζ τ η ↔
      κ = 0 ∧ τ = 0 ∧ ζ = η ∧ xo.1 = xi.1+d ∧ xo.2 = xi.2 ∧
        s = xi.1 ∧ y = xi.2 := by
  rw [InteriorStationary, tangentialStationary_iff, deriv_phase_normal, neg_eq_zero]
  constructor
  · rintro ⟨⟨hτ, hη, ht, hy, hs, hyi⟩, hκ⟩
    exact ⟨hκ, hτ.trans hκ, hη.symm, by simpa [hs] using ht,
      hy.trans hyi, hs, hyi⟩
  · rintro ⟨hκ, hτ, hζ, ht, hy, hs, hyi⟩
    exact ⟨⟨hτ.trans hκ.symm, hζ.symm, by simpa [hs] using ht,
      hy.trans hyi.symm, hs, hyi⟩, hκ⟩

/-- The oriented characteristic relation, with zero time covector
(`app:ch_regular:lem:finite-chain`). -/
def ForwardRelation (xi xo : ℝ × E) (τ : ℝ) (η : E) (κ : ℝ) (ζ : E) : Prop :=
  xi.1 ≤ xo.1 ∧ xo.2 = xi.2 ∧ τ = 0 ∧ κ = 0 ∧ ζ = η

/-- Projecting the interior critical set gives precisely the forward relation
(`app:ch_regular:lem:finite-chain`). Allowing `d = 0` includes its closure. -/
theorem exists_interior_stationary_iff (xi xo : ℝ × E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    (∃ d s y, 0 ≤ d ∧ InteriorStationary xi xo d s y κ ζ τ η) ↔
      ForwardRelation xi xo τ η κ ζ := by
  simp only [interior_stationary_iff]
  constructor
  · rintro ⟨d, s, y, hd, hκ, hτ, hζη, ht, hy, _, _⟩
    exact ⟨by linarith, hy, hτ, hκ, hζη⟩
  · rintro ⟨ht, hy, hτ, hκ, hζη⟩
    exact ⟨xo.1-xi.1, xi.1, xi.2, sub_nonneg.mpr ht,
      hκ, hτ, hζη, by ring, hy, rfl, rfl⟩

/-- Euclidean size of the joint physical covector
(`app:ch_regular:lem:finite-chain`). -/
def frequencySize (τ : ℝ) (η : E) : ℝ := Real.sqrt (τ^2 + ‖η‖^2)

omit [InnerProductSpace ℝ E] in
/-- At a characteristic covector the annular size is its transverse norm
(`app:ch_regular:lem:finite-chain`). -/
theorem frequencySize_zero (η : E) : frequencySize 0 η = ‖η‖ := by
  simp [frequencySize, Real.sqrt_sq (norm_nonneg η)]

omit [InnerProductSpace ℝ E] in
/-- The positive input annulus excludes the zero transverse covector on the
characteristic branch (`app:ch_regular:lem:finite-chain`). -/
theorem transverse_ne_zero_of_forward {xi xo : ℝ × E} {κ τ c : ℝ} {ζ η : E}
    (hc : 0 < c) (hann : c ≤ frequencySize τ η)
    (h : ForwardRelation xi xo τ η κ ζ) : η ≠ 0 := by
  rw [h.2.2.1, frequencySize_zero] at hann
  intro he
  simp only [he, norm_zero] at hann
  linarith

omit [InnerProductSpace ℝ E] in
/-- A time-elliptic chart has no characteristic branch
(`app:ch_regular:lem:finite-chain`), without dividing by the time covector. -/
theorem not_forward_of_time_elliptic {xi xo : ℝ × E} {κ τ c a : ℝ} {ζ η : E}
    (hc : 0 < c) (ha : 0 < a) (hann : a ≤ frequencySize τ η)
    (hell : c * frequencySize τ η ≤ |τ|) :
    ¬ ForwardRelation xi xo τ η κ ζ := by
  intro h
  have hp : 0 < c * frequencySize τ η := mul_pos hc (ha.trans_le hann)
  rw [h.2.2.1, abs_zero] at hell
  rw [h.2.2.1] at hp
  linarith

/-- The literal adjoint phase, with `d = s - t ≥ 0`, from
`app:ch_regular:lem:finite-chain`. This exchanges input and output; it is
separate from a signed conjugate partner. -/
def adjointPhase (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : ℝ :=
  (xo.1-t)*κ + inner ℝ (xo.2-y) ζ +
    (t+d-xi.1)*τ + inner ℝ (y-xi.2) η

/-- Exchanging input/output negates the lower phase
(`app:ch_regular:lem:finite-chain`); the resulting translation is reversed. -/
theorem adjointPhase_eq_neg_swap (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    adjointPhase xi xo d t y κ ζ τ η = -phase xo xi d t y τ η κ ζ := by
  simp only [adjointPhase, phase, inner_sub_left]
  ring


/-- All actual tangential derivatives of the literal adjoint phase
(`app:ch_regular:lem:finite-chain`). -/
def AdjointTangentialStationary (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : Prop :=
  deriv (fun r => adjointPhase xi xo d r y κ ζ τ η) t = 0 ∧
  fderiv ℝ (fun z => adjointPhase xi xo d t z κ ζ τ η) y = 0 ∧
  deriv (fun r => adjointPhase xi xo d t y r ζ τ η) κ = 0 ∧
  fderiv ℝ (fun z => adjointPhase xi xo d t y κ z τ η) ζ = 0 ∧
  deriv (fun r => adjointPhase xi xo d t y κ ζ r η) τ = 0 ∧
  fderiv ℝ (fun z => adjointPhase xi xo d t y κ ζ τ z) η = 0

/-- Interior stationarity for the literal adjoint
(`app:ch_regular:lem:finite-chain`). -/
def AdjointInteriorStationary (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : Prop :=
  AdjointTangentialStationary xi xo d t y κ ζ τ η ∧
    deriv (fun r => adjointPhase xi xo r t y κ ζ τ η) d = 0

/-- Adjoint tangential stationarity is the swapped forward calculation
(`app:ch_regular:lem:finite-chain`). -/
theorem adjoint_tangentialStationary_iff_swap (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    AdjointTangentialStationary xi xo d t y κ ζ τ η ↔
      TangentialStationary xo xi d t y τ η κ ζ := by
  simp only [AdjointTangentialStationary, TangentialStationary,
    adjointPhase_eq_neg_swap, deriv.fun_neg, fderiv_fun_neg, neg_eq_zero]
  tauto

/-- Adjoint interior stationarity is the swapped forward calculation
(`app:ch_regular:lem:finite-chain`). -/
theorem adjoint_interiorStationary_iff_swap (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    AdjointInteriorStationary xi xo d t y κ ζ τ η ↔
      InteriorStationary xo xi d t y τ η κ ζ := by
  simp only [AdjointInteriorStationary, InteriorStationary,
    adjoint_tangentialStationary_iff_swap, adjointPhase_eq_neg_swap,
    deriv.fun_neg, neg_eq_zero]

/-- The literal adjoint projects to backward translation
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_adjoint_interior_stationary_iff (xi xo : ℝ × E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    (∃ d t y, 0 ≤ d ∧ AdjointInteriorStationary xi xo d t y κ ζ τ η) ↔
      ForwardRelation xo xi κ ζ τ η := by
  simp only [adjoint_interiorStationary_iff_swap, exists_interior_stationary_iff]

/-- Covector reflection negates the phase without exchanging the bases.
This is the signed-conjugate operation in `app:ch_regular:lem:finite-chain`,
which is distinct from the literal-adjoint input/output exchange. -/
theorem phase_neg_covectors (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    phase xi xo d s y (-κ) (-ζ) (-τ) (-η) = -phase xi xo d s y κ ζ τ η := by
  simp only [phase, inner_neg_right]
  ring

end JanetCartan.FiniteChain.Retarded
