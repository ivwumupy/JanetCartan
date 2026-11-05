module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.Adjoint

/-!
# Parameter differentiation for the integrated annular envelope

`exists_annularEnvelopeIntegral_joint_envelope_of_primitive_jets` and
`exists_annularEnvelopeAdjointIntegral_joint_envelope_of_primitive_jets` prove
actual ordered parameter differentiation through the SAME elapsed-time
integrals, Bochner integrability of their derivatives, joint weighted Sobolev
bounds, and the original `Kinput^(s + ps.length)` profile in both orientations.

The time-differentiation leaf derives derivative measurability from the original
measurable orbits. Fixed-time smoothness is constructed using supported original
kernels, and local domination follows from the primitive joint estimates and
locally bounded original mixed datum jets. These producers are instantiated in
the endpoints, without assuming time regularity of a chosen critical map,
derivative/integral commutation, or an integrated estimate.

The interval costs exactly `Δ`; both physical masks, beta, frequency, literal
adjoint order, separate coefficient and input scales, frequency window and fixed
low reserve are retained. Constants precede scales and varying fields, and
integer `p` covers both orders zero and minus one. Original sector and compatible
response constructions supply the displayed primitive hypotheses. Near-plus-tail
assembly remains with the enclosing envelope task.

Sources: `app:ch_response:eq:direct-envelope-profile`,
`app:ch_response:lem:energy-carrier-jets`, and `new:eq:carrier-ibp`.
-/
