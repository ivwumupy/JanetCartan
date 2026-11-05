module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Reference

/-!
# The smooth projected cube-stress frame

The construction `Q_i(G) = Π_(ker B_G) Q_i⁰` used in
`app:ch_waves:thm:leading` and `app:ch_background:defn:bg-geometry`.

`exists_cubeBending_smooth_stressFrame_neighborhood` supplies one positive
Gram gap and the specified smooth projected basis for every smooth immersion
whose normal projection and fixed-space second form lie in the stated strict
operator neighborhood of the actual analytic cube reference.
`exists_cubeBending_ball_smooth_stressFrame` also proves that the reference
itself lies in such a frame neighborhood on a ball about its center.

The normal-space identification is restricted orthogonal projection, proved
injective by the rank-stability API. Its kernel agrees with the actual stress
kernel. Independence is proved by perturbing the frozen cube stresses; rank–
nullity then gives a basis. No projected independence, Gram gap, or smooth
projector is assumed. The actual reference rank and kernel are discharged
using the explicit analytic circular bending, without existence placeholders.

The smoothness theorem also handles arbitrary differentiability orders and
joint parameters for fixed-space operator families. Quantitative high-jet
bounds, characteristic carriers, and the remaining conclusions of the leading
wave theorem are outside this frame-construction component.
-/
