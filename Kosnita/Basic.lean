import Mathlib

/-!
# Kosnita's theorem

Let `O` be the circumcentre of a triangle `ABC` and let `Oa`, `Ob`, `Oc` be the circumcentres of
the triangles `OBC`, `OCA`, `OAB`. Then the lines `A Oa`, `B Ob`, `C Oc` are concurrent.

We work in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`. Circumcentres are specified by
equidistance (in the plane, the unique point equidistant from three non-collinear points).
The proof reduces the statement to polynomial identities with explicit cofactors
(generated with sympy, see `scratch/gen.py`) closed by `linear_combination`.

Non-degeneracy hypotheses:
* `ABC`, `OBC`, `OCA`, `OAB` are genuine triangles (the last three fail exactly when the
  triangle `ABC` has a right angle; then e.g. `Oa` does not exist);
* `AB² + BC² + CA² ≠ 5 R²`: on that locus the lines can be pairwise parallel and distinct
  (the "Kosnita point" at infinity), so the affine claim can fail; other cases are degenerate.
-/

namespace Kosnita

open EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The 2D cross product of `(x1, x2)` and `(y1, y2)`. -/
def cross (x1 x2 y1 y2 : ℝ) : ℝ := x1 * y2 - x2 * y1

/-- Cross product of `p - a` and `q - b` (the lines `a p`, `b q` are parallel iff it vanishes). -/
def den (a1 a2 b1 b2 p1 p2 q1 q2 : ℝ) : ℝ := cross (p1 - a1) (p2 - a2) (q1 - b1) (q2 - b2)

/-- `AB² + BC² + CA² - 5 R²` with the circumcentre at the origin. -/
def sumSq (a1 a2 b1 b2 c1 c2 : ℝ) : ℝ :=
  (a1 - b1)^2 + (a2 - b2)^2 + ((b1 - c1)^2 + (b2 - c2)^2) + ((c1 - a1)^2 + (c2 - a2)^2)
    - 5 * (a1^2 + a2^2)

/-- `den` times the cross product of `r - c` with `X - c`, where `X` is the intersection of the
lines `a p` and `b q`. -/
def conc (a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 : ℝ) : ℝ :=
  cross (r1 - c1) (r2 - c2)
    (den a1 a2 b1 b2 p1 p2 q1 q2 * (a1 - c1) +
      cross (q1 - b1) (q2 - b2) (a1 - b1) (a2 - b2) * (p1 - a1))
    (den a1 a2 b1 b2 p1 p2 q1 q2 * (a2 - c2) +
      cross (q1 - b1) (q2 - b2) (a1 - b1) (a2 - b2) * (p2 - a2))

/-- Polynomial certificate for the denominator: up to the factors `Ka*Kb` it equals `S*T*R²`. -/
theorem cert_den (a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 : ℝ)
    (ha : a1^2 + a2^2 = b1^2 + b2^2) (hc : a1^2 + a2^2 = c1^2 + c2^2)
    (hp1 : 2 * (p1 * b1 + p2 * b2) = b1^2 + b2^2) (hp2 : 2 * (p1 * c1 + p2 * c2) = c1^2 + c2^2)
    (hq1 : 2 * (q1 * c1 + q2 * c2) = c1^2 + c2^2) (hq2 : 2 * (q1 * a1 + q2 * a2) = a1^2 + a2^2)
    (_hr1 : 2 * (r1 * a1 + r2 * a2) = a1^2 + a2^2) (_hr2 : 2 * (r1 * b1 + r2 * b2) = b1^2 + b2^2) :
    (2 * cross b1 b2 c1 c2) * (2 * cross c1 c2 a1 a2) * den a1 a2 b1 b2 p1 p2 q1 q2 =
      sumSq a1 a2 b1 b2 c1 c2 * cross (b1 - a1) (b2 - a2) (c1 - a1) (c2 - a2) * (a1^2 + a2^2) := by
  unfold den sumSq cross
  linear_combination (2*a1^3*a2 + 2*a1^3*b2 - 4*a1^3*c2 - 2*a1^2*a2*b1 + 4*a1^2*a2*c1 + 2*a1^2*b1*c2 - 2*a1^2*b2*c1 - 2*a1^2*c1*c2 + 2*a1*a2^3 + 2*a1*a2^2*b2 - 4*a1*a2^2*c2 - 4*a1*a2*c2^2 - 2*a1*b1*c1*c2 - 2*a1*b2*c2^2 + 3*a1*c1^2*c2 + 3*a1*c2^3 - 2*a2^3*b1 + 4*a2^3*c1 + 2*a2^2*b1*c2 - 2*a2^2*b2*c1 + 2*a2^2*c1*c2 + 2*a2*b1*c1^2 + 2*a2*b2*c1*c2 - 3*a2*c1^3 - 3*a2*c1*c2^2) * ha + (-2*a1^3*a2 + a1^3*b2 + a1^3*c2 - a1^2*a2*b1 - a1^2*a2*c1 + 2*a1^2*b1*b2 - a1^2*b1*c2 + a1^2*b2*c1 - 2*a1*a2^3 + a1*a2^2*b2 + a1*a2^2*c2 + 4*a1*a2*b2^2 - a1*b2*c1^2 - a1*b2*c2^2 - a2^3*b1 - a2^3*c1 - 2*a2^2*b1*b2 - a2^2*b1*c2 + a2^2*b2*c1 + a2*b1*c1^2 + a2*b1*c2^2) * hc + (-2*(a1*c2 - a2*c1)*(-b1*c1 - b2*c2 + c1*q1 + c2*q2)) * hp1 + (2*(a1*c2 - a2*c1)*(-b1^2 + b1*q1 - b2^2 + b2*q2)) * hp2 + (2*a1^2*b1*c2 - 2*a1^2*b2*c1 - a1*b1^2*c2 - a1*b2^2*c2 + a1*b2*c1^2 + a1*b2*c2^2 + 2*a2^2*b1*c2 - 2*a2^2*b2*c1 + a2*b1^2*c1 - a2*b1*c1^2 - a2*b1*c2^2 + a2*b2^2*c1) * hq1 + (-(b1*c2 - b2*c1)*(2*a1*c1 + 2*a2*c2 - c1^2 - c2^2)) * hq2

/-- Polynomial certificate for concurrency. -/
theorem cert_conc (a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 : ℝ)
    (ha : a1^2 + a2^2 = b1^2 + b2^2) (hc : a1^2 + a2^2 = c1^2 + c2^2)
    (hp1 : 2 * (p1 * b1 + p2 * b2) = b1^2 + b2^2) (hp2 : 2 * (p1 * c1 + p2 * c2) = c1^2 + c2^2)
    (hq1 : 2 * (q1 * c1 + q2 * c2) = c1^2 + c2^2) (hq2 : 2 * (q1 * a1 + q2 * a2) = a1^2 + a2^2)
    (hr1 : 2 * (r1 * a1 + r2 * a2) = a1^2 + a2^2) (hr2 : 2 * (r1 * b1 + r2 * b2) = b1^2 + b2^2) :
    (2 * cross b1 b2 c1 c2) * (2 * cross c1 c2 a1 a2) * (2 * cross a1 a2 b1 b2) *
      conc a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 = 0 := by
  unfold conc den cross
  linear_combination (-6*a1^6*c1*c2 + 3*a1^5*a2*c1^2 - 3*a1^5*a2*c2^2 + 6*a1^5*b1*c1*c2 - 3*a1^5*b2*c1^2 + 3*a1^5*b2*c2^2 - 12*a1^4*a2^2*c1*c2 - 3*a1^4*a2*b1*c1^2 + 3*a1^4*a2*b1*c2^2 + 2*a1^4*a2*b2*c1*c2 + 3*a1^4*a2*c1^3 + 3*a1^4*a2*c1*c2^2 - 6*a1^4*b1^2*c1*c2 + 3*a1^4*b1*b2*c1^2 - 3*a1^4*b1*b2*c2^2 + 3*a1^4*b2*c1^3 + 3*a1^4*b2*c1*c2^2 + 6*a1^4*c1^3*c2 + 6*a1^4*c1*c2^3 + 6*a1^3*a2^3*c1^2 - 6*a1^3*a2^3*c2^2 + 8*a1^3*a2^2*b1*c1*c2 - 8*a1^3*a2^2*b2*c1^2 + 8*a1^3*a2^2*b2*c2^2 + 2*a1^3*a2^2*c1^2*c2 + 2*a1^3*a2^2*c2^3 + 3*a1^3*a2*b1^2*c1^2 - 3*a1^3*a2*b1^2*c2^2 - 3*a1^3*a2*b1*c1^3 - 3*a1^3*a2*b1*c1*c2^2 + 3*a1^3*a2*b2^2*c1^2 - 3*a1^3*a2*b2^2*c2^2 - a1^3*a2*b2*c1^2*c2 - a1^3*a2*b2*c2^3 - 3*a1^3*a2*c1^4 + 3*a1^3*a2*c2^4 + 3*a1^3*b1^3*c1*c2 + a1^3*b1^2*b2*c2^2 + 3*a1^3*b1^2*c1^2*c2 + a1^3*b1^2*c2^3 + 3*a1^3*b1*b2^2*c1*c2 - 6*a1^3*b1*b2*c1^3 - 2*a1^3*b1*b2*c1*c2^2 - 6*a1^3*b1*c1^3*c2 - 6*a1^3*b1*c1*c2^3 + a1^3*b2^3*c2^2 - 3*a1^3*b2^2*c1^2*c2 - a1^3*b2^2*c2^3 + 3*a1^3*b2*c1^4 - 3*a1^3*b2*c2^4 - 6*a1^2*a2^4*c1*c2 - 4*a1^2*a2^3*b1*c1^2 + 4*a1^2*a2^3*b1*c2^2 + 4*a1^2*a2^3*c1^3 + 4*a1^2*a2^3*c1*c2^2 - 6*a1^2*a2^2*b1^2*c1*c2 + 6*a1^2*a2^2*b1*b2*c1^2 - 6*a1^2*a2^2*b1*b2*c2^2 - a1^2*a2^2*b1*c1^2*c2 - a1^2*a2^2*b1*c2^3 + 6*a1^2*a2^2*b2^2*c1*c2 + a1^2*a2^2*b2*c1^3 + a1^2*a2^2*b2*c1*c2^2 + 6*a1^2*a2^2*c1^3*c2 + 6*a1^2*a2^2*c1*c2^3 - 3*a1^2*a2*b1^3*c1^2 + 2*a1^2*a2*b1^3*c2^2 + a1^2*a2*b1^2*b2*c1*c2 + 3*a1^2*a2*b1^2*c1^3 + 5*a1^2*a2*b1^2*c1*c2^2 - 3*a1^2*a2*b1*b2^2*c1^2 + 2*a1^2*a2*b1*b2^2*c2^2 - 2*a1^2*a2*b1*b2*c1^2*c2 + 2*a1^2*a2*b1*b2*c2^3 + 3*a1^2*a2*b1*c1^4 - 3*a1^2*a2*b1*c2^4 + a1^2*a2*b2^3*c1*c2 - 3*a1^2*a2*b2^2*c1^3 - 5*a1^2*a2*b2^2*c1*c2^2 - 2*a1^2*a2*b2*c1^3*c2 - 2*a1^2*a2*b2*c1*c2^3 - 3*a1^2*a2*c1^5 - 6*a1^2*a2*c1^3*c2^2 - 3*a1^2*a2*c1*c2^4 - 3*a1^2*b1^3*c1^2*c2 - a1^2*b1^3*c2^3 - 2*a1^2*b1^2*b2*c1*c2^2 + 3*a1^2*b1^2*c1^3*c2 + 3*a1^2*b1^2*c1*c2^3 - 3*a1^2*b1*b2^2*c1^2*c2 - a1^2*b1*b2^2*c2^3 + 3*a1^2*b1*b2*c1^4 + 6*a1^2*b1*b2*c1^2*c2^2 + 3*a1^2*b1*b2*c2^4 - 2*a1^2*b2^3*c1*c2^2 + 3*a1^2*b2^2*c1^3*c2 + 3*a1^2*b2^2*c1*c2^3 - 3*a1^2*b2*c1^5 - 6*a1^2*b2*c1^3*c2^2 - 3*a1^2*b2*c1*c2^4 + 3*a1*a2^5*c1^2 - 3*a1*a2^5*c2^2 + 2*a1*a2^4*b1*c1*c2 - 5*a1*a2^4*b2*c1^2 + 5*a1*a2^4*b2*c2^2 + 2*a1*a2^4*c1^2*c2 + 2*a1*a2^4*c2^3 + 3*a1*a2^3*b1^2*c1^2 - 3*a1*a2^3*b1^2*c2^2 - 3*a1*a2^3*b1*c1^3 - 3*a1*a2^3*b1*c1*c2^2 + 3*a1*a2^3*b2^2*c1^2 - 3*a1*a2^3*b2^2*c2^2 - a1*a2^3*b2*c1^2*c2 - a1*a2^3*b2*c2^3 - 3*a1*a2^3*c1^4 + 3*a1*a2^3*c2^4 - a1*a2^2*b1^3*c1*c2 - 2*a1*a2^2*b1^2*b2*c1^2 + 3*a1*a2^2*b1^2*b2*c2^2 + 5*a1*a2^2*b1^2*c1^2*c2 + 3*a1*a2^2*b1^2*c2^3 - a1*a2^2*b1*b2^2*c1*c2 - 2*a1*a2^2*b1*b2*c1^3 + 2*a1*a2^2*b1*b2*c1*c2^2 - 2*a1*a2^2*b1*c1^3*c2 - 2*a1*a2^2*b1*c1*c2^3 - 2*a1*a2^2*b2^3*c1^2 + 3*a1*a2^2*b2^3*c2^2 - 5*a1*a2^2*b2^2*c1^2*c2 - 3*a1*a2^2*b2^2*c2^3 + 5*a1*a2^2*b2*c1^4 - 5*a1*a2^2*b2*c2^4 - 2*a1*a2^2*c1^4*c2 - 4*a1*a2^2*c1^2*c2^3 - 2*a1*a2^2*c2^5 + 3*a1*a2*b1^3*c1^3 - a1*a2*b1^3*c1*c2^2 + a1*a2*b1^2*b2*c1^2*c2 - 3*a1*a2*b1^2*b2*c2^3 - 6*a1*a2*b1^2*c1^4 - 6*a1*a2*b1^2*c1^2*c2^2 + 3*a1*a2*b1*b2^2*c1^3 - a1*a2*b1*b2^2*c1*c2^2 + 3*a1*a2*b1*c1^5 + 6*a1*a2*b1*c1^3*c2^2 + 3*a1*a2*b1*c1*c2^4 + a1*a2*b2^3*c1^2*c2 - 3*a1*a2*b2^3*c2^3 + 6*a1*a2*b2^2*c1^2*c2^2 + 6*a1*a2*b2^2*c2^4 + a1*a2*b2*c1^4*c2 + 2*a1*a2*b2*c1^2*c2^3 + a1*a2*b2*c2^5 - a2^5*b1*c1^2 + a2^5*b1*c2^2 - 2*a2^5*b2*c1*c2 + a2^5*c1^3 + a2^5*c1*c2^2 + 3*a2^4*b1*b2*c1^2 - 3*a2^4*b1*b2*c2^2 - a2^4*b1*c1^2*c2 - a2^4*b1*c2^3 + 6*a2^4*b2^2*c1*c2 - 2*a2^4*b2*c1^3 - 2*a2^4*b2*c1*c2^2 - a2^3*b1^3*c1^2 - 3*a2^3*b1^2*b2*c1*c2 + a2^3*b1^2*c1^3 + 3*a2^3*b1^2*c1*c2^2 - a2^3*b1*b2^2*c1^2 + 2*a2^3*b1*b2*c1^2*c2 + 6*a2^3*b1*b2*c2^3 + a2^3*b1*c1^4 - a2^3*b1*c2^4 - 3*a2^3*b2^3*c1*c2 - a2^3*b2^2*c1^3 - 3*a2^3*b2^2*c1*c2^2 + 2*a2^3*b2*c1^3*c2 + 2*a2^3*b2*c1*c2^3 - a2^3*c1^5 - 2*a2^3*c1^3*c2^2 - a2^3*c1*c2^4 + 2*a2^2*b1^3*c1^2*c2 + a2^2*b1^2*b2*c1^3 + 3*a2^2*b1^2*b2*c1*c2^2 - 3*a2^2*b1^2*c1^3*c2 - 3*a2^2*b1^2*c1*c2^3 + 2*a2^2*b1*b2^2*c1^2*c2 - 3*a2^2*b1*b2*c1^4 - 6*a2^2*b1*b2*c1^2*c2^2 - 3*a2^2*b1*b2*c2^4 + a2^2*b1*c1^4*c2 + 2*a2^2*b1*c1^2*c2^3 + a2^2*b1*c2^5 + a2^2*b2^3*c1^3 + 3*a2^2*b2^3*c1*c2^2 - 3*a2^2*b2^2*c1^3*c2 - 3*a2^2*b2^2*c1*c2^3 + 2*a2^2*b2*c1^5 + 4*a2^2*b2*c1^3*c2^2 + 2*a2^2*b2*c1*c2^4) * ha + (6*a1^6*c1*c2 - 3*a1^5*a2*c1^2 + 3*a1^5*a2*c2^2 - 6*a1^5*b1*c1*c2 + 3*a1^5*b2*c1^2 - 3*a1^5*b2*c2^2 + 12*a1^4*a2^2*c1*c2 + 3*a1^4*a2*b1*c1^2 - 3*a1^4*a2*b1*c2^2 - 2*a1^4*a2*b2*c1*c2 - 3*a1^4*a2*c1^3 - 3*a1^4*a2*c1*c2^2 - 3*a1^4*b1*b2*c1^2 + 3*a1^4*b1*b2*c2^2 - 6*a1^4*b2^2*c1*c2 - 3*a1^4*b2*c1^3 - 3*a1^4*b2*c1*c2^2 - 6*a1^3*a2^3*c1^2 + 6*a1^3*a2^3*c2^2 - 8*a1^3*a2^2*b1*c1*c2 + 8*a1^3*a2^2*b2*c1^2 - 8*a1^3*a2^2*b2*c2^2 - 2*a1^3*a2^2*c1^2*c2 - 2*a1^3*a2^2*c2^3 + 3*a1^3*a2*b1*c1^3 + 3*a1^3*a2*b1*c1*c2^2 + a1^3*a2*b2*c1^2*c2 + a1^3*a2*b2*c2^3 + 4*a1^3*b1*b2^2*c1*c2 + 3*a1^3*b1*b2*c1^3 + 3*a1^3*b1*b2*c1*c2^2 - 2*a1^3*b2^3*c1^2 + 2*a1^3*b2^3*c2^2 + a1^3*b2^2*c1^2*c2 + a1^3*b2^2*c2^3 + 6*a1^2*a2^4*c1*c2 + 4*a1^2*a2^3*b1*c1^2 - 4*a1^2*a2^3*b1*c2^2 - 4*a1^2*a2^3*c1^3 - 4*a1^2*a2^3*c1*c2^2 - 6*a1^2*a2^2*b1*b2*c1^2 + 6*a1^2*a2^2*b1*b2*c2^2 + a1^2*a2^2*b1*c1^2*c2 + a1^2*a2^2*b1*c2^3 - 12*a1^2*a2^2*b2^2*c1*c2 - a1^2*a2^2*b2*c1^3 - a1^2*a2^2*b2*c1*c2^2 + 2*a1^2*a2*b1*b2^2*c1^2 - 2*a1^2*a2*b1*b2^2*c2^2 + a1^2*a2*b1*b2*c1^2*c2 + a1^2*a2*b1*b2*c2^3 + 4*a1^2*a2*b2^3*c1*c2 + 5*a1^2*a2*b2^2*c1^3 + 5*a1^2*a2*b2^2*c1*c2^2 - 2*a1^2*b1*b2^2*c1^2*c2 - 2*a1^2*b1*b2^2*c2^3 + 2*a1^2*b2^3*c1^3 + 2*a1^2*b2^3*c1*c2^2 - 3*a1*a2^5*c1^2 + 3*a1*a2^5*c2^2 - 2*a1*a2^4*b1*c1*c2 + 5*a1*a2^4*b2*c1^2 - 5*a1*a2^4*b2*c2^2 - 2*a1*a2^4*c1^2*c2 - 2*a1*a2^4*c2^3 + 3*a1*a2^3*b1*c1^3 + 3*a1*a2^3*b1*c1*c2^2 + a1*a2^3*b2*c1^2*c2 + a1*a2^3*b2*c2^3 + 4*a1*a2^2*b1*b2^2*c1*c2 - a1*a2^2*b1*b2*c1^3 - a1*a2^2*b1*b2*c1*c2^2 - 2*a1*a2^2*b2^3*c1^2 + 2*a1*a2^2*b2^3*c2^2 + 5*a1*a2^2*b2^2*c1^2*c2 + 5*a1*a2^2*b2^2*c2^3 - 4*a1*a2*b1*b2^2*c1^3 - 4*a1*a2*b1*b2^2*c1*c2^2 - 4*a1*a2*b2^3*c1^2*c2 - 4*a1*a2*b2^3*c2^3 + a2^5*b1*c1^2 - a2^5*b1*c2^2 + 2*a2^5*b2*c1*c2 - a2^5*c1^3 - a2^5*c1*c2^2 - 3*a2^4*b1*b2*c1^2 + 3*a2^4*b1*b2*c2^2 + a2^4*b1*c1^2*c2 + a2^4*b1*c2^3 - 6*a2^4*b2^2*c1*c2 + 2*a2^4*b2*c1^3 + 2*a2^4*b2*c1*c2^2 + 2*a2^3*b1*b2^2*c1^2 - 2*a2^3*b1*b2^2*c2^2 - 3*a2^3*b1*b2*c1^2*c2 - 3*a2^3*b1*b2*c2^3 + 4*a2^3*b2^3*c1*c2 + a2^3*b2^2*c1^3 + a2^3*b2^2*c1*c2^2 + 2*a2^2*b1*b2^2*c1^2*c2 + 2*a2^2*b1*b2^2*c2^3 - 2*a2^2*b2^3*c1^3 - 2*a2^2*b2^3*c1*c2^2) * hc + (-4*(a1*b2 - a2*b1)*(a1*c2 - a2*c1)*(-a1*b1*c1*c2 + a1*b1*c1*r2 + a1*b2*c1^2 - a1*b2*c1*r1 - a1*c1^2*q2 + a1*c1*c2*q1 - a1*c1*q1*r2 + a1*c1*q2*r1 - a2*b1*c2^2 + a2*b1*c2*r2 + a2*b2*c1*c2 - a2*b2*c2*r1 - a2*c1*c2*q2 + a2*c2^2*q1 - a2*c2*q1*r2 + a2*c2*q2*r1 + b1*c1^2*q2 - b1*c1^2*r2 + b1*c1*c2*r1 - b1*c1*q2*r1 + b1*c2^2*q2 - b1*c2*q2*r2 - b2*c1^2*q1 - b2*c1*c2*r2 + b2*c1*q1*r1 - b2*c2^2*q1 + b2*c2^2*r1 + b2*c2*q1*r2 + c1^2*q1*r2 - c1*c2*q1*r1 + c1*c2*q2*r2 - c2^2*q2*r1)) * hp1 + (4*(a1*b2 - a2*b1)*(a1*c2 - a2*c1)*(-a1*b1^2*c2 + a1*b1^2*r2 + a1*b1*b2*c1 - a1*b1*b2*r1 - a1*b1*c1*q2 + a1*b1*c2*q1 - a1*b1*q1*r2 + a1*b1*q2*r1 - a2*b1*b2*c2 + a2*b1*b2*r2 + a2*b2^2*c1 - a2*b2^2*r1 - a2*b2*c1*q2 + a2*b2*c2*q1 - a2*b2*q1*r2 + a2*b2*q2*r1 + b1^2*c1*q2 - b1^2*c1*r2 + b1^2*c2*r1 - b1^2*q2*r1 - b1*b2*c1*q1 + b1*b2*c2*q2 + b1*b2*q1*r1 - b1*b2*q2*r2 + b1*c1*q1*r2 - b1*c2*q1*r1 - b2^2*c1*r2 - b2^2*c2*q1 + b2^2*c2*r1 + b2^2*q1*r2 + b2*c1*q2*r2 - b2*c2*q2*r1)) * hp2 + (-2*(a1*b2 - a2*b1)*(-a1^2*b1^2*c1^2 + a1^2*b1^2*c1*r1 - 2*a1^2*b1^2*c2^2 + 2*a1^2*b1^2*c2*r2 + 2*a1^2*b1*b2*c1*c2 - 2*a1^2*b1*b2*c1*r2 + a1^2*b1*c1^3 - a1^2*b1*c1^2*r1 + a1^2*b1*c1*c2^2 - 2*a1^2*b1*c1*c2*r2 + a1^2*b1*c2^2*r1 - a1^2*b2^2*c1^2 + a1^2*b2^2*c1*r1 + 2*a1^2*b2*c1^2*r2 - 2*a1^2*b2*c1*c2*r1 + a1*a2*b1^2*c1*r2 - a1*a2*b1^2*c2*r1 - 2*a1*a2*b1*b2*c1^2 + 2*a1*a2*b1*b2*c1*r1 - 2*a1*a2*b1*b2*c2^2 + 2*a1*a2*b1*b2*c2*r2 + a1*a2*b1*c1^2*c2 - a1*a2*b1*c1^2*r2 + a1*a2*b1*c2^3 - a1*a2*b1*c2^2*r2 - a1*a2*b2^2*c1*r2 + a1*a2*b2^2*c2*r1 + a1*a2*b2*c1^3 - a1*a2*b2*c1^2*r1 + a1*a2*b2*c1*c2^2 - a1*a2*b2*c2^2*r1 + a1*b1^3*c1^2 - a1*b1^3*c1*r1 + a1*b1^3*c2^2 - a1*b1^3*c2*r2 - a1*b1^2*c1^3 + a1*b1^2*c1^2*r1 - a1*b1^2*c1*c2^2 + a1*b1^2*c1*c2*r2 + a1*b1*b2^2*c1^2 - a1*b1*b2^2*c1*r1 + a1*b1*b2^2*c2^2 - a1*b1*b2^2*c2*r2 - a1*b1*b2*c1^2*c2 + a1*b1*b2*c1^2*r2 - a1*b1*b2*c2^3 + a1*b1*b2*c2^2*r2 + a1*b2^2*c1*c2*r2 - a1*b2^2*c2^2*r1 - a1*b2*c1^3*r2 + a1*b2*c1^2*c2*r1 - a1*b2*c1*c2^2*r2 + a1*b2*c2^3*r1 - a2^2*b1^2*c2^2 + a2^2*b1^2*c2*r2 + 2*a2^2*b1*b2*c1*c2 - 2*a2^2*b1*b2*c2*r1 - 2*a2^2*b1*c1*c2*r2 + 2*a2^2*b1*c2^2*r1 - 2*a2^2*b2^2*c1^2 + 2*a2^2*b2^2*c1*r1 - a2^2*b2^2*c2^2 + a2^2*b2^2*c2*r2 + a2^2*b2*c1^2*c2 + a2^2*b2*c1^2*r2 - 2*a2^2*b2*c1*c2*r1 + a2^2*b2*c2^3 - a2^2*b2*c2^2*r2 + a2*b1^2*b2*c1^2 - a2*b1^2*b2*c1*r1 + a2*b1^2*b2*c2^2 - a2*b1^2*b2*c2*r2 - a2*b1^2*c1^2*r2 + a2*b1^2*c1*c2*r1 - a2*b1*b2*c1^3 + a2*b1*b2*c1^2*r1 - a2*b1*b2*c1*c2^2 + a2*b1*b2*c2^2*r1 + a2*b1*c1^3*r2 - a2*b1*c1^2*c2*r1 + a2*b1*c1*c2^2*r2 - a2*b1*c2^3*r1 + a2*b2^3*c1^2 - a2*b2^3*c1*r1 + a2*b2^3*c2^2 - a2*b2^3*c2*r2 - a2*b2^2*c1^2*c2 + a2*b2^2*c1*c2*r1 - a2*b2^2*c2^3 + a2*b2^2*c2^2*r2)) * hq1 + (2*(a1*b2 - a2*b1)*(-a1*b1^2*c1^3 + a1*b1^2*c1^2*r1 - 3*a1*b1^2*c1*c2^2 + 3*a1*b1^2*c1*c2*r2 + 2*a1*b1*b2*c1^2*c2 - 2*a1*b1*b2*c1^2*r2 - 2*a1*b1*b2*c2^3 + 2*a1*b1*b2*c2^2*r2 + a1*b1*c1^4 - a1*b1*c1^3*r1 + 2*a1*b1*c1^2*c2^2 - 3*a1*b1*c1^2*c2*r2 + a1*b1*c1*c2^2*r1 + a1*b1*c2^4 - a1*b1*c2^3*r2 - a1*b2^2*c1^3 + a1*b2^2*c1^2*r1 + a1*b2^2*c1*c2^2 - a1*b2^2*c1*c2*r2 + 2*a1*b2*c1^3*r2 - 2*a1*b2*c1^2*c2*r1 + a2*b1^2*c1^2*c2 - a2*b1^2*c1*c2*r1 - a2*b1^2*c2^3 + a2*b1^2*c2^2*r2 - 2*a2*b1*b2*c1^3 + 2*a2*b1*b2*c1^2*r1 + 2*a2*b1*b2*c1*c2^2 - 2*a2*b1*b2*c2^2*r1 - 2*a2*b1*c1*c2^2*r2 + 2*a2*b1*c2^3*r1 - 3*a2*b2^2*c1^2*c2 + 3*a2*b2^2*c1*c2*r1 - a2*b2^2*c2^3 + a2*b2^2*c2^2*r2 + a2*b2*c1^4 - a2*b2*c1^3*r1 + 2*a2*b2*c1^2*c2^2 + a2*b2*c1^2*c2*r2 - 3*a2*b2*c1*c2^2*r1 + a2*b2*c2^4 - a2*b2*c2^3*r2 + b1^3*c1^3 - b1^3*c1^2*r1 + b1^3*c1*c2^2 - b1^3*c1*c2*r2 + b1^2*b2*c1^2*c2 - b1^2*b2*c1*c2*r1 + b1^2*b2*c2^3 - b1^2*b2*c2^2*r2 - b1^2*c1^4 + b1^2*c1^3*r1 - b1^2*c1^2*c2^2 + b1^2*c1*c2^2*r1 + b1*b2^2*c1^3 - b1*b2^2*c1^2*r1 + b1*b2^2*c1*c2^2 - b1*b2^2*c1*c2*r2 - 2*b1*b2*c1^3*c2 + b1*b2*c1^3*r2 + b1*b2*c1^2*c2*r1 - 2*b1*b2*c1*c2^3 + b1*b2*c1*c2^2*r2 + b1*b2*c2^3*r1 + b1*c1^3*c2*r2 - b1*c1^2*c2^2*r1 + b1*c1*c2^3*r2 - b1*c2^4*r1 + b2^3*c1^2*c2 - b2^3*c1*c2*r1 + b2^3*c2^3 - b2^3*c2^2*r2 - b2^2*c1^2*c2^2 + b2^2*c1^2*c2*r2 - b2^2*c2^4 + b2^2*c2^3*r2 - b2*c1^4*r2 + b2*c1^3*c2*r1 - b2*c1^2*c2^2*r2 + b2*c1*c2^3*r1)) * hq2 + (-3*a1^3*b1^3*c1*c2 + 3*a1^3*b1^2*b2*c1^2 - 2*a1^3*b1^2*b2*c2^2 + 3*a1^3*b1^2*c1^2*c2 + a1^3*b1^2*c2^3 + a1^3*b1*b2^2*c1*c2 - 3*a1^3*b1*b2*c1^3 + a1^3*b1*b2*c1*c2^2 + a1^3*b2^3*c1^2 - 2*a1^3*b2^2*c1^2*c2 - a1^2*a2*b1^3*c2^2 - a1^2*a2*b1^2*b2*c1*c2 + 2*a1^2*a2*b1^2*c1*c2^2 + 2*a1^2*a2*b1*b2^2*c1^2 - 3*a1^2*a2*b1*b2^2*c2^2 - a1^2*a2*b1*b2*c1^2*c2 + 3*a1^2*a2*b1*b2*c2^3 + 3*a1^2*a2*b2^3*c1*c2 - a1^2*a2*b2^2*c1^3 - 3*a1^2*a2*b2^2*c1*c2^2 + 3*a1^2*b1^4*c1*c2 - a1^2*b1^3*b2*c1^2 + a1^2*b1^3*b2*c2^2 + 4*a1^2*b1^2*b2^2*c1*c2 - 3*a1^2*b1^2*b2*c1^3 + a1^2*b1^2*b2*c1*c2^2 - 3*a1^2*b1^2*c1^3*c2 - 3*a1^2*b1^2*c1*c2^3 - a1^2*b1*b2^3*c1^2 + a1^2*b1*b2^3*c2^2 - 6*a1^2*b1*b2^2*c1^2*c2 + 2*a1^2*b1*b2^2*c2^3 + 4*a1^2*b1*b2*c1^4 + 2*a1^2*b1*b2*c1^2*c2^2 - 2*a1^2*b1*b2*c2^4 + a1^2*b2^4*c1*c2 - a1^2*b2^3*c1^3 - 5*a1^2*b2^3*c1*c2^2 + 3*a1^2*b2^2*c1^3*c2 + 3*a1^2*b2^2*c1*c2^3 - 3*a1*a2^2*b1^3*c1*c2 + 3*a1*a2^2*b1^2*b2*c1^2 - 2*a1*a2^2*b1^2*b2*c2^2 + 3*a1*a2^2*b1^2*c1^2*c2 + a1*a2^2*b1^2*c2^3 + a1*a2^2*b1*b2^2*c1*c2 - 3*a1*a2^2*b1*b2*c1^3 + a1*a2^2*b1*b2*c1*c2^2 + a1*a2^2*b2^3*c1^2 - 2*a1*a2^2*b2^2*c1^2*c2 - 2*a1*a2*b1^4*c1^2 + 2*a1*a2*b1^4*c2^2 + 3*a1*a2*b1^3*c1^3 - a1*a2*b1^3*c1*c2^2 - 4*a1*a2*b1^2*b2^2*c1^2 + 4*a1*a2*b1^2*b2^2*c2^2 + a1*a2*b1^2*b2*c1^2*c2 - 3*a1*a2*b1^2*b2*c2^3 - a1*a2*b1^2*c1^4 - 2*a1*a2*b1^2*c1^2*c2^2 - a1*a2*b1^2*c2^4 + 3*a1*a2*b1*b2^2*c1^3 - a1*a2*b1*b2^2*c1*c2^2 - 2*a1*a2*b2^4*c1^2 + 2*a1*a2*b2^4*c2^2 + a1*a2*b2^3*c1^2*c2 - 3*a1*a2*b2^3*c2^3 + a1*a2*b2^2*c1^4 + 2*a1*a2*b2^2*c1^2*c2^2 + a1*a2*b2^2*c2^4 - 3*a1*b1^4*c1^2*c2 - a1*b1^4*c2^3 + a1*b1^3*b2*c1^3 - 3*a1*b1^3*b2*c1*c2^2 + 3*a1*b1^3*c1^3*c2 + 3*a1*b1^3*c1*c2^3 - 3*a1*b1^2*b2^2*c1^2*c2 - 3*a1*b1^2*b2^2*c2^3 + 3*a1*b1^2*b2*c1^2*c2^2 + 3*a1*b1^2*b2*c2^4 + a1*b1*b2^3*c1^3 - 3*a1*b1*b2^3*c1*c2^2 + 3*a1*b1*b2^2*c1^3*c2 + 3*a1*b1*b2^2*c1*c2^3 - a1*b1*b2*c1^5 - 2*a1*b1*b2*c1^3*c2^2 - a1*b1*b2*c1*c2^4 - 2*a1*b2^4*c2^3 + 3*a1*b2^3*c1^2*c2^2 + 3*a1*b2^3*c2^4 - a1*b2^2*c1^4*c2 - 2*a1*b2^2*c1^2*c2^3 - a1*b2^2*c2^5 - a2^3*b1^3*c2^2 - a2^3*b1^2*b2*c1*c2 + 2*a2^3*b1^2*c1*c2^2 + 2*a2^3*b1*b2^2*c1^2 - 3*a2^3*b1*b2^2*c2^2 - a2^3*b1*b2*c1^2*c2 + 3*a2^3*b1*b2*c2^3 + 3*a2^3*b2^3*c1*c2 - a2^3*b2^2*c1^3 - 3*a2^3*b2^2*c1*c2^2 - a2^2*b1^4*c1*c2 - a2^2*b1^3*b2*c1^2 + a2^2*b1^3*b2*c2^2 + 5*a2^2*b1^3*c1^2*c2 + a2^2*b1^3*c2^3 - 4*a2^2*b1^2*b2^2*c1*c2 - 2*a2^2*b1^2*b2*c1^3 + 6*a2^2*b1^2*b2*c1*c2^2 - 3*a2^2*b1^2*c1^3*c2 - 3*a2^2*b1^2*c1*c2^3 - a2^2*b1*b2^3*c1^2 + a2^2*b1*b2^3*c2^2 - a2^2*b1*b2^2*c1^2*c2 + 3*a2^2*b1*b2^2*c2^3 + 2*a2^2*b1*b2*c1^4 - 2*a2^2*b1*b2*c1^2*c2^2 - 4*a2^2*b1*b2*c2^4 - 3*a2^2*b2^4*c1*c2 + 3*a2^2*b2^2*c1^3*c2 + 3*a2^2*b2^2*c1*c2^3 + 2*a2*b1^4*c1^3 + 3*a2*b1^3*b2*c1^2*c2 - a2*b1^3*b2*c2^3 - 3*a2*b1^3*c1^4 - 3*a2*b1^3*c1^2*c2^2 + 3*a2*b1^2*b2^2*c1^3 + 3*a2*b1^2*b2^2*c1*c2^2 - 3*a2*b1^2*b2*c1^3*c2 - 3*a2*b1^2*b2*c1*c2^3 + a2*b1^2*c1^5 + 2*a2*b1^2*c1^3*c2^2 + a2*b1^2*c1*c2^4 + 3*a2*b1*b2^3*c1^2*c2 - a2*b1*b2^3*c2^3 - 3*a2*b1*b2^2*c1^4 - 3*a2*b1*b2^2*c1^2*c2^2 + a2*b1*b2*c1^4*c2 + 2*a2*b1*b2*c1^2*c2^3 + a2*b1*b2*c2^5 + a2*b2^4*c1^3 + 3*a2*b2^4*c1*c2^2 - 3*a2*b2^3*c1^3*c2 - 3*a2*b2^3*c1*c2^3) * hr1 + (3*a1^4*b1^2*c1*c2 - 2*a1^4*b1*b2*c1^2 + 2*a1^4*b1*b2*c2^2 - 3*a1^4*b1*c1^2*c2 - a1^4*b1*c2^3 - a1^4*b2^2*c1*c2 + 2*a1^4*b2*c1^3 - a1^3*a2*b1^2*c1^2 + a1^3*a2*b1^2*c2^2 + a1^3*a2*b1*c1^3 - 3*a1^3*a2*b1*c1*c2^2 - a1^3*a2*b2^2*c1^2 + a1^3*a2*b2^2*c2^2 + 3*a1^3*a2*b2*c1^2*c2 - a1^3*a2*b2*c2^3 - 3*a1^3*b1^3*c1*c2 - a1^3*b1^2*b2*c2^2 - 3*a1^3*b1*b2^2*c1*c2 + 3*a1^3*b1*b2*c1^3 - a1^3*b1*b2*c1*c2^2 + 3*a1^3*b1*c1^3*c2 + 3*a1^3*b1*c1*c2^3 - a1^3*b2^3*c2^2 + 5*a1^3*b2^2*c1^2*c2 + a1^3*b2^2*c2^3 - 3*a1^3*b2*c1^4 - 3*a1^3*b2*c1^2*c2^2 + 4*a1^2*a2^2*b1^2*c1*c2 - 4*a1^2*a2^2*b1*b2*c1^2 + 4*a1^2*a2^2*b1*b2*c2^2 - 3*a1^2*a2^2*b1*c1^2*c2 - 3*a1^2*a2^2*b1*c2^3 - 4*a1^2*a2^2*b2^2*c1*c2 + 3*a1^2*a2^2*b2*c1^3 + 3*a1^2*a2^2*b2*c1*c2^2 + 3*a1^2*a2*b1^3*c1^2 - 2*a1^2*a2*b1^3*c2^2 - a1^2*a2*b1^2*b2*c1*c2 - 3*a1^2*a2*b1^2*c1^3 + a1^2*a2*b1^2*c1*c2^2 + 3*a1^2*a2*b1*b2^2*c1^2 - 2*a1^2*a2*b1*b2^2*c2^2 + a1^2*a2*b1*b2*c1^2*c2 - 3*a1^2*a2*b1*b2*c2^3 + 3*a1^2*a2*b1*c1^2*c2^2 + 3*a1^2*a2*b1*c2^4 - a1^2*a2*b2^3*c1*c2 - 2*a1^2*a2*b2^2*c1^3 + 6*a1^2*a2*b2^2*c1*c2^2 - 3*a1^2*a2*b2*c1^3*c2 - 3*a1^2*a2*b2*c1*c2^3 + 3*a1^2*b1^3*c1^2*c2 + a1^2*b1^3*c2^3 + 2*a1^2*b1^2*b2*c1*c2^2 - 3*a1^2*b1^2*c1^3*c2 - 3*a1^2*b1^2*c1*c2^3 + 3*a1^2*b1*b2^2*c1^2*c2 + a1^2*b1*b2^2*c2^3 - a1^2*b1*b2*c1^4 - 2*a1^2*b1*b2*c1^2*c2^2 - a1^2*b1*b2*c2^4 + 2*a1^2*b2^3*c1*c2^2 - 3*a1^2*b2^2*c1^3*c2 - 3*a1^2*b2^2*c1*c2^3 + a1^2*b2*c1^5 + 2*a1^2*b2*c1^3*c2^2 + a1^2*b2*c1*c2^4 - a1*a2^3*b1^2*c1^2 + a1*a2^3*b1^2*c2^2 + a1*a2^3*b1*c1^3 - 3*a1*a2^3*b1*c1*c2^2 - a1*a2^3*b2^2*c1^2 + a1*a2^3*b2^2*c2^2 + 3*a1*a2^3*b2*c1^2*c2 - a1*a2^3*b2*c2^3 + a1*a2^2*b1^3*c1*c2 + 2*a1*a2^2*b1^2*b2*c1^2 - 3*a1*a2^2*b1^2*b2*c2^2 - 6*a1*a2^2*b1^2*c1^2*c2 + 2*a1*a2^2*b1^2*c2^3 + a1*a2^2*b1*b2^2*c1*c2 + 3*a1*a2^2*b1*b2*c1^3 - a1*a2^2*b1*b2*c1*c2^2 + 3*a1*a2^2*b1*c1^3*c2 + 3*a1*a2^2*b1*c1*c2^3 + 2*a1*a2^2*b2^3*c1^2 - 3*a1*a2^2*b2^3*c2^2 - a1*a2^2*b2^2*c1^2*c2 + 3*a1*a2^2*b2^2*c2^3 - 3*a1*a2^2*b2*c1^4 - 3*a1*a2^2*b2*c1^2*c2^2 - 3*a1*a2*b1^3*c1^3 + a1*a2*b1^3*c1*c2^2 - a1*a2*b1^2*b2*c1^2*c2 + 3*a1*a2*b1^2*b2*c2^3 + 4*a1*a2*b1^2*c1^4 + 2*a1*a2*b1^2*c1^2*c2^2 - 2*a1*a2*b1^2*c2^4 - 3*a1*a2*b1*b2^2*c1^3 + a1*a2*b1*b2^2*c1*c2^2 - a1*a2*b1*c1^5 - 2*a1*a2*b1*c1^3*c2^2 - a1*a2*b1*c1*c2^4 - a1*a2*b2^3*c1^2*c2 + 3*a1*a2*b2^3*c2^3 + 2*a1*a2*b2^2*c1^4 - 2*a1*a2*b2^2*c1^2*c2^2 - 4*a1*a2*b2^2*c2^4 + a1*a2*b2*c1^4*c2 + 2*a1*a2*b2*c1^2*c2^3 + a1*a2*b2*c2^5 + a2^4*b1^2*c1*c2 - 2*a2^4*b1*b2*c1^2 + 2*a2^4*b1*b2*c2^2 - 2*a2^4*b1*c2^3 - 3*a2^4*b2^2*c1*c2 + a2^4*b2*c1^3 + 3*a2^4*b2*c1*c2^2 + a2^3*b1^3*c1^2 + 3*a2^3*b1^2*b2*c1*c2 - a2^3*b1^2*c1^3 - 5*a2^3*b1^2*c1*c2^2 + a2^3*b1*b2^2*c1^2 + a2^3*b1*b2*c1^2*c2 - 3*a2^3*b1*b2*c2^3 + 3*a2^3*b1*c1^2*c2^2 + 3*a2^3*b1*c2^4 + 3*a2^3*b2^3*c1*c2 - 3*a2^3*b2*c1^3*c2 - 3*a2^3*b2*c1*c2^3 - 2*a2^2*b1^3*c1^2*c2 - a2^2*b1^2*b2*c1^3 - 3*a2^2*b1^2*b2*c1*c2^2 + 3*a2^2*b1^2*c1^3*c2 + 3*a2^2*b1^2*c1*c2^3 - 2*a2^2*b1*b2^2*c1^2*c2 + a2^2*b1*b2*c1^4 + 2*a2^2*b1*b2*c1^2*c2^2 + a2^2*b1*b2*c2^4 - a2^2*b1*c1^4*c2 - 2*a2^2*b1*c1^2*c2^3 - a2^2*b1*c2^5 - a2^2*b2^3*c1^3 - 3*a2^2*b2^3*c1*c2^2 + 3*a2^2*b2^2*c1^3*c2 + 3*a2^2*b2^2*c1*c2^3) * hr2

/-! ### Bridges between the plane and coordinates -/

theorem dist_sq (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0)^2 + (X 1 - Y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem vadd_apply (X Y : Plane) (r : ℝ) (i : Fin 2) :
    (r • (Y -ᵥ X) +ᵥ X) i = r * (Y i - X i) + X i := by
  simp

/-- Three points are collinear if the cross product of their difference vectors vanishes. -/
theorem collinear_of_cross (X Y Z : Plane)
    (h : cross (Y 0 - X 0) (Y 1 - X 1) (Z 0 - X 0) (Z 1 - X 1) = 0) :
    Collinear ℝ ({X, Y, Z} : Set Plane) := by
  unfold cross at h
  by_cases hXY : Y = X
  · subst hXY
    simp [collinear_pair]
  have hv : Y 0 - X 0 ≠ 0 ∨ Y 1 - X 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hXY
    ext i; fin_cases i
    · simpa [sub_eq_zero] using hc.1
    · simpa [sub_eq_zero] using hc.2
  rw [collinear_iff_of_mem (p₀ := X) (by simp)]
  refine ⟨Y -ᵥ X, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · rcases hv with hv | hv
    · refine ⟨(p 0 - X 0) / (Y 0 - X 0), ?_⟩
      ext i; fin_cases i
      · simp; field_simp; ring
      · simp; field_simp; linear_combination h
    · refine ⟨(p 1 - X 1) / (Y 1 - X 1), ?_⟩
      ext i; fin_cases i
      · simp; field_simp; linear_combination -h
      · simp; field_simp; ring

/-- Collinear points have vanishing cross product. -/
theorem cross_of_collinear (X Y Z : Plane) (h : Collinear ℝ ({X, Y, Z} : Set Plane)) :
    cross (Y 0 - X 0) (Y 1 - X 1) (Z 0 - X 0) (Z 1 - X 1) = 0 := by
  rw [collinear_iff_of_mem (p₀ := X) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv Y (by simp)
  obtain ⟨s, hs⟩ := hv Z (by simp)
  have hr0 : Y 0 = r * v 0 + X 0 := by rw [hr]; simp
  have hr1 : Y 1 = r * v 1 + X 1 := by rw [hr]; simp
  have hs0 : Z 0 = s * v 0 + X 0 := by rw [hs]; simp
  have hs1 : Z 1 = s * v 1 + X 1 := by rw [hs]; simp
  unfold cross
  rw [hr0, hr1, hs0, hs1]
  ring

/-- `dist O X = dist O Y` in coordinates relative to `O`. -/
theorem eqdist_iff (O X Y : Plane) (h : dist O X = dist O Y) :
    (X 0 - O 0)^2 + (X 1 - O 1)^2 = (Y 0 - O 0)^2 + (Y 1 - O 1)^2 := by
  have h2 := congrArg (· ^ 2) h
  simp only [dist_sq] at h2
  linear_combination h2

/-- `dist P O = dist P X` in coordinates relative to `O`. -/
theorem perp_bisector_coord (O P X : Plane) (h : dist P O = dist P X) :
    2 * ((P 0 - O 0) * (X 0 - O 0) + (P 1 - O 1) * (X 1 - O 1)) =
      (X 0 - O 0)^2 + (X 1 - O 1)^2 := by
  have h2 := congrArg (· ^ 2) h
  simp only [dist_sq] at h2
  linear_combination h2

/-- In a genuine triangle `O X Y` with `|OX| = |OY|`, the cross product `OX × OY` is nonzero. -/
theorem cross_ne_zero (O X Y : Plane) (h : ¬ Collinear ℝ ({O, X, Y} : Set Plane)) :
    cross (X 0 - O 0) (X 1 - O 1) (Y 0 - O 0) (Y 1 - O 1) ≠ 0 :=
  fun hc => h (collinear_of_cross O X Y hc)

/-! ### Kosnita's theorem -/

/-- The coordinate core: the lines are not parallel, and the concurrency polynomial vanishes. -/
theorem core (a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 : ℝ)
    (ha : a1^2 + a2^2 = b1^2 + b2^2) (hc : a1^2 + a2^2 = c1^2 + c2^2)
    (hp1 : 2 * (p1 * b1 + p2 * b2) = b1^2 + b2^2) (hp2 : 2 * (p1 * c1 + p2 * c2) = c1^2 + c2^2)
    (hq1 : 2 * (q1 * c1 + q2 * c2) = c1^2 + c2^2) (hq2 : 2 * (q1 * a1 + q2 * a2) = a1^2 + a2^2)
    (hr1 : 2 * (r1 * a1 + r2 * a2) = a1^2 + a2^2) (hr2 : 2 * (r1 * b1 + r2 * b2) = b1^2 + b2^2)
    (hKa : cross b1 b2 c1 c2 ≠ 0) (hKb : cross c1 c2 a1 a2 ≠ 0) (hKc : cross a1 a2 b1 b2 ≠ 0)
    (hT : cross (b1 - a1) (b2 - a2) (c1 - a1) (c2 - a2) ≠ 0)
    (hS : sumSq a1 a2 b1 b2 c1 c2 ≠ 0) :
    den a1 a2 b1 b2 p1 p2 q1 q2 ≠ 0 ∧ conc a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 = 0 := by
  have hR : a1^2 + a2^2 ≠ 0 := by
    intro h0
    have e1 : a1 ^ 2 = 0 := by nlinarith [sq_nonneg a1, sq_nonneg a2]
    have e2 : a2 ^ 2 = 0 := by nlinarith [sq_nonneg a1, sq_nonneg a2]
    apply hKc
    rw [pow_eq_zero_iff two_ne_zero] at e1 e2
    unfold cross; rw [e1, e2]; ring
  constructor
  · intro h0
    have := cert_den a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 ha hc hp1 hp2 hq1 hq2 hr1 hr2
    rw [h0, mul_zero] at this
    exact mul_ne_zero (mul_ne_zero hS hT) hR this.symm
  · have := cert_conc a1 a2 b1 b2 c1 c2 p1 p2 q1 q2 r1 r2 ha hc hp1 hp2 hq1 hq2 hr1 hr2
    have hK : (2 * cross b1 b2 c1 c2) * (2 * cross c1 c2 a1 a2) * (2 * cross a1 a2 b1 b2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hKa) (mul_ne_zero two_ne_zero hKb))
        (mul_ne_zero two_ne_zero hKc)
    exact (mul_eq_zero.mp this).resolve_left hK

/-- **Kosnita's theorem.** `O` is the circumcentre of `ABC` and `Oa`, `Ob`, `Oc` are the
circumcentres of `OBC`, `OCA`, `OAB`. If `AB² + BC² + CA² ≠ 5 R²` (on that locus the lines can
be parallel), the lines `A Oa`, `B Ob`, `C Oc` are concurrent. -/
theorem kosnita (A B C O Oa Ob Oc : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hOA : dist O A = dist O B) (hOC : dist O A = dist O C)
    (hOBC : ¬ Collinear ℝ ({O, B, C} : Set Plane))
    (hOCA : ¬ Collinear ℝ ({O, C, A} : Set Plane))
    (hOAB : ¬ Collinear ℝ ({O, A, B} : Set Plane))
    (hOa1 : dist Oa O = dist Oa B) (hOa2 : dist Oa O = dist Oa C)
    (hOb1 : dist Ob O = dist Ob C) (hOb2 : dist Ob O = dist Ob A)
    (hOc1 : dist Oc O = dist Oc A) (hOc2 : dist Oc O = dist Oc B)
    (hS : dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2 ≠ 5 * dist O A ^ 2) :
    ∃ P : Plane, Collinear ℝ ({A, Oa, P} : Set Plane) ∧ Collinear ℝ ({B, Ob, P} : Set Plane) ∧
      Collinear ℝ ({C, Oc, P} : Set Plane) := by
  have hT : cross ((B 0 - O 0) - (A 0 - O 0)) ((B 1 - O 1) - (A 1 - O 1))
      ((C 0 - O 0) - (A 0 - O 0)) ((C 1 - O 1) - (A 1 - O 1)) ≠ 0 := by
    intro h0
    apply hABC
    apply collinear_of_cross
    rw [← h0]; unfold cross; ring
  have hS' : sumSq (A 0 - O 0) (A 1 - O 1) (B 0 - O 0) (B 1 - O 1) (C 0 - O 0) (C 1 - O 1) ≠ 0 := by
    intro h0
    apply hS
    simp only [dist_sq]
    unfold sumSq at h0
    linear_combination h0
  obtain ⟨hD, hE⟩ := core _ _ _ _ _ _ _ _ _ _ _ _
    (eqdist_iff O A B hOA) (eqdist_iff O A C hOC)
    (perp_bisector_coord O Oa B hOa1) (perp_bisector_coord O Oa C hOa2)
    (perp_bisector_coord O Ob C hOb1) (perp_bisector_coord O Ob A hOb2)
    (perp_bisector_coord O Oc A hOc1) (perp_bisector_coord O Oc B hOc2)
    (cross_ne_zero O B C hOBC) (cross_ne_zero O C A hOCA) (cross_ne_zero O A B hOAB) hT hS'
  set d := den (A 0 - O 0) (A 1 - O 1) (B 0 - O 0) (B 1 - O 1)
    (Oa 0 - O 0) (Oa 1 - O 1) (Ob 0 - O 0) (Ob 1 - O 1) with hd
  set n := cross (Ob 0 - B 0) (Ob 1 - B 1) (A 0 - B 0) (A 1 - B 1) with hn
  have hdn : d = cross (Oa 0 - A 0) (Oa 1 - A 1) (Ob 0 - B 0) (Ob 1 - B 1) := by
    rw [hd]; unfold den cross; ring
  refine ⟨(n / d) • (Oa -ᵥ A) +ᵥ A, ?_, ?_, ?_⟩
  · rw [collinear_iff_of_mem (p₀ := A) (by simp)]
    refine ⟨Oa -ᵥ A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨n / d, rfl⟩
  · apply collinear_of_cross
    simp only [vadd_apply]
    have key : ∀ x : ℝ, x = n / d → cross (Ob 0 - B 0) (Ob 1 - B 1)
        (x * (Oa 0 - A 0) + A 0 - B 0) (x * (Oa 1 - A 1) + A 1 - B 1) = n + x * (-d) := by
      intro x _; rw [hdn, hn]; unfold cross; ring
    rw [key _ rfl]
    field_simp
    ring
  · apply collinear_of_cross
    simp only [vadd_apply]
    have hc : conc (A 0 - O 0) (A 1 - O 1) (B 0 - O 0) (B 1 - O 1) (C 0 - O 0) (C 1 - O 1)
        (Oa 0 - O 0) (Oa 1 - O 1) (Ob 0 - O 0) (Ob 1 - O 1) (Oc 0 - O 0) (Oc 1 - O 1) =
        cross (Oc 0 - C 0) (Oc 1 - C 1) (d * (A 0 - C 0) + n * (Oa 0 - A 0))
          (d * (A 1 - C 1) + n * (Oa 1 - A 1)) := by
      rw [hd, hn]; unfold conc den cross; ring
    have key : ∀ x : ℝ, cross (Oc 0 - C 0) (Oc 1 - C 1)
        (x * (Oa 0 - A 0) + A 0 - C 0) (x * (Oa 1 - A 1) + A 1 - C 1) * d =
        cross (Oc 0 - C 0) (Oc 1 - C 1) (d * (A 0 - C 0) + (x * d) * (Oa 0 - A 0))
          (d * (A 1 - C 1) + (x * d) * (Oa 1 - A 1)) := by
      intro x; unfold cross; ring
    have h2 := key (n / d)
    rw [div_mul_cancel₀ n hD, ← hc, hE] at h2
    exact (mul_eq_zero.mp h2).resolve_right hD

end Kosnita
