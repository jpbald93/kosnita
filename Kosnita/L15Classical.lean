import Kosnita.Basic

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/


/-!
# Paper D — classical statements D1–D7 (blind formalisation)

All statements live in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`.
Constructed objects (second intersection points, Clifford points, Fermat points,
Thébault circles, auxiliary circumcentres, bisector feet) are passed in as data
together with their DEFINING property; well-definedness facts that are needed only
to make such data exist are stated separately as `_obligation` theorems.
-/

open EuclideanGeometry

noncomputable section

namespace Kosnita.Classical

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ## D1 — Clifford's circle theorems -/

/-- OWN DEFINITION. General position hypothesis of D1 for `n` circles `c i` through a
common point `M`: genuine circles (positive radius), pairwise distinct, `P i j` is a
second common point of `c i` and `c j` different from `M`, and for any three circles the
three second points are not collinear. (Since distinct circles meet in at most two points,
`P i j` is uniquely determined by these conditions.) -/
structure CliffordGP (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt) (P : Fin n → Fin n → Pt) :
    Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  second_mem : ∀ i j, i ≠ j → P i j ∈ c i ∧ P i j ∈ c j
  second_ne : ∀ i j, i ≠ j → P i j ≠ M
  noncollinear : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i j, P i k, P j k}

/-- OWN DEFINITION. `X` lies on every circle `Γ_ijk` (through the non-collinear points
`P i j, P i k, P j k`) for `i, j, k` pairwise distinct in `S`. For `S` with four elements
this says that `X` is a common point of the four circles of D1(a) (a "Clifford point").
Because `P i j, P i k, P j k` are non-collinear, `Cospherical {P i j, P i k, P j k, X}`
means exactly that `X` lies on their (unique) circumcircle. -/
def OnAllGamma {n : ℕ} (P : Fin n → Fin n → Pt) (S : Finset (Fin n)) (X : Pt) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k →
    Cospherical ({P i j, P i k, P j k, X} : Set Pt)

/-- D1(a), Clifford n = 4: the four circles `Γ_123, Γ_124, Γ_134, Γ_234` have a common
point. -/
def classical_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) : Prop := 
    ∃ X : Pt, OnAllGamma P Finset.univ X


/-- D1(b), Clifford n = 5: the five Clifford points `X l` (of the four circles obtained by
omitting circle `l`) lie on one circle. -/
def classical_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) : Prop := 
    Cospherical (Set.range X)


/-- D1(c), Clifford n = 6: for each `m`, the five Clifford points `X m l` (`l ≠ m`) of the
five circles other than `m` lie on a circle `C m` (part (b)); these six circles have a
common point. `X m l` is the Clifford point of the four circles other than `m, l`. -/
def classical_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) : Prop := 
    ∃ Y : Pt, ∀ m, Y ∈ C m


/-- OWN DEFINITION. Data of Clifford's chain for `n` circles `c i` through `M`, levels
indexed by subsets `S` of the circles: `circ S` (for `|S|` odd) is the circle and `pt S`
(for `|S|` even) the point attached to `S`.
* level 1: `circ {i} = c i`;
* level 2: `pt {i,j}` is the second intersection of `c i, c j` (≠ `M`);
* odd level `|S| = 2k+1 ≥ 3`: `circ S` passes through the `|S|` points `pt (S \ {i})`,
  which are not collinear (general position), so `circ S` is uniquely determined;
* even level `|S| = 2k ≥ 4`: `pt S` lies on the `|S|` circles `circ (S \ {i})` and is their
  unique common point (general position).
All levels strictly below `n` are part of the data/hypotheses (they are the lower
instances of the chain); the theorems below assert the top level `n`. -/
structure CliffordChain (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt) : Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  level_one : ∀ i, circ {i} = c i
  level_two : ∀ S : Finset (Fin n), S.card = 2 →
    pt S ≠ M ∧ ∀ i ∈ S, pt S ∈ circ (S.erase i)
  odd_mem : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt (S.erase i) ∈ circ S
  odd_gp : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ¬ Collinear ℝ ((fun i => pt (S.erase i)) '' (S : Set (Fin n)))
  even_mem : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt S ∈ circ (S.erase i)
  even_gp : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ Y : Pt, (∀ i ∈ S, Y ∈ circ (S.erase i)) → Y = pt S

/-- D1(d), Clifford's chain, even step (all even `n ≥ 4`): the `n` circles of level
`n - 1` pass through one common point.
(The case `n = 2` is the general-position hypothesis `level_two` itself.) -/
def classical_D1_d_even (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ) : Prop := 
    ∃ Y : Pt, ∀ i, Y ∈ circ (Finset.univ.erase i)


/-- D1(d), Clifford's chain, odd step (all odd `n ≥ 3`): the `n` points of level `n - 1`
lie on one circle. -/
def classical_D1_d_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ)
    -- EXTRA HYPOTHESIS: the top-level points are not collinear ("one circle"). For `n = 3`
    -- this is exactly the non-collinearity hypothesis of (a).
    -- AMBIGUOUS: drop it and conclude `Cospherical … ∨ Collinear ℝ …` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range fun i => pt (Finset.univ.erase i))) : Prop := 
    Cospherical (Set.range fun i => pt (Finset.univ.erase i))


/-! ## D2 — Miquel's pentagram (five circles) theorem -/

/-- D2. Five lines `ℓ 0, …, ℓ 4` in general position (no two parallel, no three
concurrent), labelled in the cyclic order of the sides of the inner pentagon: its vertices
are `V i = ℓ i ∩ ℓ (i+1)`, the star points are `T i = ℓ (i-1) ∩ ℓ (i+1)`, and the outer
triangle `i` (bounded by `ℓ (i-1), ℓ i, ℓ (i+1)`) has vertices `V (i-1), V i, T i` and
circumcircle `ω i`.
AMBIGUOUS: the labelling is only required to be cyclic as above; we do not additionally
require the inner pentagon to be convex / the figure to be a "star" (alternative: add a
hypothesis that the `V i` form a convex pentagon with the `T i` outside it).
Consecutive circles `ω i, ω (i+1)` meet in the inner vertex `V i` and in
a second point `Q i`. Then the five points `Q i` lie on one circle. -/
def classical_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) : Prop := 
    Cospherical (Set.range Q)


/-- D2 obligation (well-formedness only): for five lines in general position the
intersection points `V i`, `T i` exist and the three vertices of each outer triangle are
non-collinear, so the circumcircles `ω i` exist (and are unique). -/
def classical_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) : Prop := 
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)


/-! ## D3 — Lester's theorem -/

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected OUTWARDLY on side
`q r` of triangle `p q r` (opposite side of line `q r` from `p`). -/
def IsOuterApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SOppSide p X

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected INWARDLY on side
`q r` of triangle `p q r` (same side of line `q r` as `p`). -/
def IsInnerApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SSameSide p X

/-- OWN DEFINITION. First Fermat point (first isogonic centre): common point of the lines
joining each vertex to the apex of the outward equilateral triangle on the opposite side. -/
def IsFirstFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsOuterApex a b c A' ∧ IsOuterApex b c a B' ∧ IsOuterApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- OWN DEFINITION. Second Fermat point (second isogonic centre): same with the inward
equilateral triangles. -/
def IsSecondFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsInnerApex a b c A' ∧ IsInnerApex b c a B' ∧ IsInnerApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- D3, Lester's theorem: in a scalene triangle the two Fermat points, the circumcentre and
the nine-point centre are concyclic. -/
def classical_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)


/-- D3 obligation (well-formedness only): both Fermat points exist (the second one needs
the triangle not to be equilateral; scalene suffices). -/
def classical_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) : Prop := 
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)


/-! ## D4 — Sawayama–Thébault theorem -/

/-- OWN DEFINITION. The circle `ω` (positive radius) is tangent to the line `p q`. -/
def TangentToLine (ω : Sphere Pt) (p q : Pt) : Prop :=
  0 < ω.radius ∧ Metric.infDist ω.center (line[ℝ, p, q] : Set Pt) = ω.radius

/-- OWN DEFINITION. The circle `ω` (positive radius) is internally tangent to the circle `Ω`
(lies inside `Ω` and touches it). -/
def InternallyTangent (ω Ω : Sphere Pt) : Prop :=
  0 < ω.radius ∧ ω.radius < Ω.radius ∧ dist ω.center Ω.center = Ω.radius - ω.radius

/-- D4, Sawayama–Thébault: `D` on side `BC`; `ω₁, ω₂` are tangent to lines `AD`, `BC`,
internally tangent to the circumcircle, one on each side of `AD`. Then their centres and
the incentre are collinear. -/
def classical_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt)


/-- D4 obligation (well-formedness only): the two Thébault circles exist. -/
def classical_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a


/-! ## D5 — Kosnita's theorem -/

/-- OWN DEFINITION. `o` is equidistant from `p, q, r`, i.e. (for `p, q, r` not collinear) the
circumcentre of triangle `p q r`. -/
def IsCircumcenterOf (o p q r : Pt) : Prop :=
  dist o p = dist o q ∧ dist o p = dist o r

/-- D5, Kosnita: with `O` the circumcentre and `O_a, O_b, O_c` the circumcentres of `OBC`,
`OCA`, `OAB`, the lines `AO_a, BO_b, CO_c` are concurrent.
(If `O` lies on a side — right triangle — the corresponding `O_x` does not exist and the
statement is vacuous; see the obligation.) -/
def classical_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc]))


/-- D5 obligation (well-formedness only): if the circumcentre is not on line `BC`, the
circumcentre of `OBC` exists. -/
def classical_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c


/-! ## D6 — Blundon's fundamental inequality -/

/-- D6, Blundon, lower bound. -/
def classical_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2


/-- D6, Blundon, upper bound. -/
def classical_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)


/-- D6 obligation (well-formedness only): the radicand is non-negative (Euler `R ≥ 2r`),
so `Real.sqrt` is the genuine square root rather than its junk value `0`. -/
def classical_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius


/-! ## D7 — Steiner–Lehmus theorem -/

/-- OWN DEFINITION. `e` is the foot of the internal bisector from vertex `v` of the angle
`p v q`: `e` lies on segment `p q` and bisects the angle at `v`. -/
def IsBisectorFoot (v p q e : Pt) : Prop :=
  Wbtw ℝ p e q ∧ ∠ p v e = ∠ e v q

/-- D7, Steiner–Lehmus: if the internal bisectors from `B` and `C` (vertex to opposite side)
have equal length, then `AB = AC`. -/
def classical_D7 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (e f : Pt)
    (he : IsBisectorFoot b a c e) (hf : IsBisectorFoot c a b f)
    (hlen : dist b e = dist c f) : Prop := 
    dist a b = dist a c


/-- D7 obligation (well-formedness only): the bisector foot exists. -/
def classical_D7_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    ∃ e, IsBisectorFoot b a c e


end Kosnita.Classical

namespace Kosnita.Classical

theorem cov_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c := by
  dsimp
  intro hnc
  let u : Affine.Triangle ℝ Pt := ⟨![ (⟨![a,b,c],h⟩ : Affine.Triangle ℝ Pt).circumcenter, b, c],
    affineIndependent_iff_not_collinear_set.2 hnc⟩
  refine ⟨u.circumcenter, ?_, ?_⟩
  · exact (u.dist_circumcenter_eq_circumradius' 0).trans
      (u.dist_circumcenter_eq_circumradius' 1).symm
  · exact (u.dist_circumcenter_eq_circumradius' 0).trans
      (u.dist_circumcenter_eq_circumradius' 2).symm


theorem cov_D5_part (a b c : Pt) (h : AffineIndependent ℝ ![a,b,c]) (Oa Ob Oc : Pt)
    (hOBC : ¬ Collinear ℝ { (⟨![a,b,c],h⟩ : Affine.Triangle ℝ Pt).circumcenter, b, c})
    (hOCA : ¬ Collinear ℝ { (⟨![a,b,c],h⟩ : Affine.Triangle ℝ Pt).circumcenter, c, a})
    (hOAB : ¬ Collinear ℝ { (⟨![a,b,c],h⟩ : Affine.Triangle ℝ Pt).circumcenter, a, b})
    (hS : dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2 ≠
      5 * (⟨![a,b,c],h⟩ : Affine.Triangle ℝ Pt).circumradius ^ 2) :
    classical_D5 a b c h Oa Ob Oc := by
  intro hOa hOb hOc ha hb hc
  let t : Affine.Triangle ℝ Pt := ⟨![a,b,c],h⟩
  have e0 : dist t.circumcenter a = t.circumradius := t.dist_circumcenter_eq_circumradius' 0
  have e1 : dist t.circumcenter b = t.circumradius := t.dist_circumcenter_eq_circumradius' 1
  have e2 : dist t.circumcenter c = t.circumradius := t.dist_circumcenter_eq_circumradius' 2
  obtain ⟨X, hX, hY, hZ⟩ := Kosnita.kosnita a b c t.circumcenter Oa Ob Oc
    (affineIndependent_iff_not_collinear_set.1 h) (e0.trans e1.symm) (e0.trans e2.symm)
    hOBC hOCA hOAB hOa.1 hOa.2 hOb.1 hOb.2 hOc.1 hOc.2 (by simpa only [e0] using hS)
  left
  exact ⟨X, hX.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) ha,
    hY.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hb,
    hZ.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hc⟩

 theorem cov_auxiliary_nondegenerate (o b c q : Pt) (hob : o ≠ b) (hoc : o ≠ c) (hbc : b ≠ c)
    (hq : IsCircumcenterOf q o b c) : ¬ Collinear ℝ {o,b,c} := by
  apply affineIndependent_iff_not_collinear_set.1
  apply Cospherical.affineIndependent_of_ne _ hob hoc hbc
  refine ⟨q,dist q o,?_⟩
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl|rfl|rfl
  · exact dist_comm _ _
  · rw [dist_comm]; exact hq.1.symm
  · rw [dist_comm]; exact hq.2.symm

 theorem cov_D5_nonparallel_part (a b c : Pt) (h : AffineIndependent ℝ ![a,b,c]) (Oa Ob Oc : Pt)
    (hS : dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2 ≠
      5 * (⟨![a,b,c],h⟩ : Affine.Triangle ℝ Pt).circumradius ^ 2) :
    classical_D5 a b c h Oa Ob Oc := by
  intro hOa hOb hOc ha hb hc
  let t : Affine.Triangle ℝ Pt := ⟨![a,b,c],h⟩
  have hnc := affineIndependent_iff_not_collinear_set.1 h
  have h0 : t.circumcenter ≠ a := by
    have hh := t.dist_circumcenter_eq_circumradius' 0
    have hp := t.circumradius_pos
    intro he
    change dist t.circumcenter a = t.circumradius at hh
    rw [he,dist_self] at hh
    linarith
  have h1 : t.circumcenter ≠ b := by
    have hh := t.dist_circumcenter_eq_circumradius' 1
    have hp := t.circumradius_pos
    intro he
    change dist t.circumcenter b = t.circumradius at hh
    rw [he,dist_self] at hh
    linarith
  have h2 : t.circumcenter ≠ c := by
    have hh := t.dist_circumcenter_eq_circumradius' 2
    have hp := t.circumradius_pos
    intro he
    change dist t.circumcenter c = t.circumradius at hh
    rw [he,dist_self] at hh
    linarith
  exact cov_D5_part a b c h Oa Ob Oc
    (cov_auxiliary_nondegenerate _ _ _ Oa h1 h2 (ne₂₃_of_not_collinear hnc) hOa)
    (cov_auxiliary_nondegenerate _ _ _ Ob h2 h0 (ne₁₃_of_not_collinear hnc).symm hOb)
    (cov_auxiliary_nondegenerate _ _ _ Oc h0 h1 (ne₁₂_of_not_collinear hnc) hOc)
    hS hOa hOb hOc ha hb hc


open Kosnita
 theorem cov_parallel_of_cross_zero (a p b q : Pt) (hap : a ≠ p) (hbq : b ≠ q)
    (hc : cross (p 0-a 0) (p 1-a 1) (q 0-b 0) (q 1-b 1) = 0) :
    (line[ℝ,a,p]).Parallel (line[ℝ,b,q]) := by
  have hi : Collinear ℝ ({(0:Pt),p-a,q-b} : Set Pt) :=
    collinear_of_cross _ _ _ (by simpa only [PiLp.sub_apply,PiLp.zero_apply,sub_zero] using hc)
  have hpa : p-a ≠ (0:Pt) := sub_ne_zero.2 hap.symm
  have hqb : q-b ≠ (0:Pt) := sub_ne_zero.2 hbq.symm
  have hm : q-b ∈ line[ℝ,(0:Pt),p-a] := hi.mem_affineSpan_of_mem_of_ne
    (by simp) (by simp) (by simp) hpa.symm
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hm
  have he : t • (p-a) = q-b := by simpa only [AffineMap.lineMap_apply_module',smul_zero,zero_add,sub_zero,add_zero] using ht
  have ht0 : t ≠ 0 := by intro hz; rw [hz,zero_smul] at he; exact hqb he.symm
  apply AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul'.2
  exact ⟨Units.mk0 t ht0,he⟩

 theorem cov_Kosnita_zero_locus (a b c o pa pb pc : Pt)
    (hoa : dist o a = dist o b) (hoc : dist o a = dist o c)
    (hbc : ¬ Collinear ℝ {o,b,c}) (hca : ¬ Collinear ℝ {o,c,a})
    (hpa : IsCircumcenterOf pa o b c) (hpb : IsCircumcenterOf pb o c a)
    (hpc : IsCircumcenterOf pc o a b)
    (hap : a ≠ pa) (hbp : b ≠ pb)
    (hs : dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2 = 5 * dist o a ^ 2) :
    (line[ℝ,a,pa]).Parallel (line[ℝ,b,pb]) := by
  have hz : sumSq (a 0-o 0) (a 1-o 1) (b 0-o 0) (b 1-o 1) (c 0-o 0) (c 1-o 1) = 0 := by
    simp only [dist_sq] at hs
    unfold sumSq
    linear_combination hs
  have hh := cert_den (a 0-o 0) (a 1-o 1) (b 0-o 0) (b 1-o 1) (c 0-o 0) (c 1-o 1)
    (pa 0-o 0) (pa 1-o 1) (pb 0-o 0) (pb 1-o 1) (pc 0-o 0) (pc 1-o 1)
    (eqdist_iff o a b hoa) (eqdist_iff o a c hoc)
    (perp_bisector_coord o pa b hpa.1) (perp_bisector_coord o pa c hpa.2)
    (perp_bisector_coord o pb c hpb.1) (perp_bisector_coord o pb a hpb.2)
    (perp_bisector_coord o pc a hpc.1) (perp_bisector_coord o pc b hpc.2)
  rw [hz,zero_mul,zero_mul] at hh
  have hk : (2 * cross (b 0-o 0) (b 1-o 1) (c 0-o 0) (c 1-o 1)) *
      (2 * cross (c 0-o 0) (c 1-o 1) (a 0-o 0) (a 1-o 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (cross_ne_zero o b c hbc))
      (mul_ne_zero two_ne_zero (cross_ne_zero o c a hca))
  have hd := (mul_eq_zero.1 hh).resolve_left hk
  apply cov_parallel_of_cross_zero a pa b pb hap hbp
  simpa only [den,sub_sub_sub_cancel_right] using hd

theorem cov_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc])) := by
  dsimp only
  intro hOa hOb hOc ha hb hc
  let t : Affine.Triangle ℝ Pt := ⟨![a,b,c],h⟩
  have e0 : dist t.circumcenter a = t.circumradius := t.dist_circumcenter_eq_circumradius' 0
  have e1 : dist t.circumcenter b = t.circumradius := t.dist_circumcenter_eq_circumradius' 1
  have e2 : dist t.circumcenter c = t.circumradius := t.dist_circumcenter_eq_circumradius' 2
  by_cases hs : dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2 = 5 * t.circumradius ^ 2
  · right
    have hnc := affineIndependent_iff_not_collinear_set.1 h
    have h0 : t.circumcenter ≠ a := dist_ne_zero.1 (e0.trans_ne t.circumradius_pos.ne')
    have h1 : t.circumcenter ≠ b := dist_ne_zero.1 (e1.trans_ne t.circumradius_pos.ne')
    have h2 : t.circumcenter ≠ c := dist_ne_zero.1 (e2.trans_ne t.circumradius_pos.ne')
    have hbc := cov_auxiliary_nondegenerate _ _ _ Oa h1 h2 (ne₂₃_of_not_collinear hnc) hOa
    have hca := cov_auxiliary_nondegenerate _ _ _ Ob h2 h0 (ne₁₃_of_not_collinear hnc).symm hOb
    have hab := cov_auxiliary_nondegenerate _ _ _ Oc h0 h1 (ne₁₂_of_not_collinear hnc) hOc
    constructor
    · exact cov_Kosnita_zero_locus a b c t.circumcenter Oa Ob Oc
        (e0.trans e1.symm) (e0.trans e2.symm) hbc hca hOa hOb hOc ha hb (by rwa [e0])
    · apply cov_Kosnita_zero_locus b c a t.circumcenter Ob Oc Oa
        (e1.trans e2.symm) (e1.trans e0.symm) hca hab hOb hOc hOa hb hc
      rw [e1]
      linarith
  · exact cov_D5_nonparallel_part a b c h Oa Ob Oc hs hOa hOb hOc ha hb hc


end Kosnita.Classical
