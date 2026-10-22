import Kosnita.Basic

/-!
# Layer 14: Mathlib-only restatement and a witness for Kosnita's theorem

`l14_kosnita` mentions only Mathlib notions. `T` is an `Affine.Triangle` in the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`, `O = T.circumcenter`, and `Ta`, `Tb`, `Tc` are Mathlib triangles with
vertices `O B C`, `O C A`, `O A B`. Their existence as triangles is the non-collinearity
hypothesis of the library theorem. Their circumcentres are Mathlib's `circumcenter`, and the
non-degeneracy condition `AB² + BC² + CA² ≠ 5R²` uses Mathlib's `circumradius`.
`l14w_kosnita` takes `A = (5, 0)`, `B = (3, 4)`, `C = (-4, -3)` (so `O = 0`, `R = 5`,
`AB² + BC² + CA² = 208 ≠ 125`). It computes the three circumcentres
`(-25/2, 25/2)`, `(5/2, -15/2)`, `(5/2, 5/4)` and the common point `(240/83, 125/83)`, and shows
that the three lines are pairwise distinct: no line through one vertex passes through another.
-/

namespace Kosnita

open EuclideanGeometry

/-- The points of a triangle, listed. -/
theorem l14b_points {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (T : Affine.Triangle ℝ P) :
    T.points = ![T.points 0, T.points 1, T.points 2] := by
  ext i; fin_cases i <;> rfl

theorem l14b_not_collinear {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (T : Affine.Triangle ℝ P) :
    ¬ Collinear ℝ ({T.points 0, T.points 1, T.points 2} : Set P) := by
  have h := T.independent
  rw [l14b_points T] at h
  exact affineIndependent_iff_not_collinear_set.1 h

/-- **Kosnita's theorem**, Mathlib-only statement. -/
theorem l14_kosnita (T Ta Tb Tc : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (ha : Ta.points = ![T.circumcenter, T.points 1, T.points 2])
    (hb : Tb.points = ![T.circumcenter, T.points 2, T.points 0])
    (hc : Tc.points = ![T.circumcenter, T.points 0, T.points 1])
    (hS : dist (T.points 0) (T.points 1) ^ 2 + dist (T.points 1) (T.points 2) ^ 2 +
      dist (T.points 2) (T.points 0) ^ 2 ≠ 5 * T.circumradius ^ 2) :
    ∃ P : EuclideanSpace ℝ (Fin 2),
      Collinear ℝ ({T.points 0, Ta.circumcenter, P} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Collinear ℝ ({T.points 1, Tb.circumcenter, P} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Collinear ℝ ({T.points 2, Tc.circumcenter, P} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have dO : ∀ i, dist T.circumcenter (T.points i) = T.circumradius := fun i => by
    rw [dist_comm]; exact T.dist_circumcenter_eq_circumradius i
  have nA := l14b_not_collinear Ta
  have nB := l14b_not_collinear Tb
  have nC := l14b_not_collinear Tc
  have a0 : Ta.points 0 = T.circumcenter := by rw [ha]; rfl
  have a1 : Ta.points 1 = T.points 1 := by rw [ha]; rfl
  have a2 : Ta.points 2 = T.points 2 := by rw [ha]; rfl
  have b0 : Tb.points 0 = T.circumcenter := by rw [hb]; rfl
  have b1 : Tb.points 1 = T.points 2 := by rw [hb]; rfl
  have b2 : Tb.points 2 = T.points 0 := by rw [hb]; rfl
  have c0 : Tc.points 0 = T.circumcenter := by rw [hc]; rfl
  have c1 : Tc.points 1 = T.points 0 := by rw [hc]; rfl
  have c2 : Tc.points 2 = T.points 1 := by rw [hc]; rfl
  rw [a0, a1, a2] at nA
  rw [b0, b1, b2] at nB
  rw [c0, c1, c2] at nC
  have dA : ∀ i, dist Ta.circumcenter (Ta.points i) = Ta.circumradius := fun i => by
    rw [dist_comm]; exact Ta.dist_circumcenter_eq_circumradius i
  have dB : ∀ i, dist Tb.circumcenter (Tb.points i) = Tb.circumradius := fun i => by
    rw [dist_comm]; exact Tb.dist_circumcenter_eq_circumradius i
  have dC : ∀ i, dist Tc.circumcenter (Tc.points i) = Tc.circumradius := fun i => by
    rw [dist_comm]; exact Tc.dist_circumcenter_eq_circumradius i
  refine kosnita (T.points 0) (T.points 1) (T.points 2) T.circumcenter Ta.circumcenter
    Tb.circumcenter Tc.circumcenter (l14b_not_collinear T) (by rw [dO, dO]) (by rw [dO, dO])
    nA nB nC ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← a0, ← a1, dA, dA]
  · rw [← a0, ← a2, dA, dA]
  · rw [← b0, ← b1, dB, dB]
  · rw [← b0, ← b2, dB, dB]
  · rw [← c0, ← c1, dC, dC]
  · rw [← c0, ← c2, dC, dC]
  · rwa [dO]

/-! ### Witness -/

theorem l14b_dist_eq_dist (X Y Z : EuclideanSpace ℝ (Fin 2))
    (h : (X 0 - Z 0) ^ 2 + (X 1 - Z 1) ^ 2 = (Y 0 - Z 0) ^ 2 + (Y 1 - Z 1) ^ 2) :
    dist X Z = dist Y Z := by
  have h2 : dist X Z ^ 2 = dist Y Z ^ 2 := by rw [dist_sq, dist_sq, h]
  exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h2

theorem l14b_circumcenter (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2))
    (h1 : dist (T.points 1) p = dist (T.points 0) p)
    (h2 : dist (T.points 2) p = dist (T.points 0) p) : T.circumcenter = p := by
  refine (T.eq_circumcenter_of_dist_eq (r := dist (T.points 0) p) ?_ ?_).symm
  · rw [T.span_eq_top (by simp)]; exact AffineSubspace.mem_top _ _ _
  · intro i; fin_cases i
    · rfl
    · exact h1
    · exact h2

theorem l14b_not_collinear_of_cross (X Y Z : EuclideanSpace ℝ (Fin 2))
    (h : cross (Y 0 - X 0) (Y 1 - X 1) (Z 0 - X 0) (Z 1 - X 1) ≠ 0) :
    ¬ Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) :=
  fun hc => h (cross_of_collinear X Y Z hc)

/-- Witness for `l14_kosnita`. -/
theorem l14w_kosnita :
    ∃ T Ta Tb Tc : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      T.points = ![!₂[5, 0], !₂[3, 4], !₂[-4, -3]] ∧
      Ta.points = ![T.circumcenter, T.points 1, T.points 2] ∧
      Tb.points = ![T.circumcenter, T.points 2, T.points 0] ∧
      Tc.points = ![T.circumcenter, T.points 0, T.points 1] ∧
      dist (T.points 0) (T.points 1) ^ 2 + dist (T.points 1) (T.points 2) ^ 2 +
        dist (T.points 2) (T.points 0) ^ 2 ≠ 5 * T.circumradius ^ 2 ∧
      T.circumcenter = !₂[0, 0] ∧ T.circumradius = 5 ∧
      Ta.circumcenter = !₂[-25/2, 25/2] ∧ Tb.circumcenter = !₂[5/2, -15/2] ∧
      Tc.circumcenter = !₂[5/2, 5/4] ∧
      Collinear ℝ ({T.points 0, Ta.circumcenter, !₂[240/83, 125/83]} :
        Set (EuclideanSpace ℝ (Fin 2))) ∧
      Collinear ℝ ({T.points 1, Tb.circumcenter, !₂[240/83, 125/83]} :
        Set (EuclideanSpace ℝ (Fin 2))) ∧
      Collinear ℝ ({T.points 2, Tc.circumcenter, !₂[240/83, 125/83]} :
        Set (EuclideanSpace ℝ (Fin 2))) ∧
      ¬ Collinear ℝ ({T.points 0, Ta.circumcenter, T.points 1} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ¬ Collinear ℝ ({T.points 1, Tb.circumcenter, T.points 2} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ¬ Collinear ℝ ({T.points 2, Tc.circumcenter, T.points 0} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      T.points 0 ≠ !₂[240/83, 125/83] ∧ T.points 1 ≠ !₂[240/83, 125/83] ∧
      T.points 2 ≠ !₂[240/83, 125/83] := by
  have nT : ¬ Collinear ℝ ({!₂[5, 0], !₂[3, 4], !₂[-4, -3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
    l14b_not_collinear_of_cross _ _ _ (by simp [cross]; norm_num)
  let T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![!₂[5, 0], !₂[3, 4], !₂[-4, -3]], affineIndependent_iff_not_collinear_set.2 nT⟩
  have hO : T.circumcenter = !₂[0, 0] :=
    l14b_circumcenter T _ (l14b_dist_eq_dist _ _ _ (by simp [T]; norm_num))
      (l14b_dist_eq_dist _ _ _ (by simp [T]; norm_num))
  have hR : T.circumradius = 5 := by
    rw [← T.dist_circumcenter_eq_circumradius 0, hO]
    have h := dist_sq (T.points 0) (!₂[0, 0])
    have h' : dist (T.points 0) (!₂[0, 0]) ^ 2 = 5 ^ 2 := by rw [h]; simp [T]
    exact (pow_left_inj₀ dist_nonneg (by norm_num) two_ne_zero).1 h'
  have nA : ¬ Collinear ℝ ({!₂[0, 0], !₂[3, 4], !₂[-4, -3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
    l14b_not_collinear_of_cross _ _ _ (by simp [cross]; norm_num)
  have nB : ¬ Collinear ℝ ({!₂[0, 0], !₂[-4, -3], !₂[5, 0]} : Set (EuclideanSpace ℝ (Fin 2))) :=
    l14b_not_collinear_of_cross _ _ _ (by simp [cross])
  have nC : ¬ Collinear ℝ ({!₂[0, 0], !₂[5, 0], !₂[3, 4]} : Set (EuclideanSpace ℝ (Fin 2))) :=
    l14b_not_collinear_of_cross _ _ _ (by simp [cross])
  let Ta : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![!₂[0, 0], !₂[3, 4], !₂[-4, -3]], affineIndependent_iff_not_collinear_set.2 nA⟩
  let Tb : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![!₂[0, 0], !₂[-4, -3], !₂[5, 0]], affineIndependent_iff_not_collinear_set.2 nB⟩
  let Tc : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![!₂[0, 0], !₂[5, 0], !₂[3, 4]], affineIndependent_iff_not_collinear_set.2 nC⟩
  have hA : Ta.circumcenter = !₂[-25/2, 25/2] :=
    l14b_circumcenter Ta _ (l14b_dist_eq_dist _ _ _ (by simp [Ta]; norm_num))
      (l14b_dist_eq_dist _ _ _ (by simp [Ta]; norm_num))
  have hB : Tb.circumcenter = !₂[5/2, -15/2] :=
    l14b_circumcenter Tb _ (l14b_dist_eq_dist _ _ _ (by simp [Tb]; norm_num))
      (l14b_dist_eq_dist _ _ _ (by simp [Tb]; norm_num))
  have hC : Tc.circumcenter = !₂[5/2, 5/4] :=
    l14b_circumcenter Tc _ (l14b_dist_eq_dist _ _ _ (by simp [Tc]; norm_num))
      (l14b_dist_eq_dist _ _ _ (by simp [Tc]; norm_num))
  refine ⟨T, Ta, Tb, Tc, rfl, ?_, ?_, ?_, ?_, hO, hR, hA, hB, hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hO]; ext i; fin_cases i <;> rfl
  · rw [hO]; ext i; fin_cases i <;> rfl
  · rw [hO]; ext i; fin_cases i <;> rfl
  · rw [hR, dist_sq, dist_sq, dist_sq]; simp [T]; norm_num
  · rw [hA]; exact collinear_of_cross _ _ _ (by simp [T, cross]; norm_num)
  · rw [hB]; exact collinear_of_cross _ _ _ (by simp [T, cross]; norm_num)
  · rw [hC]; exact collinear_of_cross _ _ _ (by simp [T, cross]; norm_num)
  · rw [hA]; exact l14b_not_collinear_of_cross _ _ _ (by simp [T, cross]; norm_num)
  · rw [hB]; exact l14b_not_collinear_of_cross _ _ _ (by simp [T, cross]; norm_num)
  · rw [hC]; exact l14b_not_collinear_of_cross _ _ _ (by simp [T, cross]; norm_num)
  all_goals
    intro h
    have := congrArg (fun X : EuclideanSpace ℝ (Fin 2) => X 0) h
    simp [T] at this
    norm_num at this

end Kosnita
