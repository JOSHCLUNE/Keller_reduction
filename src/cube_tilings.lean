import helpers

def in_cube {d : ℕ} (corner p : point d) : Prop :=
  ∀ coord : fin d, vector.nth corner coord ≤ vector.nth p coord ∧
                   vector.nth p coord < vector.nth corner coord + 1

--Defines the cube (set of d dimensional points) corner + [0, 1)^d
def cube {d : ℕ} (corner : point d) : set (point d) :=
  { p : point d | in_cube corner p }

lemma cube_intersection_lemma_left_implication : 
  ∀ d : ℕ, ∀ corner1 : point d, ∀ corner2 : point d,
  (cube corner1 ∩ cube corner2 = ∅) →
  (∃ coord : fin d, vector.nth corner1 coord - vector.nth corner2 coord ≥ 1 ∨ 
                    vector.nth corner2 coord - vector.nth corner1 coord ≥ 1) :=
begin
  intros _ _ _ h,
  have cube1_not_in_cube2 : ∀ p : point d, p ∈ cube corner1 → p ∉ cube corner2 :=
    begin
      rw [cube, cube, set.inter_def] at h,
      simp at h,
      rw set.eq_empty_iff_forall_not_mem at h,
      simp at h,
      rw [cube, cube],
      simp,
      exact h,
    end,
  rw [cube, cube] at cube1_not_in_cube2,
  simp at cube1_not_in_cube2,
  conv at cube1_not_in_cube2
  begin
    find (in_cube corner1 _) { rw in_cube },
    find (in_cube corner2 _) { rw in_cube },
  end,
  simp at cube1_not_in_cube2,
  contrapose cube1_not_in_cube2,
  rename cube1_not_in_cube2 no_far_coord,
  simp,
  simp at no_far_coord,
  let get_first_intersecting_point : fin d → ℝ :=
    λ coord : fin d, max (vector.nth corner1 coord) (vector.nth corner2 coord),
  let p : point d := vector.of_fn get_first_intersecting_point,
  use p,
  split,
  { intro coord,
    split, simp only [vector.nth_of_fn, le_max_iff, le_refl, true_or],
    simp only [vector.nth_of_fn, max_lt_iff, lt_add_iff_pos_right, zero_lt_one, true_and],
    replace no_far_coord := no_far_coord coord,
    contrapose no_far_coord,
    rw not_not,
    right,
    linarith,
  },
  intro coord,
  split, simp only [vector.nth_of_fn, le_max_iff, le_refl, or_true],
  simp only [vector.nth_of_fn, max_lt_iff, lt_add_iff_pos_right, zero_lt_one, and_true],
  replace no_far_coord := no_far_coord coord,
  contrapose no_far_coord,
  rw not_not,
  left,
  linarith,
end

lemma cube_intersection_lemma_right_implication :
  ∀ d : ℕ, ∀ corner1 : point d, ∀ corner2 : point d,
  (∃ coord : fin d, vector.nth corner1 coord - vector.nth corner2 coord ≥ 1 ∨ 
                    vector.nth corner2 coord - vector.nth corner1 coord ≥ 1
  ) → (cube corner1 ∩ cube corner2 = ∅)
  :=
begin
  intros _ _ _ exists_far_coord,
  cases exists_far_coord with x x_far_coord,
  rw set.inter_def,
  rw set.eq_empty_iff_forall_not_mem,
  intro p,
  simp,
  rw [cube, cube],
  simp,
  rw [in_cube, in_cube],
  simp,
  intro p_in_cube1,
  have p_in_cube1_x_coord := p_in_cube1 x,
  use x,
  intro corner2_le_p,
  cases x_far_coord, linarith,
  linarith,
end

lemma cube_intersection_lemma :
  ∀ d : ℕ, ∀ corner1 : point d, ∀ corner2 : point d,
  (∃ coord : fin d, vector.nth corner1 coord - vector.nth corner2 coord ≥ 1 ∨ 
                    vector.nth corner2 coord - vector.nth corner1 coord ≥ 1
  ) ↔ (cube corner1 ∩ cube corner2 = ∅) :=
begin
  repeat{intro},
  split,
  apply cube_intersection_lemma_right_implication,
  apply cube_intersection_lemma_left_implication,
end

--States whether two d dimensional cubes (as defined by their corners) are distinct and share a face
def is_facesharing {d : ℕ} (c1 c2 : point d) : Prop :=
  ∃ x : fin d, (vector.nth c1 x - vector.nth c2 x = 1 ∨
                vector.nth c2 x - vector.nth c1 x = 1) ∧
  ∀ y : fin d, x = y ∨ vector.nth c1 y = vector.nth c2 y

lemma is_facesharing_comm {d : ℕ} {corner1 : point d} {corner2 : point d} (h : is_facesharing corner1 corner2) :
  is_facesharing corner2 corner1 :=
begin
  rw is_facesharing at h,
  cases h with coord h,
  cases h,
  rw or_comm at h_left,
  rw is_facesharing,
  use coord,
  split, exact h_left,
  intro y,
  replace h_right := h_right y,
  cases h_right, {left, exact h_right,},
  right,
  symmetry,
  exact h_right,
end

--States whether a tiling contains any two distinct corners whose cubes share a face
def tiling_faceshare_free {d : ℕ} (T : set (point d)) : Prop :=
  ∀ c1 c2 ∈ T, ¬(is_facesharing c1 c2)

--States whether a set of d dimensional cubes (as defined by their corners) is a tiling in ℝ^d
def is_tiling {d : ℕ} (T : set (point d)) : Prop := 
  ∀ p : point d, ∃ corner ∈ T, p ∈ cube corner ∧ 
  (∀ alt_corner ∈ T, p ∈ cube alt_corner → alt_corner = corner)

/-
Takes a point p and a tiling T and returns the unique corner in T such that p
is in the cube defined by that corner. This function, when given an int_point x,
is denoted t(x) ∈ T in Brakensiek et al.'s paper

Also want to return a proof that the result is the unique corner in T such that
p is in the cube defined by that corner. For this, rather than simply return a point d,
I return a subtype of point d that for which all elements have exactly the desired property
(i.e. the only element of the type is the corner corresponding to the given point)
-/
noncomputable def point_to_corner {d : ℕ} {T : set (point d)} (h : is_tiling T) (p : point d) :
  { corner : point d // 
      corner ∈ T ∧ p ∈ cube corner ∧
      (∀ alt_corner ∈ T, p ∈ cube alt_corner → alt_corner = corner)
  } :=
begin
  rw is_tiling at h,
  have h' := h p,
  let corner := classical.some h',
  have h' := classical.some_spec h',
  change 
    ∃ (H : corner ∈ T), p ∈ cube corner ∧ 
    (∀ (alt_corner : point d), alt_corner ∈ T → p ∈ cube alt_corner → alt_corner = corner)
    at h',
  rename h'_1 h'',
  simp at h'',
  cases h'' with res_in_T h'',
  use corner,
  have goal : 
    corner ∈ T ∧ p ∈ cube corner ∧
    (∀ alt_corner ∈ T, p ∈ cube alt_corner → alt_corner = corner),
  split, exact res_in_T,
  { cases h'',
    split, exact h''_left,
    exact h''_right,
  },
  exact goal,
end

noncomputable def int_point_to_corner {d : ℕ} {T : set (point d)} (h : is_tiling T) (x : int_point d) :
  { corner : point d // 
      corner ∈ T ∧ int_point_to_point x ∈ cube corner ∧
      (∀ alt_corner ∈ T, int_point_to_point x ∈ cube alt_corner → alt_corner = corner)
  } := point_to_corner h (int_point_to_point x)

--Return type of try_point_to_corner
inductive try_point_to_corner_res {d : ℕ} (T : set (point d)) (p : point d)
  | no_corner : (∀ t ∈ T, p ∉ cube t) → try_point_to_corner_res
  | unique_corner : 
      { corner : point d // 
          corner ∈ T ∧ p ∈ cube corner ∧
          (∀ alt_corner ∈ T, p ∈ cube alt_corner → alt_corner = corner)
      } → try_point_to_corner_res
  | multiple_corners :
      { corners : point d × point d // 
          prod.fst corners ∈ T ∧ p ∈ cube (prod.fst corners) ∧
          prod.snd corners ∈ T ∧ p ∈ cube (prod.snd corners) ∧
          prod.fst corners ≠ prod.snd corners
      } → try_point_to_corner_res

/-
This function takes a set of cube corners T and an arbitrary point p, and tries to return a unique
cube corner in T that contains p. Unlike point_to_corner, this function does not require that T
is a tiling.

When we try to get the corner of a point p in a set of cube corners T, we can either find that there
is no corner in T that contains p, exactly one corner in T that contains p, or multiple corners in T
that contain p. In the first case, we return a proof that no corner in T contains p. In the second case,
we return the unique corner in T that contains p, and through the type assert that no other corner in T
contains p. In the final case, we find two distinct corners in T that contain p, and return them while
asserting through the type that the two corners are distinct, both in T, and both contain p.
-/
noncomputable def try_point_to_corner {d : ℕ} (T : set (point d)) (p : point d) : 
  try_point_to_corner_res T p :=
  begin
    let corners_containing_p_in_T := { corner ∈ T | p ∈ cube corner },
    by_cases corners_containing_p_in_T = ∅,
    { have goal : ∀ t ∈ T, p ∉ cube t :=
        begin
          intros _ t_in_T,
          change {corner ∈ T | p ∈ cube corner} = ∅ at h,
          have h' : ∀ corner ∈ T, p ∉ cube corner :=
            begin
              have empty_h := set.eq_empty_iff_forall_not_mem,
              cases empty_h with empty_h rev_empty_h,
              replace h := empty_h h,
              simp at h,
              exact h,
            end,
          exact h' t t_in_T,
        end,
      exact try_point_to_corner_res.no_corner goal,
    },
    by_cases multiple_corners_contain_p : ∃ corner1 ∈ T, ∃ corner2 ∈ T, 
      corner1 ∈ T ∧ corner2 ∈ T ∧ p ∈ cube corner1 ∧ p ∈ cube corner2 ∧ corner1 ≠ corner2,
    { let corner1 := classical.some multiple_corners_contain_p,
      have multiple_corners_contain_p_2 := classical.some_spec multiple_corners_contain_p,
      change ∃ (H : corner1 ∈ T) (corner2 : point d) (H : corner2 ∈ T), 
        corner1 ∈ T ∧ corner2 ∈ T ∧ p ∈ cube corner1 ∧ p ∈ cube corner2 ∧ corner1 ≠ corner2
        at multiple_corners_contain_p_2,
      let corner1_in_T := classical.some multiple_corners_contain_p_2,
      have multiple_corners_contain_p_3 := classical.some_spec multiple_corners_contain_p_2,
      let corner2 := classical.some multiple_corners_contain_p_3,
      have multiple_corners_contain_p_4 := classical.some_spec multiple_corners_contain_p_3,
      change ∃ (H : corner2 ∈ T),
        corner1 ∈ T ∧ corner2 ∈ T ∧ p ∈ cube corner1 ∧ p ∈ cube corner2 ∧ corner1 ≠ corner2
        at multiple_corners_contain_p_4,
      let corner2_in_T := classical.some multiple_corners_contain_p_4,
      have multiple_corners_contain_p_5 := classical.some_spec multiple_corners_contain_p_4,
      let corners : point d × point d := ⟨corner1, corner2⟩,
      have goal : 
        prod.fst corners ∈ T ∧ p ∈ cube (prod.fst corners) ∧
        prod.snd corners ∈ T ∧ p ∈ cube (prod.snd corners) ∧
        prod.fst corners ≠ prod.snd corners :=
        begin
          cases multiple_corners_contain_p_5 with corner1_in_T multiple_corners_contain_p_5,
          cases multiple_corners_contain_p_5 with corner2_in_T multiple_corners_contain_p_5,
          cases multiple_corners_contain_p_5 with p_in_cube_corner1 multiple_corners_contain_p_5,
          cases multiple_corners_contain_p_5 with p_in_cube_corner2 corner1_neq_corner2,
          split, simp, exact corner1_in_T,
          split, simp, exact p_in_cube_corner1,
          split, simp, exact corner2_in_T,
          split, simp, exact p_in_cube_corner2,
          exact corner1_neq_corner2,
        end,
      let corners' : 
        { corners : point d × point d // 
            prod.fst corners ∈ T ∧ p ∈ cube (prod.fst corners) ∧
            prod.snd corners ∈ T ∧ p ∈ cube (prod.snd corners) ∧
            prod.fst corners ≠ prod.snd corners
        } := ⟨corners, goal⟩,
      exact try_point_to_corner_res.multiple_corners corners',
    },
    rename multiple_corners_contain_p unique_corner_contains_p,
    simp at unique_corner_contains_p,
    change ∀ (t1 : point d), t1 ∈ T → ∀ (t2 : point d), t2 ∈ T → t1 ∈ T → t2 ∈ T → 
      p ∈ cube t1 → p ∈ cube t2 → t1 = t2 at unique_corner_contains_p,
    change corners_containing_p_in_T ≠ ∅ at h,
    rw [set.ne_empty_iff_nonempty, set.nonempty_def] at h,
    let corner_with_p := classical.some h,
    have h' := classical.some_spec h,
    change corner_with_p ∈ corners_containing_p_in_T at h',
    have goal : 
      corner_with_p ∈ T ∧ p ∈ cube corner_with_p ∧
      (∀ alt_corner ∈ T, p ∈ cube alt_corner → alt_corner = corner_with_p) :=
      begin
        change corner_with_p ∈ {corner ∈ T | p ∈ cube corner} at h',
        simp at h',
        cases h' with corner_with_p_in_T p_in_cube_corner_with_p,
        split, exact corner_with_p_in_T,
        split, exact p_in_cube_corner_with_p, 
        intros _ alt_corner_in_T p_in_alt_corner,
        symmetry,
        exact unique_corner_contains_p corner_with_p corner_with_p_in_T alt_corner alt_corner_in_T 
          corner_with_p_in_T alt_corner_in_T p_in_cube_corner_with_p p_in_alt_corner,
      end,
    let corner_with_p' : 
      { corner : point d // 
          corner ∈ T ∧ p ∈ cube corner ∧
          (∀ alt_corner ∈ T, p ∈ cube alt_corner → alt_corner = corner)
      } := ⟨corner_with_p, goal⟩,
    exact try_point_to_corner_res.unique_corner corner_with_p',
  end