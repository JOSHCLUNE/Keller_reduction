import data.real.basic
import data.int.order
import order.well_founded_set
import data.int.parity
import tactic
import init.data.int.order
import combinatorics.simple_graph.basic
import data.fintype.card
import data.nat.basic

--Types and helper functions for points in d dimensional space
def point (d : ℕ) : Type := vector ℝ d
def int_point (d : ℕ) : Type := vector ℤ d
def int_point_to_point {d : ℕ} (p : int_point d) : point d :=
  let fn : fin d → ℝ := λ x : fin d, ↑(vector.nth p x) in
  vector.of_fn fn

--Misc helper functions
lemma lt_of_le_add_neg {a : ℝ} {b : ℝ} {c : ℝ} (h : c < 0) : a ≤ b + c → a < b :=
  by {intro h', linarith}

lemma floor_mono_eq {a : ℝ} {b : ℝ} (h : a = b) : int.floor(a) = int.floor(b) :=
begin
  have a_le_b : a ≤ b := le_of_eq h,
  symmetry' at h,
  have b_le_a : b ≤ a := le_of_eq h,
  have floor_a_le_floor_b : int.floor(a) ≤ int.floor(b) := int.floor_mono a_le_b,
  have floor_b_le_floor_a : int.floor(b) ≤ int.floor(a) := int.floor_mono b_le_a,
  linarith,
end

lemma ceil_mono_eq {a : ℝ} {b : ℝ} (h : a = b) : int.ceil(a) = int.ceil(b) :=
begin
  have a_le_b : a ≤ b := le_of_eq h,
  symmetry' at h,
  have b_le_a : b ≤ a := le_of_eq h,
  have ceil_a_le_ceil_b := int.ceil_mono a_le_b,
  have ceil_b_le_ceil_a := int.ceil_mono b_le_a,
  linarith,
end

lemma coe_nat_abs_ge_zero (z : ℤ) : (z.nat_abs : ℤ) ≥ 0 :=
begin
  have h : z.nat_abs ≥ 0,
  by_cases z = 0,
  rw h,
  rw int.nat_abs_zero,
  linarith,
  have h' := int.nat_abs_pos_of_ne_zero h,
  linarith,
  assumption_mod_cast,
end

lemma eq_of_le_and_ge {a : ℤ} {b : ℤ} (a_le_b : a ≤ b) (b_le_a : b ≤ a) : a = b :=
begin
  replace a_le_b := eq_or_lt_of_le a_le_b,
  replace b_le_a := eq_or_lt_of_le b_le_a,
  cases a_le_b,
  assumption,
  cases b_le_a,
  symmetry,
  assumption,
  linarith,
end

lemma eq_or_lt_or_gt (a : ℤ) (b : ℤ) : a = b ∨ a < b ∨ a > b :=
begin
  by_cases a_le_b : a ≤ b,
  by_cases a_eq_b : a = b, left, exact a_eq_b,
  right, left, exact lt_of_le_of_ne a_le_b a_eq_b,
  right, right, linarith,
end

lemma real_eq_or_lt_or_gt (a : ℝ) (b : ℝ) : a = b ∨ a < b ∨ a > b :=
begin
  by_cases a_le_b : a ≤ b,
  by_cases a_eq_b : a = b, left, exact a_eq_b,
  right, left, exact lt_of_le_of_ne a_le_b a_eq_b,
  right, right, linarith,
end

lemma nat_eq_or_lt_or_gt (a : ℕ) (b : ℕ) : a = b ∨ a < b ∨ a > b :=
begin
  by_cases a_le_b : a ≤ b,
by_cases a_eq_b : a = b, left, exact a_eq_b,
right, left, exact lt_of_le_of_ne a_le_b a_eq_b,
right, right, linarith,
end

lemma floor_val {x : ℝ} {a : ℤ} (h : ↑a ≤ x) (h2 : x < ↑a + 1) : int.floor(x) = a :=
begin
  have floor_mono_h := int.floor_mono h,
  have floor_a_eq_a : int.floor(a : ℝ) = a := int.floor_coe a,
  rw floor_a_eq_a at floor_mono_h,
  have floor_x_le_x := int.floor_le x,
  have floor_x_lt_a_add_one : ((int.floor(x)) : ℝ) < ↑a + 1 := by linarith,
  replace floor_x_lt_a_add_one : ⌊x⌋ < a + 1 := by assumption_mod_cast,
  linarith,
end

lemma ceil_val {x : ℝ} {a : ℤ} (h : ↑a - 1 < x) (h2 : x ≤ ↑a) : int.ceil(x) = a :=
begin
  have ceil_mono_h2 := int.ceil_mono h2,
  have ceil_a_eq_a : int.ceil(a : ℝ) = a := int.ceil_coe a,
  rw ceil_a_eq_a at ceil_mono_h2,
  have x_le_ceil_x := int.le_ceil x,
  have coe_a_lt_ceil_x_add_one : ↑a < ↑(int.ceil x) + (1 : ℝ) := by linarith,
  have a_lt_ceil_x_add_one : a < (int.ceil x) + 1 := by assumption_mod_cast,
  have a_le_ceil_x := int.le_of_lt_add_one a_lt_ceil_x_add_one,
  linarith,
end

lemma ceil_one : int.ceil((1 : ℝ)) = 1 :=
begin
  have one_sub_one_lt_one : 1 - 1 < 1 := by linarith,
  have coe_one_sub_one_lt_one : ↑(1 : ℤ) - 1 < (1 : ℝ) := by assumption_mod_cast,
  have one_le_one : 1 ≤ 1 := by refl,
  have coe_one_le_one : (1 : ℝ) ≤ ↑(1 : ℤ) := by assumption_mod_cast,
  exact ceil_val coe_one_sub_one_lt_one coe_one_le_one,
end

lemma mul_div_two_of_even {a : ℤ} (a_is_even : even a) : 2 * (a / 2) = a :=
begin
  rw even_iff_two_dvd at a_is_even,
  have two_ne_zero : (2 : ℤ) ≠ 0 := by linarith,
  have two_times_a_eq_a_times_two : 2 * a = a * 2 := by rw mul_comm,
  symmetry,
  have almost_goal := int.eq_mul_div_of_mul_eq_mul_of_dvd_left two_ne_zero a_is_even two_times_a_eq_a_times_two,
  linarith,
end

lemma mul_div_of_ne_zero {b : ℝ} (a : ℝ) (b_ne_zero : b ≠ 0) : b * (a / b) = a :=
begin
  have h : b = 0 → a = 0 := by {intro b_eq_zero, exfalso, exact b_ne_zero b_eq_zero},
  exact mul_div_cancel_of_imp' h,
end

lemma lt_le_trans {a : ℝ} {b : ℝ} {c : ℝ} (h : a < b) (h' : b ≤ c) : a < c := by linarith
lemma le_lt_trans {a : ℝ} {b : ℝ} {c : ℝ} (h : a ≤ b) (h' : b < c) : a < c := by linarith

lemma nat_le_of_lt_add_one {a : ℕ} {b : ℕ} (h : a < b + 1) : a ≤ b := by linarith

--Vector helper functions
def zero_vector {d : ℕ} : point d := vector.of_fn (λ j, 0)
def int_zero_vector {d : ℕ} : int_point d := vector.of_fn (λ j, 0)
def unit_basis_vector {d : ℕ} (i : fin d) : point d := vector.of_fn (λ j, if(i = j) then 1 else 0)
def neg_unit_basis_vector {d : ℕ} (i : fin d) : point d := vector.of_fn (λ j, if(i=j) then -1 else 0)
def int_unit_basis_vector {d : ℕ} (i : fin d) : int_point d := vector.of_fn (λ j, if(i = j) then 1 else 0)
def int_neg_unit_basis_vector {d : ℕ} (i : fin d) : int_point d := vector.of_fn (λ j, if(i=j) then -1 else 0)

def add_vectors {d : ℕ} (v1 : point d) (v2 : point d) := vector.of_fn(λ j, v1.nth j + v2.nth j)
def add_int_vectors {d : ℕ} (v1 : int_point d) (v2 : int_point d) := vector.of_fn(λ j, v1.nth j + v2.nth j)

lemma add_same_vector {d : ℕ} {v1 : point d} {v2 : point d} (v3 : point d) (h : v1 = v2) : add_vectors v1 v3 = add_vectors v2 v3 :=
begin
  rw [add_vectors, add_vectors],
  apply vector.ext,
  intro i,
  simp,
  rw h,
end

lemma add_vectors_comm {d : ℕ} (v1 : point d) (v2 : point d) : add_vectors v1 v2 = add_vectors v2 v1 :=
begin
  rw [add_vectors, add_vectors],
  apply vector.ext,
  intro i,
  simp only [vector.nth_of_fn],
  rw add_comm,
end

lemma add_int_vectors_comm {d : ℕ} (v1 : int_point d) (v2 : int_point d) : add_int_vectors v1 v2 = add_int_vectors v2 v1 :=
begin
  rw [add_int_vectors, add_int_vectors],
  apply vector.ext,
  intro i,
  simp only [vector.nth_of_fn],
  rw add_comm,
end

lemma add_vectors_assoc {d : ℕ} (v1 : point d) (v2 : point d) (v3 : point d) : 
  add_vectors (add_vectors v1 v2) v3 = add_vectors v1 (add_vectors v2 v3) :=
begin
  rw [add_vectors, add_vectors, add_vectors, add_vectors],
  apply vector.ext,
  intro i,
  simp only [vector.nth_of_fn],
  rw add_assoc,
end

lemma add_int_vectors_assoc {d : ℕ} (v1 : int_point d) (v2 : int_point d) (v3 : int_point d) :
  add_int_vectors (add_int_vectors v1 v2) v3 = add_int_vectors v1 (add_int_vectors v2 v3) :=
begin
  rw [add_int_vectors, add_int_vectors, add_int_vectors, add_int_vectors],
  apply vector.ext,
  intro i,
  simp only [vector.nth_of_fn],
  rw add_assoc,
end

lemma remove_same_vector {d : ℕ} {v1 : point d} {v2 : point d} {v3 : point d} (h : add_vectors v1 v3 = add_vectors v2 v3) : v1 = v2 :=
begin
  apply vector.ext,
  intro i,
  have h' : (add_vectors v1 v3).nth i = (add_vectors v2 v3).nth i := by rw h,
  rw [add_vectors, add_vectors] at h',
  simp only [vector.nth_of_fn] at h',
  linarith,
end

lemma unit_basis_vector_add_neg_unit_basis_vector_eq_zero {d : ℕ} (i : fin d) : 
  add_vectors (unit_basis_vector i) (neg_unit_basis_vector i) = zero_vector :=
begin
  apply vector.ext,
  intro j,
  rw [neg_unit_basis_vector, unit_basis_vector, add_vectors, zero_vector],
  simp only [vector.nth_of_fn],
  by_cases i_eq_j : i = j, {rw i_eq_j, simp only [if_true, eq_self_iff_true, add_right_neg],},
  rw if_neg i_eq_j,
  simp only [ite_eq_right_iff, zero_add, neg_eq_zero, one_ne_zero],
  exact i_eq_j,
end

lemma add_zero_vector {d : ℕ} (v : point d) : add_vectors v zero_vector = v :=
begin
  rw [zero_vector, add_vectors],
  simp only [add_zero, vector.of_fn_nth, vector.nth_of_fn],
end

lemma zero_vector_add {d : ℕ} (v : point d) : add_vectors zero_vector v = v :=
begin
  rw [zero_vector, add_vectors],
  simp only [zero_add, vector.of_fn_nth, vector.nth_of_fn],
end

def scaled_basis_vector {d : ℕ} (scalar : ℝ) (i : fin d) : point d := vector.of_fn (λ j, if(i = j) then scalar else 0)
def int_scaled_basis_vector {d : ℕ} (scalar : ℤ) (i : fin d) : int_point d := vector.of_fn (λ j, if(i = j) then scalar else 0)
def double_int_vector {d : ℕ} (x : int_point d) : int_point d := vector.of_fn (λ j : fin d, 2 * (x.nth j))

--Mod one helper functions

/-
Note: There's no point in trying to build a computational version of eq_mod_one because it would require real equality which
isn't computable
-/
def eq_mod_one (a : ℝ) (b : ℝ) : Prop := ∃ a_floor : ℤ, ∃ b_floor : ℤ, ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ a = a_floor + y ∧ b = b_floor + y
def ne_mod_one (a : ℝ) (b : ℝ) : Prop := ¬(eq_mod_one a b)

lemma eq_mod_one_reflexive (a : ℝ) : eq_mod_one a a :=
begin
  rw eq_mod_one,
  have floor_le_fact := int.floor_le a,
  have lt_floor_add_one_fact := int.lt_floor_add_one a,
  use [int.floor(a), int.floor(a), a - ↑(int.floor(a))],
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩,
end

lemma eq_mod_one_symmetric {a : ℝ} {b : ℝ} (h : eq_mod_one a b) : eq_mod_one b a :=
begin
  rw eq_mod_one,
  rw eq_mod_one at h,
  rcases h with ⟨a_floor, b_floor, y, zero_le_y, y_lt_one, a_eq_y_mod_one, b_eq_y_mod_one⟩,
  use [b_floor, a_floor, y],
  exact ⟨zero_le_y, y_lt_one, b_eq_y_mod_one, a_eq_y_mod_one⟩,
end

lemma eq_mod_one_transitive {a : ℝ} {b : ℝ} {c : ℝ} (h1 : eq_mod_one a b) (h2 : eq_mod_one b c) : eq_mod_one a c :=
begin
  rw eq_mod_one at h1,
  rcases h1 with ⟨a_floor, b_floor, y, zero_le_y, y_lt_one, a_eq_y_mod_one, b_eq_y_mod_one⟩,
  rcases h2 with ⟨b_floor', c_floor, y', zero_le_y', y'_lt_one, b_eq_y', c_eq_y_mod_one⟩,
  have b_floor_eq_b_floor' : b_floor = b_floor' :=
    begin
      have b_floor_add_y_eq_b_floor'_add_y' : y + ↑b_floor = y' + ↑b_floor' := by linarith,
      have floor_mono_fact := floor_mono_eq b_floor_add_y_eq_b_floor'_add_y',
      have floor_add_int_fact1 := int.floor_add_int y b_floor,
      have floor_add_int_fact2 := int.floor_add_int y' b_floor',
      rw [floor_add_int_fact1, floor_add_int_fact2] at floor_mono_fact,

      replace zero_le_y : ↑(0 : ℤ) ≤ y := by assumption_mod_cast,
      replace y_lt_one : y < ↑(0 : ℤ) + 1 :=
        begin
          have coe_goal : y < 0 + 1 := by linarith,
          assumption_mod_cast,
        end,
      have floor_y_eq_zero := floor_val zero_le_y y_lt_one,
      
      replace zero_le_y' : ↑(0 : ℤ) ≤ y' := by assumption_mod_cast,
      replace y'_lt_one : y' < ↑(0 : ℤ) + 1 :=
        begin
          have coe_goal : y' < 0 + 1 := by linarith,
          assumption_mod_cast,
        end,
      have floor_y'_eq_zero := floor_val zero_le_y' y'_lt_one,

      rw [floor_y_eq_zero, floor_y'_eq_zero] at floor_mono_fact,
      simp at floor_mono_fact,
      exact floor_mono_fact,
    end,
  have y_eq_y' : y = y' :=
    begin
      have b_defs : ↑b_floor + y = ↑b_floor' + y' := by linarith,
      rw b_floor_eq_b_floor' at b_defs,
      linarith,
    end,
  rw ← y_eq_y' at c_eq_y_mod_one,
  rw eq_mod_one,
  use [a_floor, c_floor, y],
  exact ⟨zero_le_y, y_lt_one, a_eq_y_mod_one, c_eq_y_mod_one⟩,
end

lemma add_mod_eq_add_mod_right {a : ℝ} {b : ℝ} {c : ℝ} (h1 : eq_mod_one a b) : eq_mod_one (a + c) (b + c) :=
begin
  rw eq_mod_one at h1,
  rcases h1 with ⟨a_floor, b_floor, y, zero_le_y, y_lt_one, a_val, b_val⟩,
  rw eq_mod_one,
  have floor_le_fact := int.floor_le (y + c),
  have lt_floor_add_one_fact := int.lt_floor_add_one (y + c),
  have floor_c_le_c := int.floor_le c,
  have c_lt_floor_c_add_one := int.lt_floor_add_one c,
  by_cases y_add_c_remainder_lt_one : y + c - ↑(int.floor c) < 1,
  { use [a_floor + int.floor(c), b_floor + int.floor(c), y + c - ↑(int.floor c)],
    exact ⟨by linarith, by linarith, by {simp, linarith,}, by {simp, linarith,}⟩, 
  },
  use [a_floor + int.floor(c) + 1, b_floor + int.floor(c) + 1, y + c - ↑(int.floor c) - 1],
  exact ⟨by linarith, by linarith, by {simp, linarith}, by {simp, linarith,}⟩,
end

lemma subst_summand_eq_mod_one {a : ℝ} {b : ℝ} {c : ℝ} {d : ℝ} : eq_mod_one a d → eq_mod_one (a + b) c → eq_mod_one (d + b) c :=
begin
  intros a_eq_d_mod_one,
  rcases a_eq_d_mod_one with ⟨a_floor, d_floor, y, zero_le_y, y_lt_one, a_def, d_def⟩,
  rintro ⟨a_add_b_floor, c_floor, y', zero_le_y', y'_lt_one, a_add_b_def, c_def⟩,
  rw eq_mod_one,
  use [a_add_b_floor - a_floor + d_floor, c_floor, y', zero_le_y', y'_lt_one, by {simp only [int.cast_add, int.cast_sub], linarith}, c_def],
end

lemma eq_mod_one_int_add {a : ℝ} {b : ℤ} {c : ℝ} : eq_mod_one a c → eq_mod_one (a + ↑b) c :=
begin
  rw [eq_mod_one, eq_mod_one],
  rintro ⟨a_floor, c_floor, y, zero_le_y, y_lt_one, a_eq_a_floor_add_y, c_eq_c_floor_add_y⟩,
  use [a_floor + b, c_floor, y, zero_le_y, y_lt_one],
  split,
  { rw a_eq_a_floor_add_y,
    finish,
  },
  exact c_eq_c_floor_add_y,
end

lemma eq_mod_one_int_sub {a : ℝ} {b : ℤ} {c : ℝ} : eq_mod_one a c → eq_mod_one (a - ↑b) c :=
begin
  have b_id : -↑b = (↑(-b) : ℝ) := by finish,
  rw [sub_eq_add_neg a ↑b, b_id],
  exact eq_mod_one_int_add,
end

--Helpers for finsets
lemma sorted_list_to_finset_lemma :
  ∀ l : list ℝ, list.sorted (≤) l → l.nodup → finset.sort (≤) l.to_finset = l :=
begin
  intros l l_sorted l_nodup,
  cases l with l_hd l_tl,
  { simp only [list.to_finset_nil],
    have emptyset_to_list_eq_nil : finset.to_list ∅ = (list.nil : list ℝ) := finset.to_list_empty,
    have emptyset_sort_perm_emptyset_to_list := finset.sort_perm_to_list has_le.le (∅ : finset ℝ),
    rw finset.to_list_empty at emptyset_sort_perm_emptyset_to_list,
    exact list.perm.eq_nil emptyset_sort_perm_emptyset_to_list,
  },
  have finset_sort_output_nodup : (finset.sort (≤) (l_hd :: l_tl).to_finset).nodup := 
    finset.sort_nodup (≤) (l_hd :: l_tl).to_finset,
  have perm_goal : finset.sort (≤) (l_hd :: l_tl).to_finset ~ l_hd :: l_tl :=
    begin
      rw list.perm_ext finset_sort_output_nodup l_nodup,
      intro a,
      rw [← list.to_finset_eq l_nodup],
      simp only [finset.mem_sort, multiset.mem_coe, finset.mem_mk],
    end,
  have finset_to_list_ordered_output_sorted := finset.sort_sorted has_le.le ((l_hd :: l_tl).to_finset),
  exact list.eq_of_perm_of_sorted perm_goal finset_to_list_ordered_output_sorted l_sorted,
end