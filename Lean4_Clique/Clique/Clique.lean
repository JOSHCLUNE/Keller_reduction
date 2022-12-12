import Mathlib.Tactic.RunCmd
import Mathlib.Data.List.Basic

namespace Keller

def hasEdge' : List Nat → List Nat → Bool → Bool → Bool
| a::l, b::r, found, n => if a = b then hasEdge' l r found n else
  bif found || (b - a == 2 || a - b == 2) then
    n || hasEdge' l r true true
  else
    hasEdge' l r false true
| a, b, c, d => false

@[implementedBy hasEdge'] def hasEdge : List Nat → List Nat → Bool → Bool → Bool := by
  intro l; induction l with
  | nil => exact fun _ _ _ => false
  | cons a l ih => intro r; induction r with
    | nil => exact fun _ _ => false
    | cons b r => exact
      bif a == b then ih r else fun found =>
        bif found || (b - a == 2 || a - b == 2) then
          fun n => n || ih r true true
        else
          fun _ => ih r false true

inductive Dim2
| _00 | _01 | _02 | _03
| _10 | _11 | _12 | _13
| _20 | _21 | _22 | _23
| _30 | _31 | _32 | _33
deriving DecidableEq, Repr

open Lean Elab Command in
run_cmd do
  let mut s := #[]
  for (a, arr) in #[
    (`_00, #[`_02, `_12, `_20, `_21, `_23, `_32]),
    (`_01, #[`_03, `_13, `_20, `_21, `_22, `_33]),
    (`_02, #[`_21, `_22, `_23]),
    (`_03, #[`_11, `_20, `_22, `_23, `_31]),
    (`_10, #[`_12, `_31, `_33]),
    (`_11, #[`_13, `_23, `_31]),
    (`_12, #[`_20, `_31, `_32, `_33]),
    (`_13, #[`_21, `_33]),
    (`_20, #[`_22, `_32]),
    (`_21, #[`_23, `_33]),
    (`_23, #[`_31]),
    (`_31, #[`_33])] do
    for b in arr do
      s := (s.push (a, b)).push (b, a)
  let stx := s.map fun x => mkIdent $ x.1.updatePrefix default ++ x.2.updatePrefix default
  let stx1 := s.map (mkIdent ·.1)
  let stx2 := s.map (mkIdent ·.2)
  elabCommand (← set_option hygiene false in `(
    def Dim2.keller' : Dim2 → Dim2 → Bool
    $[| $stx1, $stx2 => true]*
    | _, _ => false

    @[implementedBy Dim2.keller'] def Dim2.keller : Dim2 → Dim2 → Bool := by
      intro g1 g2
      induction g1 <;> induction g2
      $[case $stx => exact true]*
      all_goals exact false))

def Dim2.value : Dim2 → List (List Nat)
| _00 => [[0, 2, 1, 1], [1, 1, 3, 2], [2, 3, 0, 3], [3, 0, 2, 0]]
| _02 => [[2, 2, 1, 1], [1, 1, 3, 0], [0, 3, 0, 3], [3, 0, 2, 2]]
| _21 => [[1, 0, 1, 1], [1, 3, 3, 1], [3, 1, 0, 3], [3, 2, 2, 3]]
| _23 => [[1, 1, 1, 3], [1, 3, 2, 3], [3, 0, 0, 1], [3, 2, 3, 1]]
| _12 => [[0, 0, 0, 0], [0, 2, 3, 0], [2, 1, 1, 2], [2, 3, 2, 2]]
| _10 => [[0, 1, 0, 2], [0, 2, 2, 2], [2, 0, 1, 0], [2, 3, 3, 0]]
| _33 => [[1, 2, 1, 0], [3, 3, 0, 2], [0, 0, 2, 3], [2, 1, 3, 1]]
| _31 => [[3, 2, 1, 0], [1, 3, 0, 2], [0, 0, 2, 1], [2, 1, 3, 3]]
| _20 => [[0, 2, 1, 3], [3, 1, 3, 2], [2, 3, 0, 1], [1, 0, 2, 0]]
| _22 => [[2, 2, 1, 3], [3, 1, 3, 0], [0, 3, 0, 1], [1, 0, 2, 2]]
| _01 => [[3, 1, 1, 1], [3, 3, 2, 1], [1, 0, 0, 3], [1, 2, 3, 3]]
| _03 => [[3, 0, 1, 3], [3, 3, 3, 3], [1, 1, 0, 1], [1, 2, 2, 1]]
| _32 => [[0, 0, 1, 2], [0, 3, 3, 2], [2, 1, 0, 0], [2, 2, 2, 0]]
| _30 => [[0, 1, 1, 0], [0, 3, 2, 0], [2, 0, 0, 2], [2, 2, 3, 2]]
| _13 => [[0, 1, 3, 1], [2, 0, 2, 3], [1, 2, 1, 2], [3, 3, 0, 0]]
| _11 => [[0, 1, 3, 3], [2, 0, 2, 1], [3, 2, 1, 2], [1, 3, 0, 0]]

theorem Dim2.is_ok (g) : (Dim2.value g).Pairwise (fun a b => hasEdge a b false false) := by
  cases g <;> decide

def dim4 : List (Dim2 × Dim2) := open Dim2 in
[(_01, _00), (_03, _20), (_10, _12), (_10, _32),
 (_11, _20), (_12, _12), (_12, _32), (_13, _00),
 (_21, _00), (_23, _20), (_31, _02), (_31, _21),
 (_31, _23), (_33, _01), (_33, _03), (_33, _22)]

def Dim2.hasEdge (x y : Dim2) (found n : Bool) : Bool :=
  x.value.all fun x => y.value.all fun y => Keller.hasEdge x y found n

def Dim2.ok₂ : Dim2 × Dim2 → Dim2 × Dim2 → Bool
| (a1, a2), (b1, b2) =>
  if a1 = b1 then a2.hasEdge b2 false false
  else if a2 = b2 then a1.hasEdge b1 false false
  else
    let k1 := a1.keller b1
    let k2 := a2.keller b2
    let x1 := a1.hasEdge b1 (!k1) true
    let x2 := a2.hasEdge b2 (!k2) true
    x1 && x2 && (k1 || k2)

set_option profiler true in -- takes about 8 seconds
theorem dim4_ok₂ : dim4.Pairwise (Dim2.ok₂ · ·) := by decide

def dim8 : List (List Nat) :=
  dim4.bind (fun (a, b) => (a.value.bind fun a => (b.value.map fun b => a ++ b)))

def isClique (l : List (List Nat)) : Bool :=
  l.all fun a => l.all fun b => a == b || hasEdge a b false false

#eval isClique dim8 -- true
