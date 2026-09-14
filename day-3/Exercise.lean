import Mathlib.Tactic.Ring

/- Mortal Cells:
Each cell produces a new cell every day starting with the 1st day of its life,
and it dies after 2 days. We start with 1 newborn cell. Each newborn cell has 0 days.
How many cells are alive after n days?
Example (each value represents the number of days of an alive cell):
0.                0              => 1 cell alive after 0 days
1.                1              => 1 cell alive after 1 day
2.        0               2      => 2 cells alive after 2 days
3.        1               0      => 2 cells alive after 3 days
4.    0       2           1      => 3 cells alive after 4 days
5.    1       0        0     2   => 4 cells alive after 5 days
6.  0   2     1        1     0   => 5 cells alive after 6 days
7.  1   0   0   2    0   2   1   => 7 cells alive after 7 days
-/

/- The answer to the above question can be expressed with two
recurrent sequences.-/

def x (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | (m + 5) => x (m + 4) + x m

def y (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | (m + 3) => y (m + 1) + y m

#eval List.range 20 |> List.map y
#eval List.range 20 |> List.map x

/- Let's prove that the two recurrent sequences are equal. -/

theorem y_eq_x (n : ℕ) : y n = x n := by
    sorry
