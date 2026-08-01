import Mathlib.Data.Nat.Basic


namespace ToBits


----------------------------------------------------------------------------------------------------
-- Conversion to and from binary representation (least-significant-bit first)
----------------------------------------------------------------------------------------------------


def toBits : Nat → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: toBits ((n + 1) / 2)

def fromBits : List Bool → Nat
  | [] => 0
  | (true :: bs) => 1 + 2 * fromBits bs
  | (false :: bs) => 2 * fromBits bs


----------------------------------------------------------------------------------------------------
-- Concrete Examples
----------------------------------------------------------------------------------------------------


#eval toBits 0
-- Output: []

#eval fromBits []
-- Output: 0

#eval toBits 4
-- Output: [false, false, true]

#eval fromBits [false, true, false, true]
-- Output: 10

#eval toBits 42
-- Output: [false, true, false, true, false, true]

#eval fromBits (toBits 42)
-- Output: 42

#eval toBits (fromBits [true, true, false, true])
-- Output: [true, true, false, true]


----------------------------------------------------------------------------------------------------
-- Formal Verification
----------------------------------------------------------------------------------------------------


theorem fromBits_toBits : (n : Nat) → fromBits (toBits n) = n
  | 0 => by
    rw [toBits, fromBits]
  | n + 1 => by
    rw [toBits]
    have ih := fromBits_toBits ((n + 1) / 2)
    have h_mod : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by omega
    rcases h_mod with hm0 | hm1
    · have hb : ((n + 1) % 2 == 1) = false := by simp [hm0]
      rw [hb]
      unfold fromBits
      rw [ih]
      omega
    · have hb : ((n + 1) % 2 == 1) = true := by simp [hm1]
      rw [hb]
      unfold fromBits
      rw [ih]
      omega


----------------------------------------------------------------------------------------------------
-- Other implementations
----------------------------------------------------------------------------------------------------


def toBits2 (n : Nat) : List Bool :=
  go n []
where
  go : Nat → List Bool → List Bool
    | 0, acc => acc.reverse
    | n + 1, acc => go (n / 2) ((n % 2 == 1) :: acc)


def toBits3 (n : Nat) : List Bool :=
  if n = 0 then []
  else (n % 2 == 1) :: toBits2 (n / 2)


end ToBits
