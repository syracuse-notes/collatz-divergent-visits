/-
実際の軌道の値と、奇数ステップ数 oddCnt をつなぐ補題(補正項 c_s の評価)。
Lean 4 本体のみ。

(A) 最初の s ステップの奇数値が全て n 以上なら
      2^s · T^s(x) · (3n)^j ≤ 3^j · x · (3n+1)^j      (j = oddCnt s x)
(B) j ≤ (N+1)/2 なら (N+1)^j ≤ 2·N^j
(C) 両者から、j ≤ (3n+1)/2、n ≥ 1 のとき 2^s · T^s(x) ≤ 2 · 3^j · x
-/
namespace L5L

def T (x : Nat) : Nat := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

def Titer : Nat → Nat → Nat
  | 0, x => x
  | s + 1, x => Titer s (T x)

def oddCnt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => (if x % 2 = 1 then 1 else 0) + oddCnt k (T x)

theorem prodA (n : Nat) : ∀ s x, (∀ r, r < s → Titer r x % 2 = 1 → n ≤ Titer r x) →
    2 ^ s * Titer s x * (3 * n) ^ (oddCnt s x) ≤ 3 ^ (oddCnt s x) * x * (3 * n + 1) ^ (oddCnt s x) := by
  intro s
  induction s with
  | zero => intro x _; simp [Titer, oddCnt]
  | succ s ih =>
    intro x hx
    have ih' := ih (T x) (fun r hr hodd => hx (r + 1) (by omega) hodd)
    show 2 ^ (s + 1) * Titer s (T x) * (3 * n) ^ ((if x % 2 = 1 then 1 else 0) + oddCnt s (T x))
      ≤ 3 ^ ((if x % 2 = 1 then 1 else 0) + oddCnt s (T x)) * x
          * (3 * n + 1) ^ ((if x % 2 = 1 then 1 else 0) + oddCnt s (T x))
    generalize hj : oddCnt s (T x) = j at ih'
    generalize hY : Titer s (T x) = Y at ih'
    by_cases hpar : x % 2 = 1
    · rw [if_pos hpar]
      have hxn : n ≤ x := hx 0 (by omega) hpar
      have hT : 2 * T x = 3 * x + 1 := by unfold T; rw [if_neg (by omega)]; omega
      -- 2^(s+1) Y (3n)^(1+j) = 2 * (2^s Y (3n)^j) * (3n)
      have e1 : 2 ^ (s + 1) * Y * (3 * n) ^ (1 + j) = (2 ^ s * Y * (3 * n) ^ j) * (2 * (3 * n)) := by
        rw [Nat.pow_succ, Nat.pow_add, Nat.pow_one]
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have e2 : 3 ^ (1 + j) * x * (3 * n + 1) ^ (1 + j)
          = (3 ^ j * (3 * n + 1) ^ j) * (3 * x * (3 * n + 1)) := by
        rw [Nat.pow_add, Nat.pow_add, Nat.pow_one, Nat.pow_one]
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [e1, e2]
      have step1 : (2 ^ s * Y * (3 * n) ^ j) * (2 * (3 * n))
          ≤ (3 ^ j * T x * (3 * n + 1) ^ j) * (2 * (3 * n)) := Nat.mul_le_mul_right _ ih'
      have e3 : (3 ^ j * T x * (3 * n + 1) ^ j) * (2 * (3 * n))
          = (3 ^ j * (3 * n + 1) ^ j) * ((2 * T x) * (3 * n)) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have key : (2 * T x) * (3 * n) ≤ 3 * x * (3 * n + 1) := by
        rw [hT, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        have : (3 * x) * (3 * n) = 3 * x * (3 * n) := rfl
        have h3 : 3 * n ≤ 3 * x := by omega
        omega
      calc (2 ^ s * Y * (3 * n) ^ j) * (2 * (3 * n))
          ≤ (3 ^ j * T x * (3 * n + 1) ^ j) * (2 * (3 * n)) := step1
        _ = (3 ^ j * (3 * n + 1) ^ j) * ((2 * T x) * (3 * n)) := e3
        _ ≤ (3 ^ j * (3 * n + 1) ^ j) * (3 * x * (3 * n + 1)) := Nat.mul_le_mul_left _ key
    · rw [if_neg hpar, Nat.zero_add]
      have hT : 2 * T x = x := by unfold T; rw [if_pos (by omega)]; omega
      have e1 : 2 ^ (s + 1) * Y * (3 * n) ^ j = 2 * (2 ^ s * Y * (3 * n) ^ j) := by
        rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [e1]
      calc 2 * (2 ^ s * Y * (3 * n) ^ j) ≤ 2 * (3 ^ j * T x * (3 * n + 1) ^ j) :=
            Nat.mul_le_mul_left 2 ih'
        _ = 3 ^ j * (2 * T x) * (3 * n + 1) ^ j := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ = 3 ^ j * x * (3 * n + 1) ^ j := by rw [hT]

theorem powB (N : Nat) : ∀ j r, j + r = N + 1 → (N + 1) ^ j * r ≤ (N + 1) * N ^ j := by
  intro j
  induction j with
  | zero => intro r h; simp at h; rw [h]; simp
  | succ j ih =>
    intro r h
    have IH := ih (r + 1) (by omega)
    -- (N+1)^(j+1) r = (N+1)^j (N+1) r ≤ (N+1)^j N (r+1) ≤ N (N+1) N^j
    have key : (N + 1) * r ≤ N * (r + 1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.mul_comm N r]; omega
    calc (N + 1) ^ (j + 1) * r = (N + 1) ^ j * ((N + 1) * r) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ (N + 1) ^ j * (N * (r + 1)) := Nat.mul_le_mul_left _ key
      _ = N * ((N + 1) ^ j * (r + 1)) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ N * ((N + 1) * N ^ j) := Nat.mul_le_mul_left _ IH
      _ = (N + 1) * N ^ (j + 1) := by
          rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

theorem powB2 (N j : Nat) (hj : 2 * j ≤ N + 1) : (N + 1) ^ j ≤ 2 * N ^ j := by
  have h := powB N j (N + 1 - j) (by omega)
  -- (N+1)^j (N+1-j) ≤ (N+1) N^j and 2(N+1-j) ≥ N+1
  have h2 : (N + 1) ^ j * (N + 1) ≤ (N + 1) ^ j * (2 * (N + 1 - j)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : (N + 1) ^ j * (N + 1) ≤ (2 * N ^ j) * (N + 1) := by
    calc (N + 1) ^ j * (N + 1) ≤ (N + 1) ^ j * (2 * (N + 1 - j)) := h2
      _ = 2 * ((N + 1) ^ j * (N + 1 - j)) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 2 * ((N + 1) * N ^ j) := Nat.mul_le_mul_left 2 h
      _ = (2 * N ^ j) * (N + 1) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-- (C) 補正項の評価:x + c_s(x) ≤ 2x の整数版。 -/
theorem correction (n s x : Nat) (hn : 1 ≤ n)
    (hx : ∀ r, r < s → Titer r x % 2 = 1 → n ≤ Titer r x)
    (hj : 2 * oddCnt s x ≤ 3 * n + 1) :
    2 ^ s * Titer s x ≤ 2 * 3 ^ (oddCnt s x) * x := by
  have hA := prodA n s x hx
  have hB := powB2 (3 * n) (oddCnt s x) hj
  generalize oddCnt s x = j at hA hB
  have hpos : 0 < (3 * n) ^ j := Nat.pow_pos (by omega)
  have : 2 ^ s * Titer s x * (3 * n) ^ j ≤ 2 * 3 ^ j * x * (3 * n) ^ j := by
    calc 2 ^ s * Titer s x * (3 * n) ^ j ≤ 3 ^ j * x * (3 * n + 1) ^ j := hA
      _ ≤ 3 ^ j * x * (2 * (3 * n) ^ j) := Nat.mul_le_mul_left _ hB
      _ = 2 * 3 ^ j * x * (3 * n) ^ j := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_right this hpos

end L5L
