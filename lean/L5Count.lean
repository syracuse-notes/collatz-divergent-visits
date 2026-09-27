/-
L5 の数え上げ部分(Terras 型の個数評価)を、確率を使わず整数だけで形式化する。
Lean 4 本体のみ、Mathlib なし。

T(x) = x/2 (偶数)、(3x+1)/2 (奇数)。oddCnt k x = 最初の k ステップの奇数ステップ数。
等差数列 a, a+d, a+2d, …(d 奇数)の長さ 2^k·m の区間で数える。

(1) Doob 型(Climb 集合用):
    #{x : ある s ≤ k で den·2^s ≤ num·3^(oddCnt s x)} · den ≤ m · 2^k · num
(2) Chernoff 型(Stay 集合用、重み u ≥ w > 0):
    #{x : t ≤ oddCnt k x} · u^t · w^k ≤ m · (u+w)^k · w^t
-/
namespace L5C

open Classical

noncomputable def ind (P : Prop) : Nat := if P then 1 else 0
theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by unfold ind; simp [h]
theorem ind_neg {P : Prop} (h : ¬P) : ind P = 0 := by unfold ind; simp [h]
theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_pos h]; exact Nat.le_refl 1
  · rw [ind_neg h]; exact Nat.zero_le 1

noncomputable def cnt (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt P n + ind (P n)

theorem cnt_succ (P : Nat → Prop) (n : Nat) : cnt P (n + 1) = cnt P n + ind (P n) := rfl

theorem cnt_le (P : Nat → Prop) (n : Nat) : cnt P n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [cnt_succ]; have := ind_le_one (P n); omega

theorem cnt_congr {P Q : Nat → Prop} (n : Nat) (h : ∀ i, i < n → (P i ↔ Q i)) :
    cnt P n = cnt Q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt_succ, cnt_succ, ih (fun i hi => h i (by omega))]
    by_cases hp : P n
    · rw [ind_pos hp, ind_pos ((h n (by omega)).mp hp)]
    · rw [ind_neg hp, ind_neg (fun hq => hp ((h n (by omega)).mpr hq))]

theorem cnt_false (n : Nat) : cnt (fun _ => False) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ, ih, ind_neg (fun h => h)]

/-- 等差数列の添字を偶奇で分ける。 -/
theorem cnt_split2 (P : Nat → Prop) (a d n : Nat) :
    cnt (fun i => P (a + d * i)) (2 * n) =
      cnt (fun i => P (a + 2 * d * i)) n + cnt (fun i => P ((a + d) + 2 * d * i)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e, cnt_succ, cnt_succ, ih, cnt_succ, cnt_succ]
    have e1 : a + d * (2 * n) = a + 2 * d * n := by
      rw [Nat.mul_left_comm, Nat.mul_assoc]
    have e2 : a + d * (2 * n + 1) = (a + d) + 2 * d * n := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_assoc]; omega
    rw [e1, e2]; omega

def T (x : Nat) : Nat := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

def oddCnt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => (if x % 2 = 1 then 1 else 0) + oddCnt k (T x)

/-- 偶数から始まる差 2d の数列:全て偶数で、T で (a/2, d) の数列に移る。 -/
theorem even_sub (a d i : Nat) (ha : a % 2 = 0) :
    (a + 2 * d * i) % 2 = 0 ∧ T (a + 2 * d * i) = a / 2 + d * i := by
  have hm : (a + 2 * d * i) % 2 = 0 := by
    rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]; exact ha
  refine ⟨hm, ?_⟩
  unfold T; rw [if_pos hm, Nat.mul_assoc, Nat.add_mul_div_left _ _ (by decide)]

/-- 奇数から始まる差 2d の数列:全て奇数で、T で ((3b+1)/2, 3d) の数列に移る。 -/
theorem odd_sub (b d i : Nat) (hb : b % 2 = 1) :
    (b + 2 * d * i) % 2 = 1 ∧ T (b + 2 * d * i) = (3 * b + 1) / 2 + 3 * d * i := by
  have hm : (b + 2 * d * i) % 2 = 1 := by
    rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]; exact hb
  refine ⟨hm, ?_⟩
  unfold T
  rw [if_neg (by omega)]
  have e : 3 * (b + 2 * d * i) + 1 = (3 * b + 1) + 2 * (3 * d * i) := by
    rw [Nat.mul_add]
    have : 3 * (2 * d * i) = 2 * (3 * d * i) := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [this]; omega
  rw [e, Nat.add_mul_div_left _ _ (by decide)]

theorem oddCnt_even (k x : Nat) (h : x % 2 = 0) : oddCnt (k + 1) x = oddCnt k (T x) := by
  show (if x % 2 = 1 then 1 else 0) + oddCnt k (T x) = oddCnt k (T x)
  rw [if_neg (by omega), Nat.zero_add]

theorem oddCnt_odd (k x : Nat) (h : x % 2 = 1) : oddCnt (k + 1) x = 1 + oddCnt k (T x) := by
  show (if x % 2 = 1 then 1 else 0) + oddCnt k (T x) = 1 + oddCnt k (T x)
  rw [if_pos h]

/-- 長さ 2·n の数列を偶数の部分と奇数の部分に分けて数える一般形。 -/
theorem split_by_parity (P : Nat → Prop) (a d n : Nat) (hd : d % 2 = 1) :
    ∃ e o : Nat, e % 2 = 0 ∧ o % 2 = 1 ∧
      cnt (fun i => P (a + d * i)) (2 * n) =
        cnt (fun i => P (e + 2 * d * i)) n + cnt (fun i => P (o + 2 * d * i)) n := by
  rw [cnt_split2]
  by_cases ha : a % 2 = 0
  · exact ⟨a, a + d, ha, by omega, rfl⟩
  · exact ⟨a + d, a, by omega, by omega, Nat.add_comm _ _⟩

/-! ### 算術の補題 -/

theorem arith0 (CE CO R M u w : Nat) (huw : w ≤ u) (IE : CE * R ≤ M) (IO : CO * R ≤ M) :
    (CE + CO) * (R * w) ≤ M * (u + w) := by
  have h1 : CE * (R * w) ≤ M * w := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right w IE
  have h2 : CO * (R * w) ≤ M * w := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right w IO
  have h3 : M * w ≤ M * u := Nat.mul_le_mul_left M huw
  rw [Nat.add_mul, Nat.mul_add]
  omega

theorem arith1 (CE CO P Q R M u w : Nat) (IE : CE * (u * P * R) ≤ M * (w * Q))
    (IO : CO * (P * R) ≤ M * Q) :
    (CE + CO) * (u * P * (R * w)) ≤ M * (u + w) * (w * Q) := by
  have h1 : CE * (u * P * (R * w)) ≤ M * (w * Q) * w := by
    have := Nat.mul_le_mul_right w IE
    have e : CE * (u * P * (R * w)) = CE * (u * P * R) * w := by
      simp only [Nat.mul_assoc]
    rw [e]; exact this
  have h2 : CO * (u * P * (R * w)) ≤ M * Q * (u * w) := by
    have := Nat.mul_le_mul_right (u * w) IO
    have e : CO * (u * P * (R * w)) = CO * (P * R) * (u * w) := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [e]; exact this
  have e3 : M * (u + w) * (w * Q) = M * (w * Q) * w + M * Q * (u * w) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  rw [e3, Nat.add_mul]
  exact Nat.add_le_add h1 h2

/-! ### (2) Chernoff 型 -/

theorem chernoff (u w : Nat) (huw : w ≤ u) :
    ∀ k t a d m, d % 2 = 1 →
      cnt (fun i => t ≤ oddCnt k (a + d * i)) (2 ^ k * m) * (u ^ t * w ^ k)
        ≤ m * (u + w) ^ k * w ^ t := by
  intro k
  induction k with
  | zero =>
    intro t a d m _
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one]
    by_cases ht : t = 0
    · subst ht; simp only [Nat.pow_zero, Nat.mul_one]; exact cnt_le _ _
    · have : cnt (fun i => t ≤ oddCnt 0 (a + d * i)) m = 0 := by
        rw [cnt_congr m (Q := fun _ => False) (fun i _ => by
          show t ≤ 0 ↔ False; exact ⟨fun h => by omega, fun h => h.elim⟩)]
        exact cnt_false m
      rw [this, Nat.zero_mul]; exact Nat.zero_le _
  | succ k ih =>
    intro t a d m hd
    have hlen : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [hlen]
    obtain ⟨e, o, he, ho, hs⟩ :=
      split_by_parity (fun x => t ≤ oddCnt (k + 1) x) a d (2 ^ k * m) hd
    rw [hs]
    have hE : cnt (fun i => t ≤ oddCnt (k + 1) (e + 2 * d * i)) (2 ^ k * m)
        = cnt (fun i => t ≤ oddCnt k (e / 2 + d * i)) (2 ^ k * m) := by
      apply cnt_congr; intro i _
      obtain ⟨hm, hT⟩ := even_sub e d i he
      rw [oddCnt_even k _ hm, hT]
    have hO : cnt (fun i => t ≤ oddCnt (k + 1) (o + 2 * d * i)) (2 ^ k * m)
        = cnt (fun i => t - 1 ≤ oddCnt k ((3 * o + 1) / 2 + 3 * d * i)) (2 ^ k * m) := by
      apply cnt_congr; intro i _
      obtain ⟨hm, hT⟩ := odd_sub o d i ho
      rw [oddCnt_odd k _ hm, hT]; omega
    rw [hE, hO]
    have h3d : (3 * d) % 2 = 1 := by omega
    have IE := ih t (e / 2) d m hd
    have IO := ih (t - 1) ((3 * o + 1) / 2) (3 * d) m h3d
    generalize cnt (fun i => t ≤ oddCnt k (e / 2 + d * i)) (2 ^ k * m) = CE at IE ⊢
    generalize cnt (fun i => t - 1 ≤ oddCnt k ((3 * o + 1) / 2 + 3 * d * i)) (2 ^ k * m) = CO at IO ⊢
    rw [Nat.pow_succ w k, Nat.pow_succ (u + w) k]
    by_cases ht : t = 0
    · subst ht
      simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.zero_sub] at IE IO ⊢
      have h := arith0 CE CO (w ^ k) (m * (u + w) ^ k) u w huw IE IO
      simpa only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [Nat.add_sub_cancel] at IO
      rw [Nat.pow_succ u t', Nat.pow_succ w t'] at IE ⊢
      have IE' : CE * (u * u ^ t' * w ^ k) ≤ m * (u + w) ^ k * (w * w ^ t') := by
        simpa only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using IE
      have h := arith1 CE CO (u ^ t') (w ^ t') (w ^ k) (m * (u + w) ^ k) u w IE' IO
      simpa only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h

/-! ### (1) Doob 型 -/

def climb (k num den x : Nat) : Prop := ∃ s, s ≤ k ∧ den * 2 ^ s ≤ num * 3 ^ (oddCnt s x)

theorem climb_zero (num den x : Nat) : climb 0 num den x ↔ den ≤ num := by
  constructor
  · rintro ⟨s, hs, h⟩
    have : s = 0 := by omega
    subst this; simpa [oddCnt] using h
  · intro h; exact ⟨0, Nat.le_refl 0, by simpa [oddCnt] using h⟩

theorem climb_even (k num den x : Nat) (hx : x % 2 = 0) (hdn : ¬ den ≤ num) :
    climb (k + 1) num den x ↔ climb k num (2 * den) (T x) := by
  constructor
  · rintro ⟨s, hs, h⟩
    cases s with
    | zero => exact absurd (by simpa [oddCnt] using h) hdn
    | succ s' =>
      refine ⟨s', by omega, ?_⟩
      rw [oddCnt_even s' x hx] at h
      rw [Nat.pow_succ] at h
      have e : den * (2 ^ s' * 2) = 2 * den * 2 ^ s' := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [e] at h; exact h
  · rintro ⟨s', hs, h⟩
    refine ⟨s' + 1, by omega, ?_⟩
    rw [oddCnt_even s' x hx, Nat.pow_succ]
    have e : den * (2 ^ s' * 2) = 2 * den * 2 ^ s' := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [e]; exact h

theorem climb_odd (k num den x : Nat) (hx : x % 2 = 1) (hdn : ¬ den ≤ num) :
    climb (k + 1) num den x ↔ climb k (3 * num) (2 * den) (T x) := by
  have key : ∀ s', den * 2 ^ (s' + 1) ≤ num * 3 ^ (oddCnt (s' + 1) x) ↔
      2 * den * 2 ^ s' ≤ 3 * num * 3 ^ (oddCnt s' (T x)) := by
    intro s'
    rw [oddCnt_odd s' x hx, Nat.pow_succ, Nat.pow_add, Nat.pow_one]
    have e1 : den * (2 ^ s' * 2) = 2 * den * 2 ^ s' := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have e2 : num * (3 * 3 ^ oddCnt s' (T x)) = 3 * num * 3 ^ oddCnt s' (T x) := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [e1, e2]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s with
    | zero => exact absurd (by simpa [oddCnt] using h) hdn
    | succ s' => exact ⟨s', by omega, (key s').mp h⟩
  · rintro ⟨s', hs, h⟩
    exact ⟨s' + 1, by omega, (key s').mpr h⟩

theorem doob :
    ∀ k num den a d m, d % 2 = 1 →
      cnt (fun i => climb k num den (a + d * i)) (2 ^ k * m) * den ≤ m * 2 ^ k * num := by
  intro k
  induction k with
  | zero =>
    intro num den a d m _
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one]
    by_cases hdn : den ≤ num
    · have h1 := cnt_le (fun i => climb 0 num den (a + d * i)) m
      exact Nat.le_trans (Nat.mul_le_mul_right den h1) (Nat.mul_le_mul_left m hdn)
    · have : cnt (fun i => climb 0 num den (a + d * i)) m = 0 := by
        rw [cnt_congr m (Q := fun _ => False) (fun i _ => by
          rw [climb_zero]; exact ⟨fun h => hdn h, fun h => h.elim⟩)]
        exact cnt_false m
      rw [this, Nat.zero_mul]; exact Nat.zero_le _
  | succ k ih =>
    intro num den a d m hd
    by_cases hdn : den ≤ num
    · have h1 := cnt_le (fun i => climb (k + 1) num den (a + d * i)) (2 ^ (k + 1) * m)
      have := Nat.le_trans (Nat.mul_le_mul_right den h1) (Nat.mul_le_mul_left (2 ^ (k + 1) * m) hdn)
      have e : 2 ^ (k + 1) * m * num = m * 2 ^ (k + 1) * num := by
        rw [Nat.mul_comm (2 ^ (k + 1)) m]
      rw [e] at this; exact this
    · have hlen : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      rw [hlen]
      obtain ⟨e, o, he, ho, hs⟩ :=
        split_by_parity (fun x => climb (k + 1) num den x) a d (2 ^ k * m) hd
      rw [hs]
      have hE : cnt (fun i => climb (k + 1) num den (e + 2 * d * i)) (2 ^ k * m)
          = cnt (fun i => climb k num (2 * den) (e / 2 + d * i)) (2 ^ k * m) := by
        apply cnt_congr; intro i _
        obtain ⟨hm, hT⟩ := even_sub e d i he
        rw [climb_even k num den _ hm hdn, hT]
      have hO : cnt (fun i => climb (k + 1) num den (o + 2 * d * i)) (2 ^ k * m)
          = cnt (fun i => climb k (3 * num) (2 * den) ((3 * o + 1) / 2 + 3 * d * i)) (2 ^ k * m) := by
        apply cnt_congr; intro i _
        obtain ⟨hm, hT⟩ := odd_sub o d i ho
        rw [climb_odd k num den _ hm hdn, hT]
      rw [hE, hO]
      have h3d : (3 * d) % 2 = 1 := by omega
      have IE := ih num (2 * den) (e / 2) d m hd
      have IO := ih (3 * num) (2 * den) ((3 * o + 1) / 2) (3 * d) m h3d
      generalize cnt (fun i => climb k num (2 * den) (e / 2 + d * i)) (2 ^ k * m) = CE at IE ⊢
      generalize cnt (fun i => climb k (3 * num) (2 * den) ((3 * o + 1) / 2 + 3 * d * i)) (2 ^ k * m) = CO at IO ⊢
      generalize hA : m * 2 ^ k * num = A at IE
      have eIO : m * 2 ^ k * (3 * num) = 3 * A := by
        rw [← hA]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [eIO] at IO
      have eG : m * 2 ^ (k + 1) * num = 2 * A := by
        rw [← hA, Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [eG, Nat.add_mul]
      have e1 : CE * (2 * den) = 2 * (CE * den) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have e2 : CO * (2 * den) = 2 * (CO * den) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [e1] at IE; rw [e2] at IO
      omega

end L5C
