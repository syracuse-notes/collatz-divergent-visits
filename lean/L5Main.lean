/-
L5 の組み立て(整数版)。非周期の Collatz 軌道 x_t = T^t(N) について、
区間 [Y, 2Y) への訪問回数を、Chernoff 型・Doob 型の個数評価で抑える。

  V ≤ S + k·(C + P + 1)
  S·(u^t0·w^k)  ≤ m1·(u+w)^k·w^t0      (Stay:その後 k ステップ Yp 以上)
  C·Y           ≤ m2·2^k'·(3Yp)         (Climb:k' 以内に Yp 以上のまま Y に届く横断)
  P·(u^t1·w^k') ≤ m2·(u+w)^k'·w^t1     (Stay':k' ステップ Yp 以上の横断)

t0, t1 は「3^j が一定以上なら j ≥ t0(t1)」を満たす任意のしきい値。
ここから Y^(1−γ) の形にするには、u, w, t0, t1, k, k' を Y の関数として選ぶ実数の評価が要る(本ファイルの対象外)。
-/
import L5Comb
import L5Count
import L5Link
import L5Pigeon
namespace L5M

open Classical

-- 3つのファイルで別々に定義した同じもの同士をつなぐ
theorem T_eq : L5C.T = L5L.T := rfl

theorem oddCnt_eq : ∀ k x, L5C.oddCnt k x = L5L.oddCnt k x := by
  intro k; induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; show _ + L5C.oddCnt k (L5C.T x) = _ + L5L.oddCnt k (L5L.T x); rw [ih]; rfl

theorem ind_eq (P : Prop) : L5.ind P = L5C.ind P := rfl

theorem cnt_eq (P : Nat → Prop) : ∀ n, L5.cnt P n = L5C.cnt P n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => rw [L5.cnt_succ, L5C.cnt_succ, ih, ind_eq]

open L5L in
theorem Titer_add : ∀ t s x, Titer (t + s) x = Titer s (Titer t x) := by
  intro t; induction t with
  | zero => intro s x; rw [Nat.zero_add]; rfl
  | succ t ih =>
    intro s x
    have e : t + 1 + s = (t + s) + 1 := by omega
    rw [e]; show Titer (t + s) (T x) = Titer s (Titer t (T x)); exact ih s (T x)

open L5L in
theorem Titer_succ (t x : Nat) : Titer (t + 1) x = T (Titer t x) := by
  have := Titer_add t 1 x; rw [this]; rfl

theorem cnt_mono (P : Nat → Prop) (n r : Nat) : L5C.cnt P n ≤ L5C.cnt P (n + r) := by
  induction r with
  | zero => exact Nat.le_refl _
  | succ r ih => rw [← Nat.add_assoc, L5C.cnt_succ]; omega

theorem cnt_shift (Q : Nat → Prop) (Y : Nat) : ∀ n,
    L5C.cnt (fun v => Y ≤ v ∧ Q v) (Y + n) = L5C.cnt (fun i => Q (Y + i)) n := by
  intro n; induction n with
  | zero =>
    rw [Nat.add_zero]
    have : ∀ m, m ≤ Y → L5C.cnt (fun v => Y ≤ v ∧ Q v) m = 0 := by
      intro m; induction m with
      | zero => intro _; rfl
      | succ m ih => intro h; rw [L5C.cnt_succ, ih (by omega), L5C.ind_neg (fun h' => by omega)]
    exact this Y (Nat.le_refl Y)
  | succ n ih =>
    rw [← Nat.add_assoc, L5C.cnt_succ, ih, L5C.cnt_succ]
    by_cases hq : Q (Y + n)
    · rw [L5C.ind_pos ⟨by omega, hq⟩, L5C.ind_pos hq]
    · rw [L5C.ind_neg (fun h => hq h.2), L5C.ind_neg hq]

theorem cnt_imp {P Q : Nat → Prop} (n : Nat) (h : ∀ i, i < n → P i → Q i) :
    L5C.cnt P n ≤ L5C.cnt Q n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [L5C.cnt_succ, L5C.cnt_succ]
    have := ih (fun i hi => h i (by omega))
    by_cases hp : P n
    · rw [L5C.ind_pos hp, L5C.ind_pos (h n (by omega) hp)]; omega
    · rw [L5C.ind_neg hp]; have := L5C.ind_le_one (Q n); omega

theorem cnt_or (P Q : Nat → Prop) (n : Nat) :
    L5C.cnt (fun i => P i ∨ Q i) n ≤ L5C.cnt P n + L5C.cnt Q n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [L5C.cnt_succ, L5C.cnt_succ, L5C.cnt_succ]
    by_cases hp : P n
    · rw [L5C.ind_pos (Or.inl hp), L5C.ind_pos hp]; omega
    · by_cases hq : Q n
      · rw [L5C.ind_pos (Or.inr hq), L5C.ind_pos hq]; omega
      · rw [L5C.ind_neg (fun h => h.elim hp hq), L5C.ind_neg hp, L5C.ind_neg hq]; omega

/-- 区間 [a, a+ℓ) の個数を、長さ 2^k·m ≥ ℓ の等差数列(差 1)の個数で上から抑える。 -/
theorem interval_to_ap (Q : Nat → Prop) (a ℓ k m : Nat) (h : ℓ ≤ 2 ^ k * m) :
    L5C.cnt (fun v => a ≤ v ∧ Q v) (a + ℓ) ≤ L5C.cnt (fun i => Q (a + 1 * i)) (2 ^ k * m) := by
  rw [cnt_shift]
  have e : L5C.cnt (fun i => Q (a + 1 * i)) (2 ^ k * m) = L5C.cnt (fun i => Q (a + i)) (2 ^ k * m) :=
    L5C.cnt_congr _ (fun i _ => by rw [Nat.one_mul])
  rw [e]
  have := cnt_mono (fun i => Q (a + i)) ℓ (2 ^ k * m - ℓ)
  rw [Nat.add_sub_cancel' h] at this; exact this

section
variable (N : Nat)
def x (t : Nat) : Nat := L5L.Titer t N
end

theorem oddCnt_le : ∀ s v, L5L.oddCnt s v ≤ s := by
  intro s; induction s with
  | zero => intro v; exact Nat.le_refl 0
  | succ s ih =>
    intro v
    show (if v % 2 = 1 then 1 else 0) + L5L.oddCnt s (L5L.T v) ≤ s + 1
    have := ih (L5L.T v)
    split <;> omega

theorem x_add (N t r : Nat) : x N (t + r) = L5L.Titer r (x N t) := Titer_add t r N

/-- 値が Yp 以上の区間での補正項評価を、軌道の言葉で。 -/
theorem corr_orbit (N t s Yp : Nat) (hYp : 1 ≤ Yp) (hs : 2 * s ≤ 3 * Yp + 1)
    (hall : ∀ r, r < s → Yp ≤ x N (t + r)) :
    2 ^ s * x N (t + s) ≤ 2 * 3 ^ (L5L.oddCnt s (x N t)) * x N t := by
  rw [x_add]
  apply L5L.correction Yp s (x N t) hYp
  · intro r hr _; rw [← x_add]; exact hall r hr
  · have := oddCnt_le s (x N t); omega

/-- 3つの個数(N にも L にもよらない)。 -/
noncomputable def Sb (Y k t0 m1 : Nat) : Nat := L5C.cnt (fun i => t0 ≤ L5C.oddCnt k (Y + 1 * i)) (2 ^ k * m1)
noncomputable def Cb (Yp Y k' m2 : Nat) : Nat := L5C.cnt (fun i => L5C.climb k' (3 * Yp) Y (Yp + 1 * i)) (2 ^ k' * m2)
noncomputable def Pb (Yp k' t1 m2 : Nat) : Nat := L5C.cnt (fun i => t1 ≤ L5C.oddCnt k' (Yp + 1 * i)) (2 ^ k' * m2)

theorem L5_main (N L Y Yp k k' u w t0 t1 m1 m2 : Nat)
    (hinj : ∀ t1 t2, x N t1 = x N t2 → t1 = t2)
    (hYp : 1 ≤ Yp) (hYY : Yp ≤ Y) (huw : w ≤ u)
    (hk : 2 * k ≤ 3 * Yp + 1) (hk' : 2 * k' ≤ 3 * Yp + 1)
    (hm1 : Y ≤ 2 ^ k * m1) (hm2 : Yp / 2 + 1 ≤ 2 ^ k' * m2)
    (ht0 : ∀ j, Yp * 2 ^ k ≤ 4 * Y * 3 ^ j → t0 ≤ j)
    (ht1 : ∀ j, Yp * 2 ^ k' ≤ 3 * Yp * 3 ^ j → t1 ≤ j) :
    L5.cnt (L5.visit (x N) Y (2 * Y)) L ≤ Sb Y k t0 m1 + k * (Cb Yp Y k' m2 + Pb Yp k' t1 m2 + 1) ∧
      Sb Y k t0 m1 * (u ^ t0 * w ^ k) ≤ m1 * (u + w) ^ k * w ^ t0 ∧
      Cb Yp Y k' m2 * Y ≤ m2 * 2 ^ k' * (3 * Yp) ∧
      Pb Yp k' t1 m2 * (u ^ t1 * w ^ k') ≤ m2 * (u + w) ^ k' * w ^ t1 := by
  -- 定数
  refine ⟨?_,
          L5C.chernoff u w huw k t0 Y 1 m1 (by decide),
          L5C.doob k' (3 * Yp) Y Yp 1 m2 (by decide),
          L5C.chernoff u w huw k' t1 Yp 1 m2 (by decide)⟩
  unfold Sb Cb Pb
  have hc := L5.L5_comb (x := x N) (Yp := Yp) (Y := Y) (W := 2 * Y) (k := k) (k' := k') hYY L
  have hinjL : ∀ t1 t2, t1 < L → t2 < L → x N t1 = x N t2 → t1 = t2 :=
    fun a b _ _ h => hinj a b h
  -- (A) ステイする訪問 → S
  have hA : L5.cnt (fun t => L5.visit (x N) Y (2 * Y) t ∧ L5.stay (x N) Yp k t) L
      ≤ L5C.cnt (fun i => t0 ≤ L5C.oddCnt k (Y + 1 * i)) (2 ^ k * m1) := by
    let R0 : Nat → Prop := fun v => Y ≤ v ∧ (v < Y + Y ∧ t0 ≤ L5C.oddCnt k v)
    have a1 : L5.cnt (fun t => L5.visit (x N) Y (2 * Y) t ∧ L5.stay (x N) Yp k t) L
        ≤ L5.cnt (fun t => R0 (x N t)) L := by
      rw [cnt_eq, cnt_eq]
      apply cnt_imp; intro t _ ⟨⟨hv1, hv2⟩, hst⟩
      refine ⟨hv1, by omega, ?_⟩
      have hcorr := corr_orbit N t k Yp hYp hk (fun r hr => hst r (by omega))
      have hend : Yp ≤ x N (t + k) := hst k (Nat.le_refl k)
      rw [oddCnt_eq]
      apply ht0
      generalize L5L.oddCnt k (x N t) = j at hcorr
      have h1 : Yp * 2 ^ k ≤ 2 ^ k * x N (t + k) := by
        have := Nat.mul_le_mul_left (2 ^ k) hend; rw [Nat.mul_comm Yp]; exact this
      have h2 : 2 * 3 ^ j * x N t ≤ 2 * 3 ^ j * (2 * Y) := Nat.mul_le_mul_left _ (by omega)
      have h3 : 2 * 3 ^ j * (2 * Y) = 4 * Y * 3 ^ j := by
        rw [show (4 : Nat) = 2 * 2 from rfl]
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      omega
    have a2 : L5.cnt (fun t => R0 (x N t)) L ≤ L5.cnt R0 (Y + Y) :=
      L5.pigeon (x N) (Y + Y) L R0 hinjL (fun t _ h => h.2.1)
    have a3 : L5.cnt R0 (Y + Y) ≤ L5C.cnt (fun i => t0 ≤ L5C.oddCnt k (Y + 1 * i)) (2 ^ k * m1) := by
      rw [cnt_eq]
      have := interval_to_ap (fun v => v < Y + Y ∧ t0 ≤ L5C.oddCnt k v) Y Y k m1 hm1
      exact Nat.le_trans this (cnt_imp _ (fun i _ h => h.2))
    omega
  -- (B) 希な上向き横断 → C + P
  have hup : ∀ t, L5.upc (x N) Yp t → Yp ≤ x N t ∧ 2 * x N t + 2 ≤ 3 * Yp := by
    intro t ⟨ht, hlt, hge⟩
    refine ⟨hge, ?_⟩
    have e : x N t = L5L.T (x N (t - 1)) := by
      have := Titer_succ (t - 1) N
      rw [Nat.sub_add_cancel ht] at this; exact this
    rw [e] at hge ⊢
    unfold L5L.T at hge ⊢
    split
    · rename_i h; rw [if_pos h] at hge; omega
    · rename_i h; omega
  have hB : L5.cnt (L5.ru (x N) Yp Y k') L
      ≤ L5C.cnt (fun i => L5C.climb k' (3 * Yp) Y (Yp + 1 * i)) (2 ^ k' * m2)
        + L5C.cnt (fun i => t1 ≤ L5C.oddCnt k' (Yp + 1 * i)) (2 ^ k' * m2) := by
    let Rc : Nat → Prop := fun v => Yp ≤ v ∧ (v < Yp + (Yp / 2 + 1) ∧ L5C.climb k' (3 * Yp) Y v)
    let Rs : Nat → Prop := fun v => Yp ≤ v ∧ (v < Yp + (Yp / 2 + 1) ∧ t1 ≤ L5C.oddCnt k' v)
    have b1 : L5.cnt (L5.ru (x N) Yp Y k') L
        ≤ L5.cnt (fun t => Rc (x N t)) L + L5.cnt (fun t => Rs (x N t)) L := by
      rw [cnt_eq, cnt_eq, cnt_eq]
      refine Nat.le_trans (cnt_imp L (Q := fun t => Rc (x N t) ∨ Rs (x N t)) ?_) (cnt_or _ _ L)
      intro t _ ⟨hu, hr⟩
      obtain ⟨hge, hlt2⟩ := hup t hu
      rcases hr with hst | ⟨s, hs, hY, hall⟩
      · -- Stay'
        refine Or.inr ⟨hge, by omega, ?_⟩
        have hcorr := corr_orbit N t k' Yp hYp hk' (fun r hr => hst r (by omega))
        have hend : Yp ≤ x N (t + k') := hst k' (Nat.le_refl k')
        rw [oddCnt_eq]; apply ht1
        generalize L5L.oddCnt k' (x N t) = j at hcorr
        have h1 : Yp * 2 ^ k' ≤ 2 ^ k' * x N (t + k') := by
          have := Nat.mul_le_mul_left (2 ^ k') hend; rw [Nat.mul_comm Yp]; exact this
        have h2 : 2 * 3 ^ j * x N t ≤ 3 * Yp * 3 ^ j := by
          have : 2 * 3 ^ j * x N t = 3 ^ j * (2 * x N t) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          rw [this, Nat.mul_comm (3 * Yp)]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      · -- Climb
        refine Or.inl ⟨hge, by omega, ⟨s, hs, ?_⟩⟩
        have hcorr := corr_orbit N t s Yp hYp (by omega) (fun r hr => hall r (by omega))
        rw [oddCnt_eq]
        generalize L5L.oddCnt s (x N t) = j at hcorr
        have h1 : Y * 2 ^ s ≤ 2 ^ s * x N (t + s) := by
          have := Nat.mul_le_mul_left (2 ^ s) hY; rw [Nat.mul_comm Y]; exact this
        have h2 : 2 * 3 ^ j * x N t ≤ 3 * Yp * 3 ^ j := by
          have : 2 * 3 ^ j * x N t = 3 ^ j * (2 * x N t) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          rw [this, Nat.mul_comm (3 * Yp)]; exact Nat.mul_le_mul_left _ (by omega)
        omega
    have b2 : L5.cnt (fun t => Rc (x N t)) L ≤ L5.cnt Rc (Yp + (Yp / 2 + 1)) :=
      L5.pigeon (x N) _ L Rc hinjL (fun t _ h => h.2.1)
    have b3 : L5.cnt (fun t => Rs (x N t)) L ≤ L5.cnt Rs (Yp + (Yp / 2 + 1)) :=
      L5.pigeon (x N) _ L Rs hinjL (fun t _ h => h.2.1)
    have b4 : L5.cnt Rc (Yp + (Yp / 2 + 1))
        ≤ L5C.cnt (fun i => L5C.climb k' (3 * Yp) Y (Yp + 1 * i)) (2 ^ k' * m2) := by
      rw [cnt_eq]
      exact Nat.le_trans (interval_to_ap (fun v => v < Yp + (Yp / 2 + 1) ∧ L5C.climb k' (3 * Yp) Y v)
        Yp (Yp / 2 + 1) k' m2 hm2) (cnt_imp _ (fun i _ h => h.2))
    have b5 : L5.cnt Rs (Yp + (Yp / 2 + 1))
        ≤ L5C.cnt (fun i => t1 ≤ L5C.oddCnt k' (Yp + 1 * i)) (2 ^ k' * m2) := by
      rw [cnt_eq]
      exact Nat.le_trans (interval_to_ap (fun v => v < Yp + (Yp / 2 + 1) ∧ t1 ≤ L5C.oddCnt k' v)
        Yp (Yp / 2 + 1) k' m2 hm2) (cnt_imp _ (fun i _ h => h.2))
    omega
  -- (C) まとめ
  have hk2 := Nat.mul_le_mul_left k (Nat.add_le_add_right hB 1)
  omega

theorem cnt_mono5 (P : Nat → Prop) (n r : Nat) : L5.cnt P n ≤ L5.cnt P (n + r) := by
  induction r with
  | zero => exact Nat.le_refl _
  | succ r ih => rw [← Nat.add_assoc, L5.cnt_succ]; omega

theorem grow (P : Nat → Prop) (hinf : ∀ L0, ∃ t, L0 ≤ t ∧ P t) : ∀ n, ∃ L, n ≤ L5.cnt P L := by
  intro n
  induction n with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨t, ht, hp⟩ := hinf L
    refine ⟨t + 1, ?_⟩
    rw [L5.cnt_succ, L5.ind_pos hp]
    have := cnt_mono5 P L (t - L)
    rw [Nat.add_sub_cancel' ht] at this
    omega

/-- 有限時刻の一様な上界から全時刻へ:ある L0 以後は条件を満たす時刻がなく、L0 までの個数が上界以下。 -/
theorem all_time (P : Nat → Prop) (B : Nat) (h : ∀ L, L5.cnt P L ≤ B) :
    ∃ L0, (∀ t, L0 ≤ t → ¬ P t) ∧ L5.cnt P L0 ≤ B := by
  by_cases hex : ∃ L0, ∀ t, L0 ≤ t → ¬ P t
  · obtain ⟨L0, h0⟩ := hex; exact ⟨L0, h0, h L0⟩
  · exfalso
    have hinf : ∀ L0, ∃ t, L0 ≤ t ∧ P t := by
      intro L0
      apply Classical.byContradiction
      intro hc
      exact hex ⟨L0, fun t ht hp => hc ⟨t, ht, hp⟩⟩
    obtain ⟨L, hL⟩ := grow P hinf (B + 1)
    have := h L
    omega

/-- L5 の全時刻版:[Y, 2Y) への訪問は有限回で、その回数は N によらない上界以下。 -/
theorem L5_all_time (N Y Yp k k' u w t0 t1 m1 m2 : Nat)
    (hinj : ∀ t1 t2, x N t1 = x N t2 → t1 = t2)
    (hYp : 1 ≤ Yp) (hYY : Yp ≤ Y) (huw : w ≤ u)
    (hk : 2 * k ≤ 3 * Yp + 1) (hk' : 2 * k' ≤ 3 * Yp + 1)
    (hm1 : Y ≤ 2 ^ k * m1) (hm2 : Yp / 2 + 1 ≤ 2 ^ k' * m2)
    (ht0 : ∀ j, Yp * 2 ^ k ≤ 4 * Y * 3 ^ j → t0 ≤ j)
    (ht1 : ∀ j, Yp * 2 ^ k' ≤ 3 * Yp * 3 ^ j → t1 ≤ j) :
    ∃ L0, (∀ t, L0 ≤ t → ¬ L5.visit (x N) Y (2 * Y) t) ∧
      L5.cnt (L5.visit (x N) Y (2 * Y)) L0 ≤ Sb Y k t0 m1 + k * (Cb Yp Y k' m2 + Pb Yp k' t1 m2 + 1) :=
  all_time _ _ (fun L => (L5_main N L Y Yp k k' u w t0 t1 m1 m2 hinj hYp hYY huw hk hk' hm1 hm2 ht0 ht1).1)

end L5M
