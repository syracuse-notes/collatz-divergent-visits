/-
L5 の組合せ部分(鎖と境目の数え上げ)の形式化。Lean 4 本体のみ、Mathlib なし。

任意の自然数列 x(Collatz 軌道に限らない)について、
  区間 [Y, W) への訪問回数
    ≤ (訪問のうち、その後 k ステップ Yp 以上にとどまるもの)
      + k · (「希な」上向き横断の回数 + 1)
が成り立つ。L5 では x を T 軌道、W = 2Y、Yp = Y^(1-ε) として使い、
右辺の各集合の大きさを Terras の数え上げで別に抑える(そちらは本ファイルの対象外)。
-/
namespace L5

open Classical

noncomputable def ind (P : Prop) : Nat := if P then 1 else 0

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by unfold ind; simp [h]
theorem ind_neg {P : Prop} (h : ¬P) : ind P = 0 := by unfold ind; simp [h]

noncomputable def cnt (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt P n + ind (P n)

theorem cnt_succ (P : Nat → Prop) (n : Nat) : cnt P (n + 1) = cnt P n + ind (P n) := rfl

section
variable (x : Nat → Nat) (Yp Y W k k' : Nat)

def visit (t : Nat) : Prop := Y ≤ x t ∧ x t < W
def stay (t : Nat) : Prop := ∀ s, s ≤ k → Yp ≤ x (t + s)
def nsv (t : Nat) : Prop := visit x Y W t ∧ ¬ stay x Yp k t
def upc (t : Nat) : Prop := 0 < t ∧ x (t - 1) < Yp ∧ Yp ≤ x t
def rare (t : Nat) : Prop :=
  (∀ s, s ≤ k' → Yp ≤ x (t + s)) ∨
  (∃ s, s ≤ k' ∧ Y ≤ x (t + s) ∧ ∀ r, r ≤ s → Yp ≤ x (t + r))
def ru (t : Nat) : Prop := upc x Yp t ∧ rare x Yp Y k' t
end

variable {x : Nat → Nat} {Yp Y W k k' : Nat}

/-- 最後の横断 p より後に上向き横断がなく、t で Yp 以上なら、[p, t] はずっと Yp 以上。 -/
theorem nodip {p t : Nat} (hno : ∀ u, p < u → u ≤ t → ¬ upc x Yp u) (ht : Yp ≤ x t) :
    ∀ d r, r + d = t → p ≤ r → Yp ≤ x r := by
  intro d
  induction d with
  | zero => intro r h _; rw [Nat.add_zero] at h; rw [h]; exact ht
  | succ d ih =>
    intro r h hpr
    have h1 : Yp ≤ x (r + 1) := ih (r + 1) (by omega) (by omega)
    apply Classical.byContradiction
    intro hc
    have hlt : x r < Yp := by omega
    apply hno (r + 1) (by omega) (by omega)
    refine ⟨by omega, ?_, h1⟩
    show x (r + 1 - 1) < Yp
    rw [Nat.add_sub_cancel]
    exact hlt

theorem nodip' {p t r : Nat} (hno : ∀ u, p < u → u ≤ t → ¬ upc x Yp u) (ht : Yp ≤ x t)
    (hpr : p ≤ r) (hrt : r ≤ t) : Yp ≤ x r :=
  nodip hno ht (t - r) r (by omega) hpr

/-- 訪問でステイしないなら k ≥ 1。 -/
theorem nsv_k_pos (hY : Yp ≤ Y) {t : Nat} (h : nsv x Yp Y W k t) : 1 ≤ k := by
  apply Classical.byContradiction
  intro hk
  apply h.2
  intro s hs
  have : s = 0 := by omega
  rw [this, Nat.add_zero]
  exact Nat.le_trans hY h.1.1

/-- 訪問でステイしないなら、k 以内に Yp 未満へ落ちる。 -/
theorem nsv_dip {t : Nat} (h : nsv x Yp Y W k t) : ∃ s, s ≤ k ∧ x (t + s) < Yp := by
  apply Classical.byContradiction
  intro hc
  apply h.2
  intro s hs
  apply Classical.byContradiction
  intro h2
  exact hc ⟨s, hs, by omega⟩

/-- 横断の直後の時刻から訪問 t まで Yp 以上なら、その横断は希(Climb か Stay')。 -/
theorem rare_of_visit (hY : Yp ≤ Y) {p t : Nat} (hpt : p ≤ t)
    (hall : ∀ r, p ≤ r → r ≤ t → Yp ≤ x r) (hv : Y ≤ x t) : rare x Yp Y k' p := by
  by_cases hc : t - p ≤ k'
  · refine Or.inr ⟨t - p, hc, ?_, ?_⟩
    · have : p + (t - p) = t := by omega
      rw [this]; exact hv
    · intro r hr
      exact hall (p + r) (by omega) (by omega)
  · refine Or.inl ?_
    intro s hs
    exact hall (p + s) (by omega) (by omega)

theorem cnt_mono_step (P : Nat → Prop) (n : Nat) : cnt P n ≤ cnt P (n + 1) := by
  rw [cnt_succ]; exact Nat.le_add_right _ _

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_pos h]; exact Nat.le_refl 1
  · rw [ind_neg h]; exact Nat.zero_le 1

/-- 帰納法の不変量。p: 今の区切りの開始時刻、E: 閉じた「予算つき」区切りの数、cur: 今の区切りでのステイしない訪問数。 -/
def Inv (x : Nat → Nat) (Yp Y W k k' L : Nat) : Prop :=
  ∃ p E cur : Nat,
    (p = 0 ∨ (upc x Yp p ∧ p < L)) ∧
    (∀ u, p < u → u < L → ¬ upc x Yp u) ∧
    cnt (nsv x Yp Y W k) L ≤ k * E + cur ∧
    E + ind (p = 0 ∨ rare x Yp Y k' p) ≤ cnt (ru x Yp Y k') L + 1 ∧
    ((p ≠ 0 ∧ ¬ rare x Yp Y k' p) → cur = 0) ∧
    cur ≤ k ∧
    (cur = 0 ∨ ∃ t0, p ≤ t0 ∧ t0 < L ∧ nsv x Yp Y W k t0 ∧ cur ≤ L - t0)

theorem inv_zero : Inv x Yp Y W k k' 0 := by
  refine ⟨0, 0, 0, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, Or.inl rfl⟩
  · intro u _ hu; exact absurd hu (Nat.not_lt_zero u)
  · exact Nat.le_refl 0
  · rw [ind_pos (Or.inl rfl)]; exact Nat.le_refl _
  · intro h; exact absurd rfl h.1
  · exact Nat.zero_le k

theorem inv_step (hY : Yp ≤ Y) (L : Nat) (h : Inv x Yp Y W k k' L) :
    Inv x Yp Y W k k' (L + 1) := by
  obtain ⟨p, E, cur, hp, hno, hcnt, hbud, hnr, hck, ht0⟩ := h
  by_cases hu : upc x Yp L
  · -- 新しい区切りが L で始まる
    refine ⟨L, E + ind (p = 0 ∨ rare x Yp Y k' p), ind (nsv x Yp Y W k L),
      Or.inr ⟨hu, Nat.lt_succ_self L⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u h1 h2; exact absurd h2 (by omega)
    · rw [cnt_succ]
      by_cases hr : p = 0 ∨ rare x Yp Y k' p
      · rw [ind_pos hr, Nat.mul_add, Nat.mul_one]
        have := Nat.add_le_add_right hcnt (ind (nsv x Yp Y W k L))
        omega
      · rw [ind_neg hr, Nat.add_zero]
        have hc0 : cur = 0 := hnr ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr h)⟩
        omega
    · have hL0 : L ≠ 0 := by have := hu.1; omega
      have hrl : ind (L = 0 ∨ rare x Yp Y k' L) = ind (ru x Yp Y k' L) := by
        by_cases hr : rare x Yp Y k' L
        · rw [ind_pos (Or.inr hr), ind_pos ⟨hu, hr⟩]
        · rw [ind_neg (fun h => h.elim hL0 hr), ind_neg (fun h => hr h.2)]
      rw [hrl, cnt_succ]
      omega
    · intro h
      apply ind_neg
      intro hn
      apply h.2
      refine Or.inr ⟨0, Nat.zero_le _, by rw [Nat.add_zero]; exact hn.1.1, ?_⟩
      intro r hr
      have : r = 0 := by omega
      rw [this, Nat.add_zero]; exact Nat.le_trans hY hn.1.1
    · by_cases hn : nsv x Yp Y W k L
      · rw [ind_pos hn]; exact nsv_k_pos hY hn
      · rw [ind_neg hn]; exact Nat.zero_le k
    · by_cases hn : nsv x Yp Y W k L
      · refine Or.inr ⟨L, Nat.le_refl L, Nat.lt_succ_self L, hn, ?_⟩
        rw [ind_pos hn]; omega
      · exact Or.inl (ind_neg hn)
  · -- 同じ区切りが続く
    have hno' : ∀ u, p < u → u < L + 1 → ¬ upc x Yp u := by
      intro u h1 h2
      by_cases hl : u < L
      · exact hno u h1 hl
      · have : u = L := by omega
        rw [this]; exact hu
    have hpL : p ≤ L := by
      rcases hp with h0 | ⟨_, hlt⟩
      · rw [h0]; exact Nat.zero_le L
      · exact Nat.le_of_lt hlt
    by_cases hn : nsv x Yp Y W k L
    · -- L はステイしない訪問
      have hall : ∀ r, p ≤ r → r ≤ L → Yp ≤ x r := by
        intro r h1 h2
        exact nodip' (fun u a b => hno' u a (Nat.lt_succ_of_le b))
          (Nat.le_trans hY hn.1.1) h1 h2
      have hrare_or0 : p = 0 ∨ rare x Yp Y k' p := by
        by_cases h0 : p = 0
        · exact Or.inl h0
        · exact Or.inr (rare_of_visit hY hpL hall hn.1.1)
      refine ⟨p, E, cur + 1, ?_, hno', ?_, ?_, ?_, ?_, ?_⟩
      · rcases hp with h0 | ⟨hup, hlt⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hup, by omega⟩
      · rw [cnt_succ, ind_pos hn]; omega
      · have := cnt_mono_step (ru x Yp Y k') L; omega
      · intro h; exact absurd (h.1) (fun hne => by
          rcases hrare_or0 with h0 | hr
          · exact hne h0
          · exact h.2 hr)
      · rcases ht0 with h0 | ⟨t0, hpt0, ht0L, hn0, hcur⟩
        · rw [h0]; exact nsv_k_pos hY hn
        · obtain ⟨s, hs, hxs⟩ := nsv_dip hn0
          have : L < t0 + s := by
            apply Classical.byContradiction
            intro hc
            have := hall (t0 + s) (by omega) (by omega)
            omega
          omega
      · rcases ht0 with h0 | ⟨t0, hpt0, ht0L, hn0, hcur⟩
        · refine Or.inr ⟨L, hpL, Nat.lt_succ_self L, hn, ?_⟩; omega
        · exact Or.inr ⟨t0, hpt0, by omega, hn0, by omega⟩
    · -- L はステイしない訪問ではない
      refine ⟨p, E, cur, ?_, hno', ?_, ?_, hnr, hck, ?_⟩
      · rcases hp with h0 | ⟨hup, hlt⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hup, by omega⟩
      · rw [cnt_succ, ind_neg hn]; omega
      · have := cnt_mono_step (ru x Yp Y k') L; omega
      · rcases ht0 with h0 | ⟨t0, hpt0, ht0L, hn0, hcur⟩
        · exact Or.inl h0
        · exact Or.inr ⟨t0, hpt0, by omega, hn0, by omega⟩

theorem inv_all (hY : Yp ≤ Y) : ∀ L, Inv x Yp Y W k k' L := by
  intro L
  induction L with
  | zero => exact inv_zero
  | succ L ih => exact inv_step hY L ih

/-- ステイしない訪問の数 ≤ k·(希な上向き横断の数 + 1)。 -/
theorem nsv_bound (hY : Yp ≤ Y) (L : Nat) :
    cnt (nsv x Yp Y W k) L ≤ k * (cnt (ru x Yp Y k') L + 1) := by
  obtain ⟨p, E, cur, _, _, hcnt, hbud, hnr, hck, _⟩ := inv_all (x := x) (Yp := Yp) (Y := Y) (W := W) (k := k) (k' := k') hY L
  by_cases hr : p = 0 ∨ rare x Yp Y k' p
  · rw [ind_pos hr] at hbud
    have h1 : k * E + cur ≤ k * (E + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have h2 : k * (E + 1) ≤ k * (cnt (ru x Yp Y k') L + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  · rw [ind_neg hr] at hbud
    have hc0 : cur = 0 := hnr ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr h)⟩
    have h2 : k * E ≤ k * (cnt (ru x Yp Y k') L + 1) := Nat.mul_le_mul_left k (by omega)
    omega

theorem cnt_split (P Q : Nat → Prop) (L : Nat) :
    cnt P L = cnt (fun t => P t ∧ Q t) L + cnt (fun t => P t ∧ ¬ Q t) L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [cnt_succ, cnt_succ, cnt_succ, ih]
    by_cases hp : P L
    · by_cases hq : Q L
      · rw [ind_pos hp, ind_pos ⟨hp, hq⟩, ind_neg (fun h => h.2 hq)]; omega
      · rw [ind_pos hp, ind_neg (fun h => hq h.2), ind_pos ⟨hp, hq⟩]; omega
    · rw [ind_neg hp, ind_neg (fun h => hp h.1), ind_neg (fun h => hp h.1)]; omega

/-- L5 の組合せ補題(本体)。 -/
theorem L5_comb (hY : Yp ≤ Y) (L : Nat) :
    cnt (visit x Y W) L ≤
      cnt (fun t => visit x Y W t ∧ stay x Yp k t) L + k * (cnt (ru x Yp Y k') L + 1) := by
  rw [cnt_split (visit x Y W) (stay x Yp k) L]
  have := nsv_bound (x := x) (W := W) (k := k) (k' := k') hY L
  exact Nat.add_le_add_left this _

end L5
