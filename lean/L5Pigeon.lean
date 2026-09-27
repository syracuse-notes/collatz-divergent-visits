/-
鳩の巣の補題:単射な時刻→値の対応で、条件 S を満たす時刻の数 ≤ S を満たす値の数。
非周期軌道では値が相異なるので、L5Comb の「時刻の数」を「値の数」に置き換えられる。
-/
import L5Comb
namespace L5

open Classical

theorem cnt_congr' {P Q : Nat → Prop} (n : Nat) (h : ∀ i, i < n → (P i ↔ Q i)) :
    cnt P n = cnt Q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt_succ, cnt_succ, ih (fun i hi => h i (by omega))]
    by_cases hp : P n
    · rw [ind_pos hp, ind_pos ((h n (by omega)).mp hp)]
    · rw [ind_neg hp, ind_neg (fun hq => hp ((h n (by omega)).mpr hq))]

theorem cnt_remove (S : Nat → Prop) (a : Nat) : ∀ hi, a < hi → S a →
    cnt S hi = cnt (fun v => S v ∧ v ≠ a) hi + 1 := by
  intro hi
  induction hi with
  | zero => intro h; exact absurd h (Nat.not_lt_zero a)
  | succ hi ih =>
    intro hlt hs
    rw [cnt_succ, cnt_succ]
    by_cases hah : a = hi
    · subst hah
      have e : cnt S a = cnt (fun v => S v ∧ v ≠ a) a :=
        cnt_congr' a (fun i hi => ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩)
      rw [e, ind_pos hs, ind_neg (fun h => h.2 rfl)]
    · rw [ih (by omega) hs]
      by_cases hsh : S hi
      · rw [ind_pos hsh, ind_pos ⟨hsh, fun h => hah h.symm⟩]
      · rw [ind_neg hsh, ind_neg (fun h => hsh h.1)]

theorem pigeon (f : Nat → Nat) (hi : Nat) : ∀ L (S : Nat → Prop),
    (∀ t1 t2, t1 < L → t2 < L → f t1 = f t2 → t1 = t2) →
    (∀ t, t < L → S (f t) → f t < hi) →
    cnt (fun t => S (f t)) L ≤ cnt S hi := by
  intro L
  induction L with
  | zero => intro S _ _; exact Nat.zero_le _
  | succ L ih =>
    intro S hinj hrange
    rw [cnt_succ]
    by_cases hs : S (f L)
    · rw [ind_pos hs]
      let S' : Nat → Prop := fun v => S v ∧ v ≠ f L
      have e : cnt (fun t => S (f t)) L = cnt (fun t => S' (f t)) L :=
        cnt_congr' L (fun t ht => ⟨fun h => ⟨h, fun heq => by
          have := hinj t L (by omega) (by omega) heq; omega⟩, fun h => h.1⟩)
      rw [e]
      have h1 := ih S' (fun t1 t2 h1 h2 => hinj t1 t2 (by omega) (by omega))
        (fun t ht hs' => hrange t (by omega) hs'.1)
      have h2 : cnt S hi = cnt S' hi + 1 := cnt_remove S (f L) hi (hrange L (by omega) hs) hs
      omega
    · rw [ind_neg hs, Nat.add_zero]
      exact ih S (fun t1 t2 h1 h2 => hinj t1 t2 (by omega) (by omega))
        (fun t ht hs' => hrange t (by omega) hs')

end L5
