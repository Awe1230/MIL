import Mathlib.Data.Nat.Dist
import MathLib.Tactic.Linarith

-- really it looks like Nat.Dist is the same idea, and already has some lemmas.
--let's try re-doing this file using Nat.dist instead of abs_diff
-- and hopefully a lot of the proofs will be shorter/easier.
-- many of them may already be in Nat.dist or be corollaries of something in there

open Nat --so we don't have to type Nat.dist every time
-- don't use this anymore. replace it everywhere by dist
def abs_diff (i j : ℕ) : ℕ :=
  if i>j then i-j else j-i

--needed
theorem ad_direction_known {n i j : ℕ }(h1: i<j) (h2 : abs_diff i j >= n) : j>= i+n := by
  unfold abs_diff at h2
  have not_lt : ¬ i > j := by linarith [h1]
  simp [not_lt] at h2
  rw [add_comm]
  exact add_le_of_le_sub (LT.lt.le h1) h2

  
  
  -- unfold abs_diff at h2
  -- have not_lt : ¬ i > j := by linarith [h1]
  -- simp [not_lt] at h2
  -- have add_both : n+i <= j-i +i := by linarith [h2]
  -- have minus_plus : j-i+i = j := by
  --   exact Nat.sub_add_cancel (Nat.not_lt.mp not_lt)
  -- rw [← minus_plus]
  -- rw [add_comm i n]
  -- exact add_both

--helper, potentially interesting if not already there
theorem ge_not_e {a b : ℕ} (h1 : a>=b) (h2 : a≠b) : b < a := by
  exact Nat.lt_of_le_of_ne h1 (id (Ne.symm h2))

--helper, uninteresting (delete if you don't use it)
theorem move_over {a b n : ℕ} (h2 : a>= b+n): a - n >= b := Nat.le_sub_of_add_le h2

--helper, uninteresting (delete if you don't use it)
theorem move_over_lt {a b n : ℕ} (h2 : a>b+n) : a-n>b := Nat.lt_sub_of_add_lt h2

--helper, potentially interesting if not already there
theorem minuend_minus_one {i j : ℕ} (h : j-i>0) : (j-1)-i<j-i := by
  refine (Nat.lt_iff_le_pred h).mpr ?_
  exact Nat.le_of_eq (Nat.sub_right_comm j 1 i)

--helper, potentially interesting if not already there
theorem minus_plus {a b :  ℕ } (h : b<=a)  : a = a-b+b := by
  refine (Nat.sub_add_cancel ?h).symm
  exact h

-- helper, interesting if new
theorem sandwich {i j : ℕ} (h1 : i<=j) : (j = i+ (j-i)) := by
exact Eq.symm (add_sub_of_le h1)
  -- induction' j with k hk
  -- · simp
  --   linarith [h1]
  -- cases h1
  -- · simp
  -- rename_i i_le_k
  -- rw [Nat.succ_sub i_le_k, Nat.add_succ]
  -- apply Nat.succ_inj'.mpr
  -- apply hk i_le_k

-- helper, interesting if new
theorem swap { a b c : ℕ } (h : b<= a) (h1 : b <= c) : a-b+c=a+(c-b) := by
apply Nat.sub_add_comm at h
rw [Nat.add_sub_assoc h1 a] at h
apply (symm h)




--helper, but interesting if it doesn't already exist
theorem swap_assoc { a b c : ℕ } (h : b<= a) : a-b+c=(a+c)-b := by
  exact Eq.symm (Nat.sub_add_comm h)

--helper, but interesting if it doesn't already exist
theorem changing_subtrahend {i j : ℕ} (h : j>i+1) : j-i = (j-(i+1))+1 := by
  refine Nat.eq_add_of_sub_eq ?hle rfl
  apply LT.lt.le at h
  exact Nat.le_sub_of_add_le' h

--helper, uninteresting (delete if you don't use it)
theorem less_than_one_less {i j : ℕ} : i>j-1 ∨ i=j-1 ∨ i<j-1  := trichotomous i (j - 1)

--helper, uninteresting (delete if you don't use it)
theorem bigger_diff_positive { i j : ℕ} (h : j>i) : j-i>0 := Nat.sub_pos_of_lt h

--definitely need
theorem ad_smaller_bigger {i j : ℕ} (h : i+1<j) : abs_diff (i + 1) j < abs_diff i j := by
  unfold abs_diff
  have H : ¬ j < i + 1 := by linarith [h]
  have H1 : ¬ j < i := by linarith [h]
  simp [H, H1]
  exact sub_succ_lt_self j i (LT.lt.le h)
  -- rw [changing_subtrahend h]
  -- exact Nat.lt.base (j - (i + 1))

--definitely need
theorem ad_larger_littler {i j : ℕ} (h : i+1<j) : abs_diff i (j-1) < abs_diff i j := by
  unfold abs_diff
  have H : ¬ i > j - 1 := by linarith [move_over_lt h]
  have H1 : ¬ j < i := by linarith [h]
  rw [add_comm] at h
  have H2 : j - i > 0 := by linarith [move_over_lt h]
  simp [H, H1]
  exact minuend_minus_one H2
