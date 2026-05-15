import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic 


def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)


theorem add_comm (n m : ℕ) : n + m = m + n := sorry 
theorem add_assoc (n m p : ℕ) 
  : n + (m + p) = (n + m) + p := sorry 

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) := sorry
