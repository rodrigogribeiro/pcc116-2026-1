import Mathlib.Data.Nat.Basic


#check (fun (x y : ℕ) => x + y)

#check Bool 

def mynot (b : Bool) : Bool := 
  match b with 
  | Bool.true => Bool.false 
  | Bool.false => Bool.true 

def mynot1 (b : Bool) : Bool := 
  open Bool in 
  match b with 
  | true => false 
  | false => true

def mynot2 (b : Bool) : Bool := 
  match b with 
  | .true => .false 
  | .false => .true 

#eval 1 + 2
#eval mynot false 
#eval mynot true 

inductive Mybool : Type where 
| myfalse : Mybool 
| mytrue : Mybool 


def mynot3 (b : Mybool) : Mybool := 
  match b with 
  | .myfalse => .mytrue 
  | .mytrue => .myfalse 


theorem mynotinv 
  : ∀ b, mynot3 (mynot3 b) = b := by
  intros b 
  cases b 
  · 
    simp [mynot3]
  · 
    simp [mynot3]

inductive N : Type where 
| Z : N 
| S : N → N 


def addn : N → N → N 
| .Z, m => m 
| .S n, m => .S (addn n m) 


lemma addn_Z_l (n : N) 
   : addn N.Z n = n := by 
  simp [addn] 

lemma addn_Z_r (n : N) 
   : addn n N.Z = n := by 
  induction n with 
  | Z => 
    simp [addn]
  | S n1 IH1 => 
    simp only [addn]
    rw [IH1]

lemma addn_S (m n : N) 
: N.S (addn m n) = addn m (N.S n) := by 
  induction m with 
  | Z => simp [addn] 
  | S m1 IH1 => 
    simp [addn, IH1] 

theorem addn_comm (n m : N) 
   : addn n m = addn m n := by 
  induction n with 
  | Z =>
    simp [addn, addn_Z_r] 
  | S n1 IH1 =>
    simp [addn, IH1, addn_S]
  




