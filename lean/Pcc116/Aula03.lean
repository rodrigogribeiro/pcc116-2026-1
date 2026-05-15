
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic 

-- inversão de listas 

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

lemma reverse_cat {a : Type} 
   (xs ys : List a) 
  : reverse (xs ++ ys) = 
    reverse ys ++ reverse xs := by 
    induction xs with 
    | nil =>
      simp [reverse] 
    | cons x xs IHxs => 
      simp [reverse, IHxs, List.append_assoc]

theorem reverse_reverse {α : Type} 
    (xs : List α) :
    reverse (reverse xs) = xs := by 
  induction xs with 
  | nil => simp [reverse] 
  | cons y ys IHys => 
    simp [reverse, IHys, reverse_cat]

-- otimizando a inversão usando acumulador

def rev_acc {a : Type} 
  : List a -> List a -> List a 
| [], ac => ac 
| x :: xs, ac => rev_acc xs (x :: ac)

def rev {a : Type} (xs : List a) : List a := 
  rev_acc xs []

-- provando a equivalência das def. 

lemma rev_acc_append {a : Type} 
  (xs ys zs : List a) 
  : rev_acc xs ys ++ zs = rev_acc xs (ys ++ zs) 
    := by 
    revert ys zs 
    induction xs with 
    | nil => 
      simp [rev_acc]
    | cons x1 xs1 IHxs1 =>
      intros ys zs 
      simp [rev_acc, IHxs1]

theorem reverse_rev {a : Type}
  (xs : List a) : rev xs = reverse xs := by
  induction xs with 
  | nil =>
    simp [rev, rev_acc, reverse]
  | cons y ys IHys => 
    simp [rev, rev_acc, reverse, <- IHys, rev_acc_append] 
    
-- map and foldr 

def map {a b : Type} (f : a -> b) 
  : List a -> List b 
| [] => [] 
| x :: xs => f x :: map f xs 

def foldr {a b : Type}(f : a -> b -> b)(v : b) 
  : List a -> b 
| [] => v 
| x :: xs => f x (foldr f v xs) 

-- id x = x

theorem map_id {a : Type} (xs : List a) 
  : map id xs = xs := by 
  induction xs with 
  | nil => simp [map]
  | cons y ys IHys => 
    simp [map, IHys]

theorem map_append {a b : Type} 
  (f : a -> b)(xs ys : List a) : 
  map f (xs ++ ys) = map f xs ++ map f ys := by 
  induction xs with 
  | nil => simp [map]
  | cons x xs IHxs => 
    simp [map]
    exact IHxs  

def compose {a b c : Type}
  (g : b -> c)(f : a -> b) : a -> c := 
    fun x => g (f x) 

infixl:90 "•" => compose

theorem map_fusion {a b c : Type}
  (f : a -> b)(g : b -> c)(xs : List a) : 
  map (g • f) xs = map g (map f xs) := by 
    induction xs with 
    | nil => 
      simp [map]
    | cons x xs IHxs =>
      simp [map, IHxs, compose]

theorem foldr_map_fusion {a b c : Type}
  (f : a -> b)(g : b -> c -> c)
  (v : c)(xs : List a) 
  : (foldr g v • map f) xs = foldr (g • f) v xs 
    := by
    induction xs with 
    | nil =>
      simp [foldr, map, compose]
    | cons x xs IHxs => 
      simp [compose, map, foldr]
      rw [<- IHxs] 
      simp [compose] 

-- árvores binárias 

inductive BTree (a : Type) : Type where 
| Leaf : BTree a 
| Node : a -> BTree a -> BTree a -> BTree a 

def BTree.size {a : Type} : BTree a -> ℕ 
| .Leaf => 0 
| .Node _ l r => l.size + r.size + 1 

def BTree.height {a :Type} : BTree a -> ℕ 
| .Leaf => 0 
| .Node _ l r => 1 + (max l.height r.height)
  

theorem BTree.height_le_size {a : Type}
  (t : BTree a) : t.height <= t.size := by
  induction t with 
  | Leaf =>
    simp [size, height]
  | Node x l r IHl IHr =>
    simp [size, height] 
    simp [max] 
    split_ifs 
    · 
      rw [Nat.add_comm _ r.height]
      simp 
      omega 
    · 
      rw [Nat.add_comm _ l.height] 
      simp 
      omega 

def BTree.mirror {a : Type} : BTree a -> BTree a 
| .Leaf => .Leaf 
| .Node x l r => .Node x r.mirror l.mirror

theorem BTree.mirror_mirror {a : Type}
  (t : BTree a) : t.mirror.mirror = t := by 
  sorry 


