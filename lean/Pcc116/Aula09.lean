import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option tactic.hygienic false

/- Semântica Operacional -/

/- Sintaxe -/

inductive Expr where
  | num : ℕ → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr

/- Semântica denotacional -/

def eval : Expr → ℕ
  | .num n     => n
  | .add e1 e2 => eval e1 + eval e2
  | .mul e1 e2 => eval e1 * eval e2

#eval eval (.mul (.add (.num 3) (.num 4)) 
                 (.num 2))   

-- 14

/- Semântica Big-Step

    A relação e ⇓ n significa que a expressão e 
    avalia para n "de uma vez só", sem detalhar 
    os passos intermediários.

                  ─────────────   BS-Num
                   .num n ⇓ n

              e₁ ⇓ n₁    e₂ ⇓ n₂
              ─────────────────────  BS-Add
               .add e₁ e₂ ⇓ n₁+n₂

              e₁ ⇓ n₁    e₂ ⇓ n₂
              ─────────────────────  BS-Mul
               .mul e₁ e₂ ⇓ n₁*n₂
-/

inductive BigStep : Expr → ℕ → Prop where
  | num (n : ℕ) : BigStep (.num n) n
  | add {e1 e2 : Expr} {n1 n2 : ℕ} 
    : BigStep e1 n1 → 
      BigStep e2 n2
    ---------------------------------
    → BigStep (.add e1 e2) (n1 + n2)
  | mul {e1 e2 : Expr} {n1 n2 : ℕ} 
    : BigStep e1 n1 → 
      BigStep e2 n2
    --------------------------------
    → BigStep (.mul e1 e2) (n1 * n2)

infix:50 " ⇓ " => BigStep

-- Exemplo: (1 + 2) * 3 ⇓ 9
example : .mul (.add (.num 1) (.num 2)) (.num 3) ⇓ 9
  := by 
      have Heq : 9 = 3 * 3 := by omega 
      rw [Heq] 
      apply BigStep.mul
      · 
        have Heq1 : 3 = 1 + 2 := by omega 
        rw [Heq1] 
        apply BigStep.add
        · 
          apply BigStep.num 
        · 
          apply BigStep.num
      · 
        apply BigStep.num 

/-! ### Conexão com o avaliador -/

theorem eval_bigStep (e : Expr) : e ⇓ eval e := by
  induction e with
  | num n          => constructor 
  | add e1 e2 IH1 IH2 => 
    constructor <;> assumption
  | mul _ _ IH1 IH2 => constructor <;> assumption 

theorem bigStep_eval 
              {e : Expr} 
              {n : ℕ} 
              (h : e ⇓ n) : eval e = n := by
  induction h with
  | num n             => rfl
  | add _ _ IH1 IH2   => simp [eval, IH1, IH2]
  | mul _ _ IH1 IH2   => simp [eval, IH1, IH2]

/-  Determinismo da semântica big-step

    Para cada expressão existe **no máximo um** resultado. -/

theorem bigStep_det {e : Expr} {n1 n2 : ℕ}
    (h1 : e ⇓ n1) (h2 : e ⇓ n2) : n1 = n2 := by
  induction h1 generalizing n2 with
  | num _ =>
      cases h2 with | num => rfl
  | add _ _ IH1 IH2 =>
      cases h2 with
      | add hb1 hb2 => rw [IH1 hb1, IH2 hb2]
  | mul _ _ IH1 IH2 =>
      cases h2 with
      | mul hb1 hb2 => rw [IH1 hb1, IH2 hb2]

/- Semântica Small-Step

    A relação e →₁ e' representa um único 
    passo de redução de e para e'.
    Os valores são números.

                 e₁ →₁ e₁'
         ─────────────────────────    SS-AddL
         .add e₁ e₂ →₁ .add e₁' e₂

                    e₂ →₁ e₂'
         ──────────────────────────────────  SS-AddR
         .add (.num n) e₂ →₁ .add (.num n) e₂'

         ──────────────────────────────────  SS-AddNum
         .add (.num n₁) (.num n₂) →₁ .num (n₁+n₂)
-/

inductive SmallStep : Expr → Expr → Prop where
  | addL  {e1 e1' e2 : Expr} 
    : SmallStep e1 e1'
    → SmallStep (.add e1 e2) (.add e1' e2)
  | addR  {n1 : ℕ} {e2 e2' : Expr} 
    : SmallStep e2 e2'
    → SmallStep (.add (.num n1) e2) (.add (.num n1) e2')
  | addNum (n1 n2 : ℕ)              
    : SmallStep (.add (.num n1) (.num n2)) (.num (n1 + n2))
  | mulL  {e1 e1' e2 : Expr}        
    : SmallStep e1 e1'
    → SmallStep (.mul e1 e2) (.mul e1' e2)
  | mulR  {n1 : ℕ} {e2 e2' : Expr} 
    : SmallStep e2 e2'
    → SmallStep (.mul (.num n1) e2) (.mul (.num n1) e2')
  | mulNum (n1 n2 : ℕ)              
    : SmallStep (.mul (.num n1) (.num n2)) (.num (n1 * n2))

infix:50 " →₁ " => SmallStep

-- Exemplo: (3+4)*2 reduz em dois passos
example : .mul (.add (.num 3) (.num 4)) (.num 2) →₁ .mul (.num 7) (.num 2) :=
  .mulL (.addNum 3 4)

example : .mul (.num 7) (.num 2) →₁ .num 14 :=
  .mulNum 7 2

/- Valores não reduzem -/

lemma num_irreducible {n : ℕ} {e : Expr} : ¬ (.num n →₁ e) := by intros H ; cases H

/- Determinismo da semântica small-step -/

theorem smallStep_det {e e1 : Expr} (h1 : e →₁ e1) :
    ∀ {e2 : Expr}, e →₁ e2 → e1 = e2 := by
  induction h1 with
  | addL hs1 IH =>
      intro e2 h2
      cases h2 with
      | addL hs2 => rw [IH hs2]
      | addR hs2 => exact absurd hs1 num_irreducible
      | addNum   => exact absurd hs1 num_irreducible
  | addR hs1 IH =>
      intro e2 h2
      cases h2 with
      | addL hs2 => exact absurd hs2 num_irreducible
      | addR hs2 => rw [IH hs2]
      | addNum   => exact absurd hs1 num_irreducible
  | addNum n1 n2 =>
      intro e2 h2
      cases h2 with
      | addL hs2 => exact absurd hs2 num_irreducible
      | addR hs2 => exact absurd hs2 num_irreducible
      | addNum   => rfl
  | mulL hs1 IH =>
      intro e2 h2
      cases h2 with
      | mulL hs2 => rw [IH hs2]
      | mulR hs2 => exact absurd hs1 num_irreducible
      | mulNum   => exact absurd hs1 num_irreducible
  | mulR hs1 IH =>
      intro e2 h2
      cases h2 with
      | mulL hs2 => exact absurd hs2 num_irreducible
      | mulR hs2 => rw [IH hs2]
      | mulNum   => exact absurd hs1 num_irreducible
  | mulNum n1 n2 =>
      intro e2 h2
      cases h2 with
      | mulL hs2 => exact absurd hs2 num_irreducible
      | mulR hs2 => exact absurd hs2 num_irreducible
      | mulNum   => rfl

/- Fecho Reflexivo-Transitivo -/

inductive MultiStep : Expr → Expr → Prop where
  | refl {e : Expr}                                     
    : MultiStep e e
  | step {e e' e'' : Expr} 
    : e →₁ e' 
    → MultiStep e' e'' 
    → MultiStep e e''

infix:50 " →* " => MultiStep

lemma MultiStep.trans {e e' e'' : Expr}
    (h1 : e →* e') (h2 : e' →* e'') : e →* e'' := by
  induction h1 with
  | refl          => exact h2
  | step hs _ IH  => exact .step hs (IH h2)

/- Equivalência entre Big-Step e Multi-Step -/

lemma multiStep_addL {e1 e1' e2 : Expr} 
                     (h : e1 →* e1') 
  : .add e1 e2 →* .add e1' e2 := by
  induction h with
  | refl          => exact .refl
  | step hs _ IH  => exact .step (.addL hs) IH

lemma multiStep_addR {n1 : ℕ} 
                     {e2 e2' : Expr} 
                     (h : e2 →* e2') 
  : .add (.num n1) e2 →* .add (.num n1) e2' := by
  induction h with
  | refl          => exact .refl
  | step hs _ IH  => exact .step (.addR hs) IH

lemma multiStep_mulL {e1 e1' e2 : Expr} 
                     (h : e1 →* e1') 
  : .mul e1 e2 →* .mul e1' e2 := by
  induction h with
  | refl          => exact .refl
  | step hs _ IH  => exact .step (.mulL hs) IH

lemma multiStep_mulR {n1 : ℕ} 
                     {e2 e2' : Expr} 
                     (h : e2 →* e2') 
    : .mul (.num n1) e2 →* .mul (.num n1) e2' := by
  induction h with
  | refl          => exact .refl
  | step hs _ IH  => exact .step (.mulR hs) IH


/- Big-Step implica Multi-Step -/

theorem bigStep_to_multiStep {e : Expr} {n : ℕ} (h : e ⇓ n) : e →* .num n := by
  induction h with
  | num n => exact .refl
  | add h1 h2 IH1 IH2 =>
      exact MultiStep.trans (multiStep_addL IH1)
           (MultiStep.trans (multiStep_addR IH2)
                            (.step (.addNum _ _) .refl))
  | mul h1 h2 IH1 IH2 =>
      exact MultiStep.trans (multiStep_mulL IH1)
           (MultiStep.trans (multiStep_mulR IH2)
                            (.step (.mulNum _ _) .refl))

/- Multi-Step implica Big-Step -/

lemma smallStep_bigStep {e e' : Expr} 
                        (hs : e →₁ e') 
  : ∀ {n : ℕ}, e' ⇓ n → e ⇓ n := by
  induction hs with
  | addL _ IH =>
      intro n hb
      cases hb with
      | add h1 h2 => exact .add (IH h1) h2
  | addR _ IH =>
      intro n hb
      cases hb with
      | add h1 h2 => exact .add h1 (IH h2)
  | addNum n1 n2 =>
      intro n hb
      cases hb with
      | num => exact .add (.num n1) (.num n2)
  | mulL _ IH =>
      intro n hb
      cases hb with
      | mul h1 h2 => exact .mul (IH h1) h2
  | mulR _ IH =>
      intro n hb
      cases hb with
      | mul h1 h2 => exact .mul h1 (IH h2)
  | mulNum n1 n2 =>
      intro n hb
      cases hb with
      | num => exact .mul (.num n1) (.num n2)

-- Lema auxiliar com endpoint `e'` generalizado (evita índice não-variável).
lemma multiStep_to_bigStep_aux 
      {e e' : Expr} (h : e →* e') 
      : ∀ {n : ℕ}, e' = .num n → e ⇓ n := by
  induction h with
  | refl => 
    intro n heq 
    rw [heq] 
    constructor
  | step hs _ IH => 
    intro n heq 
    apply smallStep_bigStep <;> try assumption 
    apply IH ; assumption 

theorem multiStep_to_bigStep 
    {e : Expr} 
    {n : ℕ} 
    (h : e →* .num n) : e ⇓ n := 
  multiStep_to_bigStep_aux h rfl

/- Teorema de Equivalência -/

theorem bigStep_iff_multiStep (e : Expr) (n : ℕ) :
    e ⇓ n ↔ e →* .num n :=
  ⟨bigStep_to_multiStep, multiStep_to_bigStep⟩
