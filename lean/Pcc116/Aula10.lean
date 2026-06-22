import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

/- Semântica da Linguagem Imperativa IMP

   IMP é uma linguagem imperativa mínima com:
   · Expressões aritméticas  (AExp)
   · Expressões booleanas    (BExp)
   · Comandos                (Com)

   Estudaremos duas semânticas operacionais:
   1. Big-step   — ⟪c, s⟫ ⟹ s'
   2. Small-step — ⟪c, s⟫ →₁ ⟪c', s'⟫

   E provaremos a equivalência:
      ⟪c, s⟫ ⟹ s'  ↔  ⟪c, s⟫ →* ⟪skip, s'⟫
-/

-- Sintaxe

abbrev Var := String

abbrev State := Var → ℕ

def State.update (s : State) (x : Var) (n : ℕ) : State :=
  fun y => if y = x then n else s y

notation:80 s "[" x " ↦ " n "]" => State.update s x n

def State.empty : State := fun _ => 0

/-- Expressões aritméticas da linguagem IMP. -/
inductive AExp where
  | num : ℕ → AExp              -- constante numérica n
  | var : Var → AExp            -- leitura de variável x
  | add : AExp → AExp → AExp   -- soma         a₁ + a₂
  | sub : AExp → AExp → AExp   -- subtração    a₁ - a₂  (truncada em ℕ)
  | mul : AExp → AExp → AExp   -- produto      a₁ * a₂
  deriving Repr

/-- Expressões booleanas da linguagem IMP. -/
inductive BExp where
  | tt  : BExp                    -- verdadeiro
  | ff  : BExp                    -- falso
  | eq  : AExp → AExp → BExp     -- igualdade    a₁ = a₂
  | le  : AExp → AExp → BExp     -- comparação   a₁ ≤ a₂
  | not : BExp → BExp             -- negação      ¬ b
  | and : BExp → BExp → BExp     -- conjunção    b₁ ∧ b₂
  deriving Repr

/-- Comandos da linguagem IMP. -/
inductive Com where
  | skip   : Com                         -- comando nulo
  | assign : Var → AExp → Com           -- atribuição   x := a
  | seq    : Com → Com → Com            -- sequência    c₁ ; c₂
  | ite    : BExp → Com → Com → Com    -- condicional  if b then c₁ else c₂
  | whl    : BExp → Com → Com          -- repetição    while b do c
  deriving Repr

/-- Notação para sequência de comandos. -/
infixl:70 " ;; " => Com.seq

/-- Notação para atribuição. -/
notation:65 x " ::= " a => Com.assign x a


/-- Avaliação de expressão aritmética no estado s. -/
def aeval (s : State) : AExp → ℕ
  | .num n      => n
  | .var x      => s x
  | .add a₁ a₂ => aeval s a₁ + aeval s a₂
  | .sub a₁ a₂ => aeval s a₁ - aeval s a₂
  | .mul a₁ a₂ => aeval s a₁ * aeval s a₂

/-- Avaliação de expressão booleana no estado s. -/
def beval (s : State) : BExp → Bool
  | .tt        => true
  | .ff        => false
  | .eq  a₁ a₂ => (aeval s a₁ == aeval s a₂)
  | .le  a₁ a₂ => decide (aeval s a₁ ≤ aeval s a₂)
  | .not b     => !beval s b
  | .and b₁ b₂ => beval s b₁ && beval s b₂

-- Testes rápidos
#eval aeval (fun _ => 0) (.add (.num 3) (.mul (.num 2) (.num 4)))  -- 11
#eval beval (fun _ => 0) (.le (.num 3) (.num 5))                   -- true

-- Semântica Big-Step

inductive BigStep : Com → State → State → Prop where
  | skip   (s : State)
      : BigStep .skip s s
  | assign {x : Var} {a : AExp} (s : State)
      : BigStep (.assign x a) s (s[x ↦ aeval s a])
  | seq    {c₁ c₂ : Com} {s s' s'' : State}
      : BigStep c₁ s s'
      → BigStep c₂ s' s''
      → BigStep (c₁ ;; c₂) s s''
  | iteTrue  {b : BExp} {c₁ c₂ : Com} {s s' : State}
      : beval s b = true
      → BigStep c₁ s s'
      → BigStep (.ite b c₁ c₂) s s'
  | iteFalse {b : BExp} {c₁ c₂ : Com} {s s' : State}
      : beval s b = false
      → BigStep c₂ s s'
      → BigStep (.ite b c₁ c₂) s s'
  | whileFalse {b : BExp} {c : Com} (s : State)
      : beval s b = false
      → BigStep (.whl b c) s s
  | whileTrue  {b : BExp} {c : Com} {s s' s'' : State}
      : beval s b = true
      → BigStep c s s'
      → BigStep (.whl b c) s' s''
      → BigStep (.whl b c) s s''

notation:50 "⟪" c ", " s "⟫" " ⟹ " s':51 => BigStep c s s'

-- Exemplo 1: skip preserva o estado
example (s : State) : ⟪.skip, s⟫ ⟹ s := .skip s

-- Exemplo 2: x := 5 ; y := x + 1 a partir do estado vazio  →  x=5, y=6
example :
    ⟪("x" ::= .num 5) ;; ("y" ::= .add (.var "x") (.num 1)),
     State.empty⟫ ⟹ State.empty["x" ↦ 5]["y" ↦ 6] :=
  .seq (.assign State.empty) (.assign _)

/- Determinismo: cada comando tem no máximo um resultado. -/

theorem bigStep_det {c : Com} {s t1 t2 : State}
    (h1 : ⟪c, s⟫ ⟹ t1) (h2 : ⟪c, s⟫ ⟹ t2) : t1 = t2 := by
  induction h1 generalizing t2 with
  | skip   => cases h2; rfl
  | assign => cases h2; rfl
  | seq _ _ IH1 IH2 =>
      cases h2 with
      | seq ha hb =>
          rw [IH1 ha] at IH2
          exact IH2 hb
  | iteTrue hbT _ IH =>
      cases h2 with
      | iteTrue  _   hc => exact IH hc
      | iteFalse hbF _  => simp [hbT] at hbF
  | iteFalse hbF _ IH =>
      cases h2 with
      | iteTrue  hbT _  => simp [hbF] at hbT
      | iteFalse _   hc => exact IH hc
  | whileFalse _ hbF =>
      cases h2 with
      | whileFalse     => rfl
      | whileTrue hbT _ _ => simp [hbF] at hbT
  | whileTrue hbT _ _ IHc IHw =>
      cases h2 with
      | whileFalse _ hbF => simp [hbT] at hbF
      | whileTrue _ hc hw =>
          rw [IHc hc] at IHw
          exact IHw hw

-- Semântica Small-Step

inductive SmallStep : Com → State → Com → State → Prop where
  | assign {x : Var} {a : AExp} (s : State)
      : SmallStep (.assign x a) s .skip (s[x ↦ aeval s a])
  | seqSkip {c₂ : Com} (s : State)
      : SmallStep (.skip ;; c₂) s c₂ s
  | seq {c₁ c₁' c₂ : Com} {s s' : State}
      : SmallStep c₁ s c₁' s'
      → SmallStep (c₁ ;; c₂) s (c₁' ;; c₂) s'
  | iteTrue  {b : BExp} {c₁ c₂ : Com} (s : State)
      : beval s b = true
      → SmallStep (.ite b c₁ c₂) s c₁ s
  | iteFalse {b : BExp} {c₁ c₂ : Com} (s : State)
      : beval s b = false
      → SmallStep (.ite b c₁ c₂) s c₂ s
  | whileUnfold {b : BExp} {c : Com} (s : State)
      : SmallStep (.whl b c) s (.ite b (c ;; .whl b c) .skip) s

notation:50 "⟪" c ", " s "⟫" " →₁ " "⟪" c' ", " s' "⟫" => SmallStep c s c' s'

-- Exemplos de passos individuais
example (s : State) :
    ⟪"x" ::= .num 3, s⟫ →₁ ⟪.skip, s["x" ↦ 3]⟫ :=
  .assign s

example (s : State) (c₂ : Com) :
    ⟪.skip ;; c₂, s⟫ →₁ ⟪c₂, s⟫ :=
  .seqSkip s

-- Fecho Reflexivo-Transitivo (Multi-Step)

inductive MultiStep : Com → State → Com → State → Prop where
  | refl (c : Com) (s : State)
      : MultiStep c s c s
  | step {c c' c'' : Com} {s s' s'' : State}
      : SmallStep c s c' s'
      → MultiStep c' s' c'' s''
      → MultiStep c s c'' s''

notation:50 "⟪" c ", " s "⟫" " →* " "⟪" c' ", " s' "⟫" => MultiStep c s c' s'

-- Transitividade do fecho reflexivo-transitivo
lemma MultiStep.trans {c c' c'' : Com} {s s' s'' : State}
    (h1 : ⟪c, s⟫ →* ⟪c', s'⟫) (h2 : ⟪c', s'⟫ →* ⟪c'', s''⟫) :
    ⟪c, s⟫ →* ⟪c'', s''⟫ := by
  induction h1 with
  | refl    => exact h2
  | step hs _ IH => exact .step hs (IH h2)

/-- Congruência: multi-step propaga pelo lado esquerdo de seq. -/
lemma multiStep_seqL {c₁ c₁' c₂ : Com} {s s' : State}
    (h : ⟪c₁, s⟫ →* ⟪c₁', s'⟫) :
    ⟪c₁ ;; c₂, s⟫ →* ⟪c₁' ;; c₂, s'⟫ := by
  induction h with
  | refl    => exact .refl _ _
  | step hs _ IH => exact .step (.seq hs) IH

-- Exemplo de multi-step: x := 3 ; y := 2
example (s : State) :
    ⟪("x" ::= .num 3) ;; ("y" ::= .num 2), s⟫ →*
    ⟪.skip, s["x" ↦ 3]["y" ↦ 2]⟫ :=
  .step (.seq (.assign s))
  (.step (.seqSkip _)
  (.step (.assign _)
  (.refl _ _)))

-- Equivalência Big-Step ↔ Multi-Step

/- Direção 1: big-step implica multi-step -/

theorem bigStep_to_multiStep {c : Com} {s t : State}
    (h : ⟪c, s⟫ ⟹ t) : ⟪c, s⟫ →* ⟪.skip, t⟫ := by
  induction h with
  | skip s =>
      constructor 
  | assign s =>
      apply MultiStep.step <;> constructor
  | seq _ _ IH1 IH2 =>
      -- c₁;;c₂ →* skip;;c₂ →₁ c₂ →* skip
      apply MultiStep.trans 
      · apply multiStep_seqL <;> assumption  
      · apply MultiStep.trans 
        · apply MultiStep.step 
          · apply SmallStep.seqSkip
          · assumption
        · constructor 
  | iteTrue hbT _ IH =>
      apply MultiStep.step 
      · apply SmallStep.iteTrue ; assumption
      · assumption 
  | iteFalse hbF _ IH =>
      apply MultiStep.step
      · apply SmallStep.iteFalse ; assumption 
      · assumption 
  | whileFalse s hbF =>
      -- while b c →₁ if b then ... else skip →₁ skip
      apply MultiStep.step 
      · apply SmallStep.whileUnfold 
      · apply MultiStep.step 
        · apply SmallStep.iteFalse ; assumption 
        · constructor
  | whileTrue hbT _ _ IHc IHw =>
      -- while b c →₁ if b then (c;;while) else skip
      --           →₁ c;;while
      --           →* skip;;while   (por IHc)
      --           →₁ while
      --           →* skip           (por IHw)
      apply MultiStep.trans 
      · apply MultiStep.step 
        · apply SmallStep.whileUnfold
        · constructor
      · apply MultiStep.trans 
        · apply MultiStep.step 
          · apply SmallStep.iteTrue
            assumption 
          · apply MultiStep.trans 
            · apply multiStep_seqL 
              assumption 
            · apply MultiStep.trans 
              · apply MultiStep.step 
                · apply SmallStep.seqSkip 
                · assumption 
              · apply MultiStep.trans 
                · constructor
                · constructor
        · constructor

/- Direção 2: multi-step implica big-step -/

lemma smallStep_bigStep {c c' : Com} {s s' : State}
    (hs : ⟪c, s⟫ →₁ ⟪c', s'⟫) :
    ∀ {t : State}, ⟪c', s'⟫ ⟹ t → ⟪c, s⟫ ⟹ t := by
  induction hs with
  | assign s =>
      -- ⟪x:=a, s⟫ →₁ ⟪skip, s[x↦v]⟫ ;  ⟪skip, s[x↦v]⟫ ⟹ t → t = s[x↦v]
      intro t hb
      cases hb
      apply BigStep.assign s
  | seqSkip s =>
      -- ⟪skip;;c₂, s⟫ →₁ ⟪c₂, s⟫ ;  ⟪c₂, s⟫ ⟹ t → ⟪skip;;c₂, s⟫ ⟹ t
      intro t hb
      apply BigStep.seq  
      · apply BigStep.skip 
      · assumption 
  | seq _ IH =>
      -- ⟪c₁;;c₂, s⟫ →₁ ⟪c₁';;c₂, s'⟫ ;  ⟪c₁';;c₂, s'⟫ ⟹ t
      -- Por BS-Seq: ∃ smid, ⟪c₁', s'⟫ ⟹ smid ∧ ⟪c₂, smid⟫ ⟹ t
      -- Por IH: ⟪c₁, s⟫ ⟹ smid ;  daí BS-Seq fecha.
      intro t hb
      cases hb with
      | seq hc1 hc2 => 
        apply BigStep.seq 
        · apply IH ; assumption 
        · assumption
  | iteTrue s hbT =>
      intro t hb
      apply BigStep.iteTrue <;> assumption
  | iteFalse s hbF =>
      intro t hb
      apply BigStep.iteFalse <;> assumption
  | whileUnfold s =>
      -- ⟪while b c, s⟫ →₁ ⟪if b then (c;;while) else skip, s⟫
      -- Reconstruímos BS-WhileTrue ou BS-WhileFalse
      intro t hb
      cases hb with
      | iteTrue hbT hseq =>
          cases hseq with
          | seq hc hw => 
            apply BigStep.whileTrue <;> assumption
      | iteFalse hbF hskip =>
          cases hskip
          apply BigStep.whileFalse ; assumption

lemma multiStep_to_bigStep_aux {c c' : Com} {s s' : State}
    (h : ⟪c, s⟫ →* ⟪c', s'⟫) :
    ∀ {t : State}, ⟪c', s'⟫ ⟹ t → ⟪c, s⟫ ⟹ t := by
  induction h with
  | refl    => intro t hb; exact hb
  | step hs _ IH =>
      intro t hb
      apply smallStep_bigStep <;> try assumption 
      apply IH ; assumption 

theorem multiStep_to_bigStep {c : Com} {s t : State}
    (h : ⟪c, s⟫ →* ⟪.skip, t⟫) : ⟪c, s⟫ ⟹ t :=
  multiStep_to_bigStep_aux h (.skip t)

/- Teorema de Equivalência -/

theorem bigStep_iff_multiStep (c : Com) (s t : State) :
    ⟪c, s⟫ ⟹ t  ↔  ⟪c, s⟫ →* ⟪.skip, t⟫ :=
  ⟨bigStep_to_multiStep, multiStep_to_bigStep⟩
