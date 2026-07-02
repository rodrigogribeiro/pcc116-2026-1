import Pcc116.Aula10

set_option autoImplicit false
set_option tactic.hygienic false

/- Lógica de Hoare para a Linguagem IMP

   A lógica de Hoare é um sistema formal para raciocinar sobre a
   correção de programas imperativos de forma composicional.
   Uma tripla de Hoare  { P } c { Q }  é lida:

       "se P vale no estado inicial e c termina, então Q vale no estado final"

   P é chamada de pré-condição e Q de pós-condição.

   Nesta aula:
   1. Definimos asserções e a substituição de asserção.
   2. Apresentamos as regras de derivação como um predicado indutivo.
   3. Definimos a noção semântica de validade de triplas.
   4. Provamos o teorema de soundness: toda tripla derivável é válida.
-/

-- Asserções

/-- Uma asserção é um predicado sobre estados. -/
abbrev Assertion := State → Prop

/-- Substituição de asserção: assub P x a s = P (s[x ↦ aeval s a]).

    Esta é a pré-condição mais fraca para x := a com pós-condição P:
    se P vale no estado atualizado, então P valerá após a atribuição. -/
def assub (P : Assertion) (x : Var) (a : AExp) : Assertion :=
  fun s => P (s[x ↦ aeval s a])

def aand (P Q : Assertion) : Assertion := 
  fun s => P s ∧ Q s 

def aor (P Q : Assertion) : Assertion := 
  fun s => P s ∨ Q s 

def atrue (b : BExp) : Assertion := 
  fun s => beval s b = true 

def afalse (b : BExp) : Assertion :=
  fun s => beval s b = false

def aequal (a : AExp) (v : ℕ) : Assertion := 
  fun s => aeval s a = v 

infixl:35 " .&. " => aand
infixl:30 " .||. " => aor

notation:max "True(" b ")" => atrue b
notation:max "False(" b ")" => afalse b
notation:65 x " .==. " v => aequal (AExp.var x) v


-- Triplas de Hoare (sistema de prova)


inductive HoareTriple : Assertion → Com → Assertion → Prop where
  | skip   {P : Assertion}
      : HoareTriple P .skip P
  | assign {P : Assertion} {x : Var} {a : AExp}
      : HoareTriple (assub P x a) (.assign x a) P
  | seq    {P Q R : Assertion} {c₁ c₂ : Com}
      : HoareTriple P c₁ Q
      → HoareTriple Q c₂ R
      → HoareTriple P (c₁ ;; c₂) R
  | ite    {P Q : Assertion} {b : BExp} {c₁ c₂ : Com}
      : HoareTriple (P .&. True(b))  c₁ Q
      → HoareTriple (P .&. False(b)) c₂ Q
      → HoareTriple P (.ite b c₁ c₂) Q
  | whl    {I : Assertion} {b : BExp} {c : Com}
      : HoareTriple (I .&. True(b)) c I
      → HoareTriple I (.whl b c) (I .&. False(b))
  | conseq {P P' Q Q' : Assertion} {c : Com}
      : (∀ s, P' s → P s)
      → HoareTriple P c Q
      → (∀ s, Q s → Q' s)
      → HoareTriple P' c Q'

notation:25 "{{ " P " }} " c " {{ " Q " }}" => HoareTriple P c Q

-- Regras derivadas para conveniência
lemma conseq_pre {P P' Q : Assertion} {c : Com}
    (h : ∀ s, P' s → P s) (ht : {{ P }} c {{ Q }}) : {{ P' }} c {{ Q }} :=
  .conseq h ht (fun _ hq => hq)

lemma conseq_post {P Q Q' : Assertion} {c : Com}
    (ht : {{ P }} c {{ Q }}) (h : ∀ s, Q s → Q' s) : {{ P }} c {{ Q' }} :=
  .conseq (fun _ hp => hp) ht h

-- Tripla Semântica (Validade)

/-- Uma tripla é semanticamente válida se toda execução que começa
    com P satisfeita termina com Q satisfeita. -/
def ValidTriple (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ s t, P s → ⟪c, s⟫ ⟹ t → Q t

notation:25 "{{* " P " *}} " c " {{* " Q " *}}" => ValidTriple P c Q

-- Soundness (Correção do Sistema)

/-- Lema auxiliar: a regra do while é semanticamente válida.

    Como `BigStep` está em `Prop`, seu recursor só elimina em `Prop`.
    Não é possível definir uma função `ℕ`-valued de profundidade diretamente.
    A solução é generalizar o comando `cmd` como variável livre antes de
    induzir, obtendo um IH suficientemente forte para o caso recursivo. -/
lemma while_valid {b : BExp} {c : Com} (I : Assertion)
    (hbody : {{* I .&. True(b) *}} c {{* I *}}) :
    {{* I *}} (.whl b c) {{* I .&. False(b) *}} := by
  -- Generaliza cmd para que `induction hBig` funcione (índices livres)
  suffices h : ∀ cmd s t, BigStep cmd s t → 
                          cmd = .whl b c →
                          I s → 
                          I t ∧ beval t b = false 
  from fun s t hIs hBig => h _ s t hBig rfl hIs
  intro cmd s t hBig hEq hIs
  induction hBig with
  | skip _      => simp at hEq
  | assign _    => simp at hEq
  | seq _ _ _ _ => simp at hEq
  | iteTrue _ _ _   => simp at hEq
  | iteFalse _ _ _  => simp at hEq
  | whileFalse s' hbF =>
      -- injection gives hb : b_inner = b_outer; use ▸ to rewrite hbF
      injection hEq with hb hc_eq
      exact ⟨hIs, hb ▸ hbF⟩
  | whileTrue hbT hc hw _ IHw =>
      -- injection consumes hEq; save it first so we can pass it to IHw
      have hEq' := hEq
      injection hEq with hb hc_eq
      exact IHw hEq' (hbody _ _ ⟨hIs, hb ▸ hbT⟩ (hc_eq ▸ hc))

/-- Teorema de Soundness: toda tripla derivável é semanticamente válida. -/
theorem hoare_sound {P : Assertion} {c : Com} {Q : Assertion}
    (h : {{ P }} c {{ Q }}) : {{* P *}} c {{* Q *}} := by
  induction h with
  | skip =>
      intro s _ hPs hBig; cases hBig; exact hPs
  | assign =>
      intro s _ hPs hBig; cases hBig; exact hPs
  | seq _ _ IH1 IH2 =>
      intro s t hPs hBig
      cases hBig with
      | seq h1 h2 => exact IH2 _ _ (IH1 _ _ hPs h1) h2
  | ite _ _ IH1 IH2 =>
      intro s t hPs hBig
      cases hBig with
      | iteTrue  hbT hc => exact IH1 _ _ ⟨hPs, hbT⟩ hc
      | iteFalse hbF hc => exact IH2 _ _ ⟨hPs, hbF⟩ hc
  | whl _ IH =>
      exact while_valid _ IH
  | conseq hPP' _ hQQ' IH =>
      intro s t hP's hBig
      exact hQQ' _ (IH _ _ (hPP' _ hP's) hBig)

-- Exemplos de Derivações

-- Exemplo 1: regra de atribuição usada diretamente.
-- HoareTriple (assub Q "x" (.num 5)) ("x" ::= .num 5) Q
example : {{ assub (fun s => s "x" = 5) "x" (.num 5) }}
              ("x" ::= .num 5)
          {{ "x" .==. 5 }} := by
  apply HoareTriple.assign

-- Exemplo 2: consequência + atribuição.
-- { True } (x := 0) { s.x = 0 }
example : {{ (fun _ => True) }}
            ("x" ::= .num 0)
          {{ (fun s => s "x" = 0) }} := by
  apply conseq_pre
  swap
  · apply HoareTriple.assign
  · intro s _
    simp [assub, State.update, aeval]

-- Exemplo 3: incremento de variável.
-- { s.x = n } (x := x + 1) { s.x = n + 1 }
example (n : ℕ) :
    {{ "x" .==. n }}
       ("x" ::= .add (.var "x") (.num 1))
      {{ "x" .==. n + 1 }} := by
  apply conseq_pre
  swap
  · apply HoareTriple.assign
  · intro s hs
    simp [aequal, assub, State.update, aeval] at *
    assumption

-- Exemplo 4: laço com guarda sempre falsa (body inacessível).
-- { True } (while false do skip) { True }
-- O .whl dá { True } while ff skip { True ∧ ff=false };
-- conseq_post enfraquece a pós para { True }.
example : {{ (fun _ => True) }}
            (.whl .ff .skip)
          {{ (fun _ => True) }} := by
  apply conseq_post
  · apply HoareTriple.whl
    apply conseq_pre
    swap
    · apply HoareTriple.skip
    · intro s ⟨_, hF⟩
      trivial
  · intro _ h
    exact h.1

-- Exemplo 5: sequência de duas atribuições.
-- { True } (x := 1 ;; y := 2) { s.x = 1 ∧ s.y = 2 }
-- A asserção intermediária é (fun s => s "x" = 1).
example :   {{ (fun _ => True) }}
              (("x" ::= .num 1) ;;
               ("y" ::= .num 2))
            {{ ("x" .==. 1) .&. ("y" .==. 2) }} := by
  apply HoareTriple.seq (Q := "x" .==. 1)
  · apply conseq_pre
    swap
    · apply HoareTriple.assign
    · intro s _; simp [aequal, assub, State.update, aeval]
  · apply conseq_pre
    swap
    · apply HoareTriple.assign
    · intro s hs
      simp only [ aand, aequal, assub
                , State.update, aeval] at *
      have hne : ("x" : Var) ≠ "y" := by decide
      split_ifs 
      · contradiction 
      · simp [*]

-- Exemplo 6: Troca de valores entre duas variáveis
-- { s "x" = a ∧ s "y" = b }
-- tmp := x; x := y; y := tmp
-- { s "x" = b ∧ s "y" = a }
-- A pré-condição mais fraca das três atribuições em cadeia é (s "y" = b ∧ s "x" = a),
-- que é equivalente (por comutatividade de ∧) à pré-condição dada.
example (a b : ℕ) :
    {{ ("x" .==. a) .&. ("y" .==. b) }}
       (("tmp" ::= .var "x") ;; 
        ("x" ::= .var "y") ;; 
        ("y" ::= .var "tmp"))
    {{ ("x" .==. b) .&. ("y" .==. a) }} := by
  apply conseq_pre
  swap
  · apply HoareTriple.seq
    · apply HoareTriple.seq
      · apply HoareTriple.assign
      · apply HoareTriple.assign
    · apply HoareTriple.assign
  · intro s H
    simp [assub, aequal, aand, State.update, aeval] at *
    simp [H.1, H.2]

-- Exemplo 7: Cálculo de fatorial iterativo
-- { s "n" = n₀ }
-- r := 1; while (n ≠ 0) do (r := r*n; n := n-1)
-- { s "r" = n₀! }
-- Invariante do laço: I s ↔  s "r" * (s "n")! = n₀!
example (n₀ : ℕ) :
    {{ "n" .==. n₀ }}
       (("r" ::= .num 1) ;;
        .whl (.not (.eq (.var "n") (.num 0)))
            (("r" ::= .mul (.var "r") (.var "n")) ;; 
             ("n" ::= .sub (.var "n") (.num 1))
        ))
    {{ "r" .==. n₀.factorial }} := by
  -- Invariante: r * n! = n₀!  (vale na entrada e é preservada pelo corpo)
  let I : Assertion := fun s => 
      s "r" * (s "n").factorial = n₀.factorial
  apply HoareTriple.seq (Q := I)
  · -- { n = n₀ } r := 1 { I }
    apply conseq_pre
    swap
    · apply HoareTriple.assign
    · intro s hs
      simp [aequal, assub, State.update, aeval, I] at *
      simp [*]
  · -- { I } while (n ≠ 0) do corpo { r = n₀! }
    apply conseq_post
    · apply HoareTriple.whl
      apply conseq_pre
      swap
      · -- corpo: { I ∧ n≠0 } r:=r*n ;; n:=n-1 { I }
        apply HoareTriple.seq
        · apply HoareTriple.assign
        · apply HoareTriple.assign
      · intro s ⟨hI, hbT⟩
        replace hbT : s "n" ≠ 0 := by
          intro h
          have : (!(s "n" == 0) : Bool) = true := hbT
          rw [h] at this; simp at this
        have hrn : ("r" : Var) ≠ "n" := by decide
        have hnr : ("n" : Var) ≠ "r" := by decide
        simp only [assub, State.update, aeval, hrn, hnr, ite_false, ite_true, I]
        have hfact : s "n" * (s "n" - 1).factorial = (s "n").factorial :=
          match s "n", hbT with
          | Nat.succ k, _ => by simp [Nat.factorial_succ]
        calc s "r" * s "n" * (s "n" - 1).factorial
            = s "r" * (s "n" * (s "n" - 1).factorial) := by ring
          _ = s "r" * (s "n").factorial               := by rw [hfact]
          _ = n₀.factorial                            := hI
    · -- pós-condição: I s ∧ n=0 → s "r" = n₀!
      intro s ⟨hI, hbF⟩
      replace hbF : s "n" = 0 := by
        cases hn : s "n" with
        | zero   => rfl
        | succ k =>
          have h1 : (!(s "n" == 0) : Bool) = false := hbF
          simp [hn] at h1
      simp [hbF, I] at hI
      simp [aequal, aeval, *] at *

