import Pcc116.Aula11

set_option autoImplicit false
set_option tactic.hygienic false

/- Gerador de Condições de Verificação (VCG) para IMP
 -/

-- Comandos Anotados (ACom)

/-- Comandos IMP anotados: laços carregam um invariante de Hoare. -/
inductive ACom where
  | skip   : ACom
  | assign : Var → AExp → ACom
  | seq    : ACom → ACom → ACom
  | ite    : BExp → ACom → ACom → ACom
  | whl    : Assertion → BExp → ACom → ACom  -- I: invariante, b: guarda, c: corpo

infixl:70 " ;;ₐ " => ACom.seq

/-- Remove as anotações, produzindo um comando IMP ordinário. -/
def erase : ACom → Com
  | .skip        => .skip
  | .assign x a  => .assign x a
  | .seq c₁ c₂   => erase c₁ ;; erase c₂
  | .ite b c₁ c₂ => .ite b (erase c₁) (erase c₂)
  | .whl _ b c   => .whl b (erase c)

-- Pré-condição Mais Fraca  (wp)

/-
  wp c Q  é a pré-condição mais fraca de c para a pós-condição Q:
  a condição mínima sobre o estado inicial que garante Q após c.

  Propriedade central (provada pelo vcg_sound abaixo):
      vc c Q  →  {{ wp c Q }} (erase c) {{ Q }}

  Para laços anotados, o wp do laço É o invariante I:
  o invariante captura exatamente o que precisa valer antes de entrar no laço.
-/
def wp : ACom → Assertion → Assertion
  | .skip, Q => Q
  | .assign x a, Q => assub Q x a
  | .seq c₁ c₂, Q => wp c₁ (wp c₂ Q)
  | .ite b c₁ c₂, Q => fun s =>
      (beval s b = true  → wp c₁ Q s) ∧
      (beval s b = false → wp c₂ Q s)
  | .whl I _ _,   _ => I   -- o invariante é a pré-condição mais fraca do laço

-- Condições de Verificação  (vc)

/-
  vc c Q  é a conjunção de todas as condições de verificação de c
  com pós-condição Q.

  Para skip e atribuição não há VCs não-triviais (retorna True).
  Para sequência e condicional, as VCs são herdadas dos sub-comandos.
  Para laços, surgem duas VCs obrigatórias:
    (a) o corpo preserva o invariante:  I ∧ b  →  wp(corpo, I)
    (b) a saída implica a pós-condição: I ∧ ¬b →  Q
  mais as VCs internas do próprio corpo.
-/
def vc : ACom → Assertion → Prop
  | .skip,        _ => True
  | .assign _ _,  _ => True
  | .seq c₁ c₂,   Q => vc c₁ (wp c₂ Q) ∧ vc c₂ Q
  | .ite _ c₁ c₂, Q => vc c₁ Q ∧ vc c₂ Q
  | .whl I b c,   Q =>
      (∀ s, I s ∧ beval s b = true  → wp c I s) ∧   
      -- corpo preserva I
      (∀ s, I s ∧ beval s b = false → Q s) ∧   
      -- saída implica Q
      vc c I                                           
      -- VCs internas do corpo

-- Correção do VCG

/-- Lema central: se vc c Q vale, a tripla
    {{ wp c Q }} erase(c) {{ Q }}
    é derivável na Lógica de Hoare de Aula11. -/
theorem vcg_sound : ∀ (c : ACom) (Q : Assertion),
    vc c Q → {{ wp c Q }} (erase c) {{ Q }} := by
  intro c
  induction c with
  | skip =>
      intro Q _
      constructor
  | assign x a =>
      intro Q _
      constructor
  | seq c₁ c₂ IH₁ IH₂ =>
      intro Q ⟨h₁, h₂⟩
      -- wp(c₁;;c₂, Q) = wp(c₁, wp(c₂,Q))
      -- { wp(c₁, wp(c₂,Q)) } c₁ { wp(c₂,Q) }  por IH₁
      -- { wp(c₂,Q) }         c₂ { Q }           por IH₂
      constructor 
      · apply IH₁ ; assumption 
      · apply IH₂ ; assumption 
  | ite b c₁ c₂ IH₁ IH₂ =>
      intro Q ⟨h₁, h₂⟩
      apply HoareTriple.ite
      · -- { wp(ite) ∧ b=true } c₁ { Q }
        -- wp(ite) ∧ b=true → wp(c₁, Q)  (por definição de wp para ite)
        apply conseq_pre _ (IH₁ _ h₁)
        intro s ⟨hwp, hbT⟩
        simp only [wp] at hwp
        exact hwp.1 hbT
      · -- { wp(ite) ∧ b=false } c₂ { Q }
        apply conseq_pre _ (IH₂ _ h₂)
        intro s ⟨hwp, hbF⟩
        simp only [wp] at hwp
        apply hwp.2 ; assumption
  | whl I b c IH =>
      intro Q ⟨hbody, hpost, hvc⟩
      -- IH: vc c I → HoareTriple (wp c I) (erase c) I
      -- hbody: I ∧ b → wp c I   (consequência para a pré do corpo)
      -- hpost:  I ∧ ¬b → Q      (consequência para a pós do laço)
      --
      -- 1. { I ∧ b } erase(c) { I }   por conseq_pre + IH
      -- 2. { I } while b erase(c) { I ∧ ¬b }  por regra whl
      -- 3. { I } while b erase(c) { Q }        por conseq_post + hpost
      apply conseq_post 
      apply HoareTriple.whl
      · apply conseq_pre 
        · 
          rintro s ⟨H1, H2⟩
          apply hbody 
          simp [wp] at H1 
          constructor <;> assumption 
        · simp [wp] at * 
          apply IH 
          assumption 
      · rintro s ⟨ H1, H2 ⟩ 
        simp [wp] at *
        apply hpost <;> assumption

/-- Correção semântica: se P → wp c Q e vc c Q, 
    então {{* P *}} erase(c) {{* Q *}} é válida. -/
theorem vcg_correct (P : Assertion) (c : ACom) (Q : Assertion)
    (hpre : ∀ s, P s → wp c Q s)
    (hvc : vc c Q) : {{* P *}} (erase c) {{* Q *}} :=
  hoare_sound (conseq_pre hpre (vcg_sound c Q hvc))

-- Exemplos

-- Exemplo 1: atribuição simples via VCG
-- { True } x := 5 { s "x" = 5 }
-- vc = True; basta provar True → assub (s"x"=5) "x" 5  ≡  (5=5)
example : {{* (fun _ => True) *}}
             (erase (.assign "x" (.num 5)))
          {{* "x" .==. 5 *}} := by 
  apply vcg_correct 
  · intros s H1 
    simp [wp, aequal, assub, aeval, State.update]
  · simp [vc]
  

-- Exemplo 2: sequência de atribuições
-- { True } x:=0 ;; x:=x+1 { s "x" = 1 }
-- vc = True ∧ True;  basta provar True → wp = (0+1 = 1)
example : {{* (fun _ => True) *}}
            (erase (.assign "x" (.num 0) ;;ₐ 
                    .assign "x" (.add (.var "x") (.num 1))
                    ))
          {{* "x" .==. 1 *}} := by 
  apply vcg_correct 
  · intros s _ 
    simp [wp, assub, aequal, aeval, State.update]
  · simp [vc] 

-- Exemplo 3: laço while com guarda sempre falsa
-- { True } while false do skip { True }
-- Invariante I = fun _ => True
-- VC1 (corpo preserva I): True ∧ false=true → True  ← vacuamente verdadeira
-- VC2 (saída → Q):        True ∧ false=false → True ← trivialmente verdadeira
example : {{* (fun _ => True) *}}
             (erase (.whl (fun _ => True) .ff .skip))
          {{* (fun _ => True) *}} := by 
  apply vcg_correct 
  · intros s _ 
    simp [wp] 
  · simp [vc] 
    intros s H1 
    simp [beval, wp] at * 
   

-- Exemplo 4: laço de contagem regressiva
-- { True } while (x ≠ 0) do x:=x-1 { s "x" = 0 }
-- Invariante I = fun _ => True  (apenas correção parcial)
-- VC1: True ∧ x≠0 → wp(x:=x-1, True) = True          ← trivial
-- VC2: True ∧ x=0 → s "x" = 0                         ← segue da guarda
example : {{* (fun _ => True) *}}
            (erase (.whl (fun _ => True)
                      (.not (.eq (.var "x") (.num 0)))
                      (.assign "x" (.sub (.var "x") 
                                         (.num 1)))
            ))
          {{* "x" .==. 0 *}} := by 
  apply vcg_correct 
  · intros s _  
    simp [wp] 
  · simp [vc] 
    constructor 
    · intros s H1 
      simp [wp, beval, assub] at * 
    · intros s H1 
      simp [beval, aequal, aeval] at *
      assumption 

-- Exemplo 5: fatorial via VCG
-- { s "n" = n₀ }  r:=1; while(n≠0) do (r:=r*n; n:=n-1)  { s "r" = n₀! }
-- Invariante: I s = s "r" * (s "n")! = n₀!
--
-- O VCG gera apenas duas VCs não-triviais:
--   VC1 (corpo preserva I): s "r" * s "n" * (s "n"-1)! = n₀!  quando s "n" ≠ 0
--   VC2 (saída → Q):        s "r" * 0! = n₀!  ↔  s "r" = n₀!  quando s "n" = 0
-- Todas as decomposições estruturais ficam a cargo de vcg_correct.
example (n₀ : ℕ) :
    {{* (fun s => s "n" = n₀) *}}
        (erase (.assign "r" (.num 1) ;;ₐ
          .whl (fun s => 
            s "r" * (s "n").factorial = n₀.factorial)
               (.not (.eq (.var "n") (.num 0)))
                (.assign "r" (.mul (.var "r") 
                                   (.var "n")) ;;ₐ
                 .assign "n" (.sub (.var "n") 
                                   (.num 1)))
        ))
    {{* "r" .==. n₀.factorial *}} := by
  apply vcg_correct
  · -- P → wp c Q:  s "n" = n₀  →  assub I "r" 1 s  =  (s "n")! = n₀!
    intro s hs
    simp [wp, assub, State.update, aeval, hs]
  · -- VCs do laço:
    -- vc (.seq (.assign "r" 1) (.whl I b body)) Q
    --   = True ∧ (VC1 ∧ (VC2 ∧ (True ∧ True)))
    -- O primeiro True é vc (.assign "r" 1) I, provado inline com `trivial`.
    simp [vc]
    constructor
    · -- VC1: I ∧ n≠0 → wp(corpo, I)
      -- wp(corpo, I) = assub (assub I "n" (n-1)) "r" (r*n)
      --             ≡  s "r" * s "n" * (s "n"-1)! = n₀!
      intro s H1 H2 
      simp [wp, assub, State.update, aeval, beval] at *
      rw [<- H1] 
      cases H3 : s "n"
      · contradiction
      · simp at *
        simp [Nat.factorial, H3] at * 
        linarith
    · -- VC2: I ∧ n=0 → r = n₀!
      -- Não usar simp [beval, aeval] em hbF: a direção fica ambígua com .not.
      -- Em vez disso, case-split em s "n" com hipótese h nomeada.
      intros s H1 H2 
      simp [beval, aeval, aequal] at *
      simp [H2] at *
      assumption 

example : {{* assub (fun s => s "x" = 5) "x" (.num 5) *}}
              (erase (.assign "x" (.num 5)))
          {{* "x" .==. 5 *}} := by 
  apply vcg_correct 
  · intros s H1 
    simp [assub, wp, State.update, aeval, aequal] at *
  · simp [vc] 

example : {{* (fun _ => True) *}}
            (erase (.assign "x" (.num 0)))
          {{* "x" .==. 0 *}} := by 
  apply vcg_correct
  · intros s H1 
    simp [wp, assub, aequal, assub, State.update, aeval]
  · simp [vc] 

example (n : ℕ) :
    {{* "x" .==. n *}}
       (erase (.assign "x" (.add (.var "x") (.num 1))))
    {{* "x" .==. n + 1 *}} := by 
  apply vcg_correct
  · intros s H1 
    simp [aequal, wp, assub, State.update, aeval] at *
    assumption
  · simp [vc]

example : {{* (fun _ => True) *}}
            (erase (.whl (fun _ => True) .ff .skip))
          {{* (fun _ => True) *}} := by 
  apply vcg_correct 
  · intros s H1 
    simp [wp] 
  · simp [vc] 
    intros s H1 
    simp [beval] at * 

example : {{* (fun _ => True) *}}
            (erase (.assign "x" (.num 1) ;;ₐ 
                    .assign "y" (.num 2)
            ))
          {{* ("x" .==. 1) .&. ("y" .==. 2) *}} := by 
  apply vcg_correct
  · intros s _ 
    simp [wp, assub, aand, aequal, aeval, State.update]
  · simp [vc]
  
example (a b : ℕ) :
    {{* ("x" .==. a) .&. ("y" .==. b) *}}
      (erase (.assign "tmp" (.var "x") ;;ₐ 
              .assign "x" (.var "y") ;;ₐ 
              .assign "y" (.var "tmp")
             ))
    {{* ("x" .==. b) .&. ("y" .==. a) *}} := by 
  apply vcg_correct
  · intros s H1 
    simp [ wp, aand, aequal, assub
         , aeval, State.update] at *
    rw [H1.1, H1.2]
    simp 
  · simp [vc]
