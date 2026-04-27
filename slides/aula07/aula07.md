---
author: PCC116 - Lógica aplicada à computação - Prof. Rodrigo Ribeiro
title: Cálculo de Construções
---

# Objetivos

# Objetivos

- Apresentar o **Cálculo de Construções** (CoC), um sistema de tipos que unifica
  tipos e termos em uma única categoria sintática.

# Objetivos

- Situar o CoC na **hierarquia dos Sistemas de Tipos Puros** (PTS / Cubo de
  Barendregt).

# Objetivos

- Descrever as **regras de formação de tipos** do CoC e a noção de **igualdade
  definitional** por redução beta-delta.

# Objetivos

- Apresentar as **codificações de Church** de conectivos lógicos e
  quantificadores no CoC.

# Objetivos

- Descrever a implementação em Haskell do **verificador de tipos** e do **REPL
  com táticas** para construção interativa de provas.

# Motivação

# Motivação

- O STLC separa dois mundos: **termos** (provas) e **tipos** (proposições).

- Tipos não podem depender de termos; termos não podem depender de tipos.

# Motivação

- A lógica de predicados exige **quantificadores**:

$$\forall x : A.\; P(x) \qquad \exists x : A.\; P(x)$$

- Estes não têm representação natural no STLC.

# Motivação

- Precisamos de um sistema capaz de expressar:
  - **polimorfismo** — termos que dependem de tipos;
  - **tipos dependentes** — tipos que dependem de termos;
  - **operadores de tipo** — tipos que dependem de tipos.

# Motivação

- O **Cálculo de Construções** de Coquand e Huet (1988) incorpora todas essas
  formas de dependência em um único sistema coerente.

# Motivação

- O CoC é a base teórica de assistentes de prova como **Coq** e **Lean**.

# O Cubo de Barendregt

# O Cubo de Barendregt

- O **Cubo de Barendregt** organiza oito sistemas de tipos segundo três eixos de
  dependência:

| Eixo           | Dependência                    |
| -------------- | ------------------------------ |
| $\lambda{\to}$ | termos em tipos (STLC)         |
| $\lambda{2}$   | tipos em termos (polimorfismo) |

# O Cubo de Barendregt

- O **Cubo de Barendregt** organiza oito sistemas de tipos segundo três eixos de
  dependência:

| Eixo                          | Dependência                         |
| ----------------------------- | ----------------------------------- |
| $\lambda{\underline{\omega}}$ | tipos em tipos (operadores)         |
| $\lambda{P}$                  | termos em tipos (tipos dependentes) |

# Sistemas de Tipos Puros

# Sistemas de Tipos

- Um **Sistema de Tipos Puro** (PTS) é especificado por uma tripla
  $(\mathcal{S}, \mathcal{A}, \mathcal{R})$:

  - $\mathcal{S}$ — conjunto de **sorts**
  - $\mathcal{A}$ — **axiomas** $(s_1 : s_2)$
  - $\mathcal{R}$ — **regras** $(s_1, s_2, s_3)$ para formação de $\Pi$-tipos

# Sistemas de Tipos

- Para o Cálculo de Construções $\lambda C$:

$$
\mathcal{S} = \{*, \square\}
\qquad
\mathcal{A} = \{* : \square\}
$$

$$
\mathcal{R} = \{(*, *),\; (*, \square),\; (\square, *),\; (\square, \square)\}
$$

- $*$ — sort das **proposições / tipos pequenos**
- $\square$ — sort dos **tipos de tipos** (não habitada por termos)

# Sistemas de Tipos

| Regra $\mathcal{R}$ | Significado                              |
| ------------------- | ---------------------------------------- |
| $(*, *)$            | funções entre termos ($A \to B$)         |
| $(\square, *)$      | polimorfismo ($\forall \alpha{:}*.\; A$) |

# Sistemas de Tipos

| Regra $\mathcal{R}$  | Significado                                    |
| -------------------- | ---------------------------------------------- |
| $(*, \square)$       | tipos dependentes de termos ($\Pi x{:}A.\; B$) |
| $(\square, \square)$ | operadores de tipo ($\Pi \alpha{:}*.\; B$)     |

# Sintaxe

# Sintaxe

- No CoC, **termos e tipos** pertencem à mesma categoria sintática:

$$
t, A, B \;::=\; s \;\mid\; x \;\mid\; t\;t \;\mid\;
            \lambda x{:}A.\, t \;\mid\; \Pi x{:}A.\, B
$$

# Sintaxe

- $s \in \{*, \square\}$ — sorts
- $x$ — variáveis
- $t\;t$ — aplicação
- $\lambda x{:}A.\,t$ — abstração
- $\Pi x{:}A.\,B$ — produto dependente

# Sintaxe

- O tipo **função** $A \to B$ é açúcar sintático para $\Pi x{:}A.\, B$ quando
  $x \notin \mathsf{fv}(B)$.

$$A \to B \;\stackrel{\text{def}}{=}\; \Pi\_\,{:}A.\, B$$

# Sintaxe

- Exemplos de termos e seus tipos:

| Termo                                                    | Tipo                                 |
| -------------------------------------------------------- | ------------------------------------ |
| $*$                                                      | $\square$                            |
| $\lambda \alpha{:}*.\, \lambda x{:}\alpha.\, x$          | $\Pi\alpha{:}*.\, \alpha \to \alpha$ |
| $\Pi\alpha{:}*.\, \alpha \to \alpha$                     | $*$                                  |
| $\lambda \alpha{:}*.\, \Pi\beta{:}*.\, \alpha \to \beta$ | $* \to *$                            |

# Sistema de Tipos

# Sistema de Tipos

- Um **contexto** $\Gamma$ é uma lista de declarações:

$$\Gamma \;::=\; \emptyset \;\mid\; \Gamma,\, x : A \;\mid\; \Gamma,\, x := t : A$$

- $x : A$ — $x$ tem tipo $A$ (hipótese)
- $x := t : A$ — $x$ é definido como $t$ com tipo $A$ (definição; habilita
  delta-redução)

# Sistema de Tipos

- **Axioma** e **variável**:

$$
\dfrac{}{\Gamma \vdash * : \square}
\quad\text{(Ax)}
\qquad
\dfrac{(x : A) \in \Gamma}{\Gamma \vdash x : A}
\quad\text{(Var)}
$$

# Sistema de Tipos

- **Definição** no contexto (delta):

$$
\dfrac{(x := t : A) \in \Gamma}{\Gamma \vdash x : A}
\quad\text{(Def)}
$$

- A redução $x \longrightarrow_\delta t$ é parte da igualdade definitional.

# Sistema de Tipos

- **Produto dependente** (regra de $\mathcal{R}$):

$$
\dfrac{\Gamma \vdash A : s_1 \qquad \Gamma,\, x : A \vdash B : s_2
       \qquad (s_1, s_2) \in \mathcal{R}}
      {\Gamma \vdash \Pi x{:}A.\, B : s_2}
\quad\text{(Pi)}
$$

# Sistema de Tipos

- **Abstração**:

$$
\dfrac{\Gamma \vdash \Pi x{:}A.\, B : s \qquad \Gamma,\, x : A \vdash t : B}
      {\Gamma \vdash \lambda x{:}A.\, t : \Pi x{:}A.\, B}
\quad\text{(Lam)}
$$

# Sistema de Tipos

- **Aplicação**:

$$
\dfrac{\Gamma \vdash f : \Pi x{:}A.\, B \qquad \Gamma \vdash a : A}
      {\Gamma \vdash f\; a : B[x := a]}
\quad\text{(App)}
$$

# Sistema de Tipos

- **Conversão** (igualdade definitional):

$$
\dfrac{\Gamma \vdash t : A \qquad \Gamma \vdash B : s \qquad A =_\beta B}
      {\Gamma \vdash t : B}
\quad\text{(Conv)}
$$

- $A =_\beta B$ — $A$ e $B$ se reduzem ao mesmo normal.

# Redução

# Redução

- **Beta-redução**:

$$(\lambda x{:}A.\, t)\; a \;\longrightarrow_\beta\; t[x := a]$$

- **Delta-redução** (definições):

$$x \;\longrightarrow_\delta\; t \quad\text{quando}\quad (x := t : A) \in \Gamma$$

# Redução

- **Igualdade definitional** $=_\beta$: fecho reflexivo-simétrico-transitivo de
  $\longrightarrow_{\beta\delta}$.

- Para verificar $A =_\beta B$: reduz ambos à **forma normal** e testa
  **alfa-equivalência**.

# Redução

- **Weak head normal form** (WHNF):

$$
\begin{array}{c}
\dfrac{}{s \;\text{em WHNF}} \\
\dfrac{}{x \;\text{em WHNF}} \\
\end{array}
$$

# Redução

- **Weak head normal form** (WHNF):

$$
\begin{array}{c}
\dfrac{}{\lambda x{:}A.\,t \;\text{em WHNF}} \\
\dfrac{}{\Pi x{:}A.\,B \;\text{em WHNF}}
\end{array}
$$

# Redução

- **Weak head normal form** (WHNF):

$$
\dfrac{f \;\text{em WHNF}\quad f \neq \lambda}{f\;a \;\text{em WHNF}}
$$

# Redução

- **Forma normal completa**: após WHNF, reduz recursivamente os subtermos
  (inclusive sob ligadores).

# Codificações de Church

# Codificações de Church

- No CoC, os **conectivos lógicos** são codificados como tipos $\Pi$-dependentes
  — não é necessário estender a sintaxe.

# Codificações de Church

- **Verdade** $\top$:

$$\top \;\stackrel{\text{def}}{=}\; \Pi\alpha{:}*.\, \alpha \to \alpha$$

- Único habitante: $\mathbf{tt} = \lambda\alpha{:}*.\, \lambda x{:}\alpha.\, x$

# Codificações de Church

- **Falsidade** $\bot$:

$$\bot \;\stackrel{\text{def}}{=}\; \Pi\alpha{:}*.\, \alpha$$

- $\bot$ não tem habitantes (ex falso quodlibet):

$$\mathbf{exFalso} : \bot \to \Pi\alpha{:}*.\, \alpha$$

# Codificações de Church

- **Conjunção** $A \wedge B$:

$$A \wedge B \;\stackrel{\text{def}}{=}\; \Pi c{:}*.\, (A \to B \to c) \to c$$

- Introdução: $\lambda c\, f.\, f\, t_A\, t_B$
- Eliminação: $\mathbf{fst} = \lambda p.\, p\;A\;(\lambda a\,b.\, a)$,
  $\mathbf{snd} = \lambda p.\, p\;B\;(\lambda a\,b.\, b)$

# Codificações de Church

- **Disjunção** $A \vee B$:

$$A \vee B \;\stackrel{\text{def}}{=}\; \Pi c{:}*.\, (A \to c) \to (B \to c) \to c$$

- Injeção esquerda: $\lambda c\, f_l\, f_r.\, f_l\, t_A$
- Injeção direita: $\lambda c\, f_l\, f_r.\, f_r\, t_B$

# Codificações de Church

- **Quantificador universal** $\forall x{:}A.\, P(x)$:

$$\forall x{:}A.\, P(x) \;\stackrel{\text{def}}{=}\; \Pi x{:}A.\, P(x)$$

- É o próprio tipo $\Pi$ — nenhuma codificação adicional necessária!

# Codificações de Church

- **Quantificador existencial** $\exists x{:}A.\, P(x)$:

$$\exists x{:}A.\, P(x) \;\stackrel{\text{def}}{=}\; \Pi c{:}*.\, (\Pi x{:}A.\, P(x) \to c) \to c$$

- Introdução com testemunha $a$: $\lambda c\, k.\, k\; a\; p_a$ onde
  $p_a : P(a)$

# Codificações de Church

| Conectivo | Codificação em CoC                |
| --------- | --------------------------------- |
| $\top$    | $\Pi\alpha{:}*.\,\alpha\to\alpha$ |
| $\bot$    | $\Pi\alpha{:}*.\,\alpha$          |

# Codificações de Church

| Conectivo    | Codificação em CoC               |
| ------------ | -------------------------------- |
| $A \to B$    | $\Pi\_{:}A.\,B$                  |
| $A \wedge B$ | $\Pi c{:}*.\,(A\to B\to c)\to c$ |

# Codificações de Church

| Conectivo           | Codificação em CoC                      |
| ------------------- | --------------------------------------- |
| $A \vee B$          | $\Pi c{:}*.\,(A\to c)\to(B\to c)\to c$  |
| $\forall x{:}A.\,P$ | $\Pi x{:}A.\,P$                         |
| $\exists x{:}A.\,P$ | $\Pi c{:}*.\,(\Pi x{:}A.\,P\to c)\to c$ |

# Propriedades do CoC

# Propriedades do CoC

- **Confluência** (teorema de Church-Rosser): se
  $t \twoheadrightarrow_\beta t_1$ e $t \twoheadrightarrow_\beta t_2$, existe
  $t'$ tal que $t_1 \twoheadrightarrow_\beta t'$ e
  $t_2 \twoheadrightarrow_\beta t'$.

# Propriedades do CoC

- **Normalização forte**: todo termo bem-tipado do CoC possui uma forma normal —
  não existem computações infinitas.

- Consequência: o CoC não é Turing-completo (mas suficiente para matemática
  construtiva).

# Propriedades do CoC

- **Consistência lógica**: $\bot$ não é habitado em contexto vazio.

  - Ou seja: não é possível provar $\forall \alpha{:}*.\,\alpha$ sem hipóteses.

# Propriedades do CoC

- **Decidibilidade** da verificação de tipos: dado $\Gamma$ e $t$, é decidível
  determinar se existe $A$ tal que $\Gamma \vdash t : A$.

  - Algoritmo: bidireccional; decidibilidade depende da normalização forte.

# Referências

# Referências

- COQUAND, Thierry; HUET, Gérard. The calculus of constructions. Information and
  Computation, 76(2–3): 95–120, 1988.

# Referências

- BARENDREGT, Henk. Lambda calculi with types. In: ABRAMSKY, S. et al. (eds.).
  Handbook of Logic in Computer Science, vol. 2. Oxford University Press, 1992.

# Referências

- BARENDREGT, Henk. Introduction to generalized type systems. Journal of
  Functional Programming, 1(2): 125–154, 1991.

# Referências

- PIERCE, Benjamin C. Types and Programming Languages. MIT Press, 2002. (Cap.
  29–30: tipos dependentes e PTS)

# Referências

- SORENSEN, Morten; URZYCZYN, Pawel. Lectures on the Curry-Howard Isomorphism.
  Elsevier, 2006.
