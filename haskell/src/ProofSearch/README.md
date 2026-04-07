# `proof-search` — REPL de Busca Automática de Provas

Algoritmo construção de demonstrações para a **lógica proposicional
intuicionista**, baseado no cálculo de sequentes sem contraction (Dyckhoff,
1992). Dado um sequente `Γ ⊢ G`, o REPL encontra uma árvore de prova completa ou
informa que a fórmula não é demonstrável.

## Execução

A partir do diretório `haskell/`:

```bash
cabal run proof-search
```

---

## Comandos

| Comando        | Descrição                      |
| -------------- | ------------------------------ |
| `:help`        | Exibe a referência de comandos |
| `:quit` / `:q` | Sai do REPL                    |

Qualquer outra entrada é interpretada como um sequente e pesquisada.

---

## Sintaxe de sequentes

Um sequente tem a forma `Γ ⊢ G`, onde `Γ` é uma lista de hipóteses separadas por
vírgulas e `G` é o objetivo.

```
P -> Q, Q -> R |- P -> R
```

Se o contexto estiver vazio, o travessão pode aparecer sozinho:

```
|- P -> P
```

### Sintaxe de fórmulas

| Notação              | Significado                                   |
| -------------------- | --------------------------------------------- |
| `P`, `Q`, `foo`      | Proposições atômicas (qualquer identificador) |
| `A -> B` ou `A → B`  | Implicação (associa à direita)                |
| `A /\ B` ou `A ∧ B`  | Conjunção (associa à esquerda)                |
| `A \/ B` ou `A ∨ B`  | Disjunção (associa à esquerda)                |
| `Top` ou `⊤`         | Verdade                                       |
| `Bot` ou `⊥`         | Falsidade                                     |
| `( A )`              | Agrupamento                                   |
| `\|-` ou `⊢` ou `=>` | Travessão                                     |

---

## Exemplos

```
proof> |- P -> P
✓  Proof found:

                 ──────────── Ax
                 P ⊢ P
            ──────────────── →-R
            ⊢ P → P
   (2 rule applications)

proof> |- (P /\ Q) -> (Q /\ P)
✓  Proof found:

proof> P -> Q, Q -> R |- P -> R
✓  Proof found:

proof> |- P \/ (P -> Bot)
✗  Not provable in intuitionistic propositional logic.
```

O último exemplo mostra que o **princípio do terceiro excluído** não é
demonstrável na lógica intuicionista.

---

## Regras de inferência (G4ip)

| Regra    | Descrição                                                     |
| -------- | ------------------------------------------------------------- |
| `Ax`     | Axioma: objetivo atômico pertence a `Γ`                       |
| `⊤-R`    | Prova `⊤`                                                     |
| `⊥-L`    | `⊥` no contexto fecha qualquer objetivo                       |
| `→-R`    | Introdução da implicação                                      |
| `∧-R`    | Prova conjunção (dois subobjetivos)                           |
| `∧-L`    | Decompõe conjunção no contexto                                |
| `∨-L`    | Análise de casos em disjunção no contexto (dois subobjetivos) |
| `∨-R₁/₂` | Prova disjunção pelo ramo esquerdo ou direito                 |
| `L1`     | Modus ponens quando `P` é atômico e `P ∈ Γ`                   |
| `L4`     | Simplifica `⊤→C` para `C`                                     |
| `L0`     | Descarta `⊥→C` (trivialmente verdadeiro)                      |
| `L2`     | Substitui `(A∧B)→C` por `A→B→C`                               |
| `L3`     | Substitui `(A∨B)→C` por `A→C, B→C`                            |
| `L5`     | Regra crítica sem contração para `(A→B)→C`                    |
