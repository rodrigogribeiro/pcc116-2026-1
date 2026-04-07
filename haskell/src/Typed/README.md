# `typed` — REPL do Cálculo Lambda Simplesmente Tipado

Interpretador interativo para o **Cálculo Lambda Simplesmente Tipado (STLC)**
com um assistente de provas baseado em táticas. Demonstra a correspondência de
Curry-Howard entre o STLC e a lógica proposicional.

## Execução

A partir do diretório `haskell/`:

```bash
cabal run typed
```

O REPL inicia no **modo baseado em nomes** com um contexto de tipagem vazio.

---

## Comandos — modo de termos

| Comando        | Descrição                                                  |
| -------------- | ---------------------------------------------------------- |
| `:mode named`  | Alterna para entrada com variáveis representadas por nomes |
| `:mode db`     | Alterna para entrada com índices de De Bruijn              |
| `:ctx`         | Exibe o contexto de tipagem atual                          |
| `proof τ`      | Entra no modo de prova por táticas para a proposição `τ`   |
| `:help`        | Exibe a referência de comandos                             |
| `:quit` / `:q` | Sai do REPL                                                |

Qualquer outra entrada é tratada como um termo: será verificado o tipo e
avaliado.

---

## Tipos / Proposições

| Notação       | Significado                        |
| ------------- | ---------------------------------- |
| `⊤` ou `Top`  | Verdade / tipo unitário            |
| `⊥` ou `Bot`  | Falsidade / tipo vazio             |
| `A -> B`      | Implicação / tipo função           |
| `A * B`       | Conjunção / tipo produto           |
| `A + B`       | Disjunção / tipo soma              |
| `P`, `Q`, `R` | Átomos proposicionais (maiúsculas) |

---

## Sintaxe de termos (modo baseado em nomes)

| Construção        | Sintaxe                                  |
| ----------------- | ---------------------------------------- |
| Prova de ⊤        | `unit`                                   |
| Par / conjunção   | `(t, u)`                                 |
| Primeira projeção | `fst t`                                  |
| Segunda projeção  | `snd t`                                  |
| Injeção esquerda  | `inl t as A+B`                           |
| Injeção direita   | `inr t as A+B`                           |
| Análise de casos  | `case t of (inl x => t1 \| inr y => t2)` |
| Ex falso          | `absurd t as τ`                          |
| Abstração lambda  | `\x:A. t`                                |
| Aplicação         | `t u`                                    |

---

## Modo de prova por táticas

Entre no modo de prova com `proof τ`. O prompt muda para `tactic(n)>`, mostrando
o número de objetivos restantes.

| Tática             | Descrição                                                |
| ------------------ | -------------------------------------------------------- |
| `intro x`          | Introduz a hipótese `→` como `x`                         |
| `assumption`       | Fecha o objetivo encontrando uma hipótese correspondente |
| `exact t`          | Fecha o objetivo com o termo de prova explícito `t`      |
| `apply h`          | Aplica a hipótese `h` ao objetivo atual                  |
| `split`            | Divide `A ∧ B` em dois subobjetivos                      |
| `left`             | Prova `A ∨ B` pelo ramo esquerdo                         |
| `right`            | Prova `A ∨ B` pelo ramo direito                          |
| `cases h x y`      | Análise de casos em `h : A ∨ B`                          |
| `trivial`          | Fecha um objetivo `⊤`                                    |
| `absurd h`         | Fecha qualquer objetivo usando `h : ⊥`                   |
| `destruct h h1 h2` | Divide `h : A ∧ B` em `h1 : A` e `h2 : B`                |
| `:qed`             | Finaliza a prova quando não há mais objetivos            |
| `:abandon`         | Descarta a prova em andamento                            |

---

## Exemplos

### Modo de termos

```
ch-named> (\x:P. x)
  Type:      P -> P
  Named:     λx. x
  De Bruijn: λ. 0
  Value (0 steps):
    Named:     λx. x

ch-named> (\x:P*Q. fst x)
  Type:      P * Q -> P

ch-named> inl unit as Top+P
  Type:      ⊤ + P
```

### Modo de táticas — identidade

```
ch-named> proof P -> P
tactic(1)> intro h
tactic(1)> assumption
tactic(0)> :qed
Proof complete!
  Term:  λh. h
  Type:  P -> P
```

### Modo de táticas — silogismo hipotético

```
ch-named> proof (P -> Q) -> (Q -> R) -> P -> R
tactic(1)> intro hpq
tactic(1)> intro hqr
tactic(1)> intro hp
tactic(1)> apply hqr
tactic(1)> apply hpq
tactic(1)> assumption
tactic(0)> :qed
Proof complete!
  Term:  λhpq. λhqr. λhp. hqr (hpq hp)
```
