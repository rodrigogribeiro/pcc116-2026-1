import Mathlib.Data.Nat.Basic
import Plausible

set_option autoImplicit false
set_option tactic.hygienic false

/-!
  # Aula 05 – Classes de Tipos e 
  Testes Baseados em Propriedades -/

/-- Interface para tipos que podem ser 
    exibidos como String. -/

class Mostravel (α : Type) where
  mostrar : α → String

-- Instância para Nat
instance : Mostravel Nat where
  mostrar n := s!"Nat({n})"

-- Instância para Bool
instance : Mostravel Bool where
  mostrar b := if b then "verdadeiro" 
               else "falso"

-- Instância paramétrica: par de tipos mostráveis
instance {α β : Type} 
         [Mostravel α] 
         [Mostravel β] : Mostravel (α × β) where
  mostrar p := 
      s!"( {Mostravel.mostrar p.1}, {Mostravel.mostrar p.2})"

-- Instância paramétrica: lista de tipo mostrável
instance {α : Type} 
         [Mostravel α] : Mostravel (List α) where
  mostrar xs :=
    "[" ++ String.intercalate ", " 
               (xs.map Mostravel.mostrar) ++ "]"

#eval Mostravel.mostrar (42 : Nat)
#eval Mostravel.mostrar true
#eval Mostravel.mostrar ((3 : Nat), false)
#eval Mostravel.mostrar ([1, 2, 3] : List Nat)

-- Função polimórfica que usa a restrição [Mostravel α]
def mostrarTodos {α : Type} 
                [Mostravel α] 
                (xs : List α) : List String :=
  xs.map Mostravel.mostrar

#eval mostrarTodos ([1, 2, 3] : List Nat)


-- BEq: igualdade decidível booleana
#check @BEq.beq     -- α → α → Bool
#eval  (3 : Nat) == 3   -- true
#eval  (3 : Nat) == 4   -- false

-- Ord: comparação com três resultados
#check @Ord.compare  -- α → α → Ordering
#eval  compare (2 : Nat) 5   -- Ordering.lt
#eval  compare (5 : Nat) 5   -- Ordering.eq
#eval  compare (7 : Nat) 5   -- Ordering.gt

-- ToString: usado em interpolações s!"..."
#eval toString (42 : Nat)
#eval toString true

-- Aritmética: Add, Mul, Sub, Div
#check @Add.add   -- α → α → α
#check @Mul.mul   -- α → α → α

-- Identidades aritméticas
#check @Zero.zero  -- α
#check @One.one    -- α


-- Z/2Z: inteiros módulo 2 (corpo de dois elementos)
inductive Mod2 : Type where
  | zero : Mod2
  | one  : Mod2
  deriving Repr, DecidableEq

namespace Mod2

def add : Mod2 → Mod2 → Mod2
  | .zero, x    => x
  | x,    .zero => x
  | .one, .one  => .zero

def mul : Mod2 → Mod2 → Mod2
  | .one, .one => .one
  | _,    _    => .zero

end Mod2

-- Registro nas classes aritméticas padrão
instance : Add  Mod2 where add  := Mod2.add
instance : Mul  Mod2 where mul  := Mod2.mul
instance : Zero Mod2 where zero := .zero
instance : One  Mod2 where one  := .one

#eval (0 : Mod2) + 0    -- Mod2.zero
#eval (0 : Mod2) + 1    -- Mod2.one
#eval (1 : Mod2) + 1    -- Mod2.zero   (1 + 1 = 0 em Z/2Z)
#eval (1 : Mod2) * 0    -- Mod2.zero
#eval (1 : Mod2) * 1    -- Mod2.one


/-- Um monóide é um conjunto com operação associativa e elemento neutro. -/
class Monóide (α : Type) where
  neutro : α
  op : α → α → α
  neutro_op : ∀ (a : α), op neutro a = a
  op_neutro : ∀ (a : α), op a neutro = a
  op_assoc : ∀ (a b c : α), 
    op a (op b c) = op (op a b) c

-- Nat com adição forma um monóide
instance : Monóide Nat where
  neutro    := 0
  op        := (· + ·)
  neutro_op := by intro; simp
  op_neutro := by intro; simp
  op_assoc  := by intros; omega

-- Mod2 com adição forma um monóide
instance : Monóide Mod2 where
  neutro    := .zero
  op        := Mod2.add
  neutro_op := by intro a; cases a <;> rfl
  op_neutro := by intro a; cases a <;> rfl
  op_assoc  := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

-- Listas com concatenação formam um monóide
instance {α : Type} : Monóide (List α) where
  neutro    := []
  op        := (· ++ ·)
  neutro_op := by intro; simp
  op_neutro := by intro; simp
  op_assoc  := by intros; simp [List.append_assoc]


-- `deriving` pede ao Lean que gere instâncias automaticamente

structure Ponto where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq

#eval Ponto.mk 3 4
#eval Ponto.mk 1 2 == Ponto.mk 1 2   -- true
#eval Ponto.mk 1 2 == Ponto.mk 1 3   -- false

inductive Cor where
  | vermelho
  | verde
  | azul
  deriving Repr, BEq, DecidableEq, Inhabited

#eval (default : Cor) -- primeiro construtor
#eval Cor.vermelho == Cor.verde -- false
#eval Cor.azul == Cor.azul    -- true

/-!
  ## Functor, Applicative e Monad

  Estas classes generalizam "computação com contexto":
  - Functor     – aplica uma função pura dentro do contexto.
  - Applicative – combina contextos independentes.
  - Monad       – encadeia computações dependentes dentro do contexto.
-/

-- Tipo análogo a Option/Maybe: representa um valor que pode estar ausente.
inductive Talvez (α : Type) : Type where
  | nada : Talvez α
  | algo : α → Talvez α
  deriving Repr

namespace Talvez

instance : Functor Talvez where
  map f
    | .nada   => .nada
    | .algo x => .algo (f x)

#eval (· * 2) <$> (.algo 21 : Talvez Nat)   -- Talvez.algo 42
#eval (· * 2) <$> (.nada   : Talvez Nat)    -- Talvez.nada

instance : Applicative Talvez where
  pure      := .algo
  seq mf mx :=
    match mf with
    | .nada   => .nada
    | .algo f => f <$> mx ()

#eval (pure 7 : Talvez Nat)                           -- Talvez.algo 7
#eval (.algo (· + 10)) <*> (.algo 32 : Talvez Nat)   -- Talvez.algo 42
#eval (.algo (· + 10)) <*> (.nada    : Talvez Nat)   -- Talvez.nada

instance : Monad Talvez where
  bind mx f :=
    match mx with
    | .nada   => .nada
    | .algo x => f x

-- Divisão segura: retorna Nada quando o divisor é zero.
def divSeg (n d : Nat) : Talvez Nat :=
  if d == 0 then .nada else .algo (n / d)

-- Encadeamento explícito com >>=
#eval (.algo 100 : Talvez Nat) >>= (divSeg · 4)   -- Talvez.algo 25
#eval (.algo 100 : Talvez Nat) >>= (divSeg · 0)   -- Talvez.nada
#eval (.nada     : Talvez Nat) >>= (divSeg · 4)   -- Talvez.nada

-- Notação `do` é açúcar sintático para bind: cada `←` vira um >>=.
def calcular (a b c : Nat) : Talvez Nat := do
  let x ← divSeg a b   -- falha aqui se b = 0
  let y ← divSeg x c   -- falha aqui se c = 0
  return y

#eval calcular 100 5 4   -- Talvez.algo 5  (100÷5=20, 20÷4=5)
#eval calcular 100 0 4   -- Talvez.nada    (falha na primeira divisão)
#eval calcular 100 5 0   -- Talvez.nada    (falha na segunda divisão)

end Talvez


/-
  Para testar propriedades sobre Mod2 e Cor, 
  precisamos dizer ao Plausible
  como gerar e simplificar valores desses tipos.
  Isso é feito através das classes Shrinkable e 
  Arbitrary.
-/

-- Shrinkable: como simplificar um valor ao encontrar contraexemplo
instance : Plausible.Shrinkable Mod2 where
  shrink
    | .zero => []        -- .zero já é o mínimo
    | .one  => [.zero]   -- .one simplifica para .zero

instance : Plausible.Shrinkable Cor where
  shrink
    | .vermelho => []
    | .verde    => [.vermelho]
    | .azul     => [.vermelho, .verde]

-- Arbitrary: como gerar valores aleatórios
open Plausible Gen in
instance : Arbitrary Mod2 where
  arbitrary := do
    let b ← chooseAny Bool
    return if b then .one else .zero

open Plausible Gen in
instance : Arbitrary Cor where
  arbitrary := do
    -- choose retorna Gen {a // lo ≤ a ∧ a ≤ hi}; usamos .val para obter o Nat
    let n ← choose Nat 0 2 (by omega)
    return match n.val with
           | 0 => .vermelho
           | 1 => .verde
           | _ => .azul

-- ---- Propriedades algébricas de Mod2 ----

-- Comutatividade da adição
example (a b : Mod2) : a + b = b + a := by
  plausible

-- Associatividade da adição
example (a b c : Mod2) : a + (b + c) = (a + b) + c := by
  plausible

-- Zero é elemento neutro
example (a : Mod2) : a + 0 = a := by
  plausible

-- Todo elemento é seu próprio inverso em Z/2Z
example (a : Mod2) : a + a = 0 := by
  plausible

-- Distributividade da multiplicação sobre a adição
example (a b c : Mod2) : a * (b + c) = a * b + a * c := by
  plausible

-- ---- Propriedades sobre Nat ----

-- max é comutativo
example (a b : Nat) : Nat.max a b = Nat.max b a := by
  plausible

-- max é associativo
example (a b c : Nat) :
    Nat.max (Nat.max a b) c = Nat.max a (Nat.max b c) := by
  plausible

-- max é maior que ambos os argumentos
example (a b : Nat) : Nat.max a b ≥ a ∧ Nat.max a b ≥ b := by
  plausible

-- gcd é comutativo
example (a b : Nat) : Nat.gcd a b = Nat.gcd b a := by
  plausible

-- ---- Propriedades sobre List ----

-- Reverter duas vezes é a identidade
example (xs : List Nat) : xs.reverse.reverse = xs := by
  plausible

-- Reverter preserva o comprimento
example (xs : List Nat) : xs.reverse.length = xs.length := by
  plausible

-- Comprimento da concatenação é a soma dos comprimentos
example (xs ys : List Nat) :
    (xs ++ ys).length = xs.length + ys.length := by
  plausible

-- Reverso da concatenação
example (xs ys : List Nat) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  plausible

-- ---- Execução direta via #eval ----

-- Também é possível rodar os testes diretamente no elaborador
open Plausible in
#eval Testable.check (∀ a b : Mod2, a + b = b + a)

open Plausible in
#eval Testable.check (∀ a b : Nat, Nat.gcd a b = Nat.gcd b a)

-- ---- Exemplo de propriedade falsa ----

-- A propriedade abaixo é falsa; o Plausible encontra um contraexemplo.
-- Descomente para ver a mensagem "Found a counter-example!":
-- example (xs ys : List Nat) : xs ++ ys = ys ++ xs := by
--   plausible



