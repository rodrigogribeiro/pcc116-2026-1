module CoC.Encode
  ( topTy
  , botTy
  , notTy
  , andTy
  , orTy
  , existsTy
  , builtins
  ) where

import CoC.Syntax.Term

-- Helpers

arr :: Term -> Term -> Term
arr a b = Pi "_" a b

-- | ⊤  ≡  Πα:*. α → α
topTy :: Term
topTy = Pi "a" (Sort Star) (arr (Var "a") (Var "a"))

-- | ⊥  ≡  Πα:*. α
botTy :: Term
botTy = Pi "a" (Sort Star) (Var "a")

-- | ¬A  ≡  A → ⊥
notTy :: Term -> Term
notTy a = arr a botTy

-- | A ∧ B  ≡  Πc:*. (A → B → c) → c
andTy :: Term -> Term -> Term
andTy a b =
  Pi "c" (Sort Star)
    (arr (arr a (arr b (Var "c"))) (Var "c"))

-- | A ∨ B  ≡  Πc:*. (A → c) → (B → c) → c
orTy :: Term -> Term -> Term
orTy a b =
  Pi "c" (Sort Star)
    (arr (arr a (Var "c"))
         (arr (arr b (Var "c")) (Var "c")))

-- | ∃x:A. B  ≡  Πc:*. (Πx:A. B → c) → c
existsTy :: String -> Term -> Term -> Term
existsTy x a b =
  Pi "c" (Sort Star)
    (arr (Pi x a (arr b (Var "c"))) (Var "c"))

-- | Standard proof constructors pre-loaded as definitions.
-- Each entry is (name, definition, type).
builtins :: [(String, Term, Term)]
builtins =
  [ -- ⊤ : *
    ( "True"
    , topTy
    , Sort Star
    )
    -- ⊥ : *
  , ( "False"
    , botTy
    , Sort Star
    )
    -- tt : ⊤   (the canonical proof of ⊤)
    -- tt = λa:*. λx:a. x
  , ( "tt"
    , Lam "a" (Sort Star) (Lam "x" (Var "a") (Var "x"))
    , topTy
    )
    -- exFalso : ⊥ → Πα:*. α
    -- exFalso = λf:⊥. λa:*. f a
  , ( "exFalso"
    , Lam "f" botTy (Lam "a" (Sort Star) (App (Var "f") (Var "a")))
    , arr botTy (Pi "a" (Sort Star) (Var "a"))
    )
    -- and_intro : Πa b:*. a → b → a ∧ b
    -- and_intro = λa b:*. λha:a. λhb:b. λc:*. λf:a→b→c. f ha hb
  , ( "and_intro"
    , Lam "a" (Sort Star)
       (Lam "b" (Sort Star)
         (Lam "ha" (Var "a")
           (Lam "hb" (Var "b")
             (Lam "c" (Sort Star)
               (Lam "f" (arr (Var "a") (arr (Var "b") (Var "c")))
                 (App (App (Var "f") (Var "ha")) (Var "hb")))))))
    , Pi "a" (Sort Star) (Pi "b" (Sort Star)
        (arr (Var "a") (arr (Var "b") (andTy (Var "a") (Var "b")))))
    )
    -- and_fst : Πa b:*. a ∧ b → a
    -- and_fst = λa b:*. λp:a∧b. p a (λha hb. ha)
  , ( "and_fst"
    , Lam "a" (Sort Star)
       (Lam "b" (Sort Star)
         (Lam "p" (andTy (Var "a") (Var "b"))
           (App (App (Var "p") (Var "a"))
                (Lam "ha" (Var "a") (Lam "hb" (Var "b") (Var "ha"))))))
    , Pi "a" (Sort Star) (Pi "b" (Sort Star)
        (arr (andTy (Var "a") (Var "b")) (Var "a")))
    )
    -- and_snd : Πa b:*. a ∧ b → b
  , ( "and_snd"
    , Lam "a" (Sort Star)
       (Lam "b" (Sort Star)
         (Lam "p" (andTy (Var "a") (Var "b"))
           (App (App (Var "p") (Var "b"))
                (Lam "ha" (Var "a") (Lam "hb" (Var "b") (Var "hb"))))))
    , Pi "a" (Sort Star) (Pi "b" (Sort Star)
        (arr (andTy (Var "a") (Var "b")) (Var "b")))
    )
    -- or_inl : Πa b:*. a → a ∨ b
  , ( "or_inl"
    , Lam "a" (Sort Star)
       (Lam "b" (Sort Star)
         (Lam "ha" (Var "a")
           (Lam "c" (Sort Star)
             (Lam "fl" (arr (Var "a") (Var "c"))
               (Lam "fr" (arr (Var "b") (Var "c"))
                 (App (Var "fl") (Var "ha")))))))
    , Pi "a" (Sort Star) (Pi "b" (Sort Star)
        (arr (Var "a") (orTy (Var "a") (Var "b"))))
    )
    -- or_inr : Πa b:*. b → a ∨ b
  , ( "or_inr"
    , Lam "a" (Sort Star)
       (Lam "b" (Sort Star)
         (Lam "hb" (Var "b")
           (Lam "c" (Sort Star)
             (Lam "fl" (arr (Var "a") (Var "c"))
               (Lam "fr" (arr (Var "b") (Var "c"))
                 (App (Var "fr") (Var "hb")))))))
    , Pi "a" (Sort Star) (Pi "b" (Sort Star)
        (arr (Var "b") (orTy (Var "a") (Var "b"))))
    )
  ]
