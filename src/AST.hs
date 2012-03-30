{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module AST where

import Combinators
import Typelevel
import EP

data Expr a = Const Int
            | Add   (Expr a) (Expr a)
            | EVar  a
            | Let   (Decl a) (Expr a)
  deriving (Show)

data Decl a = Assign a (Expr a)
            | Seq    (Decl a) (Decl a)
            | None
  deriving (Show)

-- PFExpr :: Fin 1 + Fin 2 >>> o
type PFExpr =   K Int
            :+: (I (TRight Zero) :*: I (TRight Zero))
            :+: (I (TLeft Zero))
            :+: (I (TRight (Succ Zero)) :*: I (TRight Zero))

-- PFDecl :: Fin 1 + Fin 2 >>> o
type PFDecl =   (I (TLeft Zero) :*: I (TRight Zero))
            :+: (I (TRight (Succ Zero)) :*: I (TRight (Succ Zero)))
            :+: U

-- PFAST :: Fin 1 >>> Fin 2
type PFAST = Fix (Tag Zero PFExpr :+: Tag (Succ Zero) PFDecl)

type PFAST' a = PFAST (Cons a Nil)

fromExpr :: Expr a -> PFAST' a Zero
fromExpr (Const n)   = Fix (LL (Tag (LL (K n))))
fromExpr (Add e1 e2) = Fix (LL (Tag (RR (LL (I (JR (fromExpr e1)) :*: I (JR (fromExpr e2)))))))
fromExpr (EVar x)    = Fix (LL (Tag (RR (RR (LL (I (JL (Z x))))))))
fromExpr (Let d e)   = Fix (LL (Tag (RR (RR (RR (I (JR (fromDecl d)) :*: I (JR (fromExpr e))))))))

toExpr :: PFAST' a Zero -> Expr a
toExpr (Fix (LL (Tag (LL (K n)))))                             = Const n
toExpr (Fix (LL (Tag (RR (LL (I (JR e1) :*: I (JR e2)))))))    = Add (toExpr e1) (toExpr e2)
toExpr (Fix (LL (Tag (RR (RR (LL (I (JL (Z x)))))))))          = EVar x
toExpr (Fix (LL (Tag (RR (RR (RR (I (JR d) :*: I (JR e)))))))) = Let (toDecl d) (toExpr e)

fromDecl :: Decl a -> PFAST' a (Succ Zero)
fromDecl (Assign x e) = Fix (RR (Tag (LL (I (JL (Z x)) :*: I (JR (fromExpr e))))))
fromDecl (Seq d1 d2)  = Fix (RR (Tag (RR (LL (I (JR (fromDecl d1)) :*: I (JR (fromDecl d2)))))))
fromDecl None         = Fix (RR (Tag (RR (RR U))))

toDecl :: PFAST' a (Succ Zero) -> Decl a
toDecl (Fix (RR (Tag (LL (I (JL (Z x)) :*: I (JR e))))))    = Assign x (toExpr e)
toDecl (Fix (RR (Tag (RR (LL (I (JR d1) :*: I (JR d2))))))) = Seq (toDecl d1) (toDecl d2)
toDecl (Fix (RR (Tag (RR (RR U)))))                         = None

fromAST' :: (Cons (Expr a) (Cons (Decl a) Nil)) ix -> PFAST' a ix
fromAST' (Z e)     = fromExpr e
fromAST' (S (Z d)) = fromDecl d

toAST' :: PTwo ix -> PFAST' a ix -> (Cons (Expr a) (Cons (Decl a) Nil)) ix
toAST' PZero e         = Z (toExpr e)
toAST' (PSucc PZero) d = S (Z (toDecl d))
