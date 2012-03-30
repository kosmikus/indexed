{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
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

type PFAST' a = PFAST POne PTwo (Cons a Nil)

fromExpr :: Expr a -> PFAST' a Zero
fromExpr (Const n)   = Fix (LL (Tag PZero (LL (K n))))
fromExpr (Add e1 e2) = Fix (LL (Tag PZero (RR (LL (I (PRight PZero) (JR (fromExpr e1)) :*: I (PRight PZero) (JR (fromExpr e2)))))))
fromExpr (EVar x)    = Fix (LL (Tag PZero (RR (RR (LL (I (PLeft PZero) (JL (Z x))))))))
fromExpr (Let d e)   = Fix (LL (Tag PZero (RR (RR (RR (I (PRight (PSucc PZero)) (JR (fromDecl d)) :*: I (PRight PZero) (JR (fromExpr e))))))))

toExpr :: PFAST' a Zero -> Expr a
toExpr (Fix (LL (Tag PZero (LL (K n)))))                                                                   = Const n
toExpr (Fix (LL (Tag PZero (RR (LL (I (PRight PZero) (JR e1) :*: I (PRight PZero) (JR e2)))))))            = Add (toExpr e1) (toExpr e2)
toExpr (Fix (LL (Tag PZero (RR (RR (LL (I (PLeft PZero) (JL (Z x)))))))))                                  = EVar x
toExpr (Fix (LL (Tag PZero (RR (RR (RR (I (PRight (PSucc PZero)) (JR d) :*: I (PRight PZero) (JR e)))))))) = Let (toDecl d) (toExpr e)

fromDecl :: Decl a -> PFAST' a (Succ Zero)
fromDecl (Assign x e) = Fix (RR (Tag (PSucc PZero) (LL (I (PLeft PZero) (JL (Z x)) :*: I (PRight PZero) (JR (fromExpr e))))))
fromDecl (Seq d1 d2)  = Fix (RR (Tag (PSucc PZero) (RR (LL (I (PRight (PSucc PZero)) (JR (fromDecl d1)) :*: I (PRight (PSucc PZero)) (JR (fromDecl d2)))))))
fromDecl None         = Fix (RR (Tag (PSucc PZero) (RR (RR U))))

toDecl :: PFAST' a (Succ Zero) -> Decl a
toDecl (Fix (RR (Tag (PSucc PZero) (LL (I (PLeft PZero) (JL (Z x)) :*: I (PRight PZero) (JR e))))))                     = Assign x (toExpr e)
toDecl (Fix (RR (Tag (PSucc PZero) (RR (LL (I (PRight (PSucc PZero)) (JR d1) :*: I (PRight (PSucc PZero)) (JR d2))))))) = Seq (toDecl d1) (toDecl d2)
toDecl (Fix (RR (Tag (PSucc PZero) (RR (RR U)))))                                                                       = None

fromAST' :: PTwo ix -> (Cons (Expr a) (Cons (Decl a) Nil)) ix -> PFAST' a ix
fromAST' PZero         (Z e)     = fromExpr e
fromAST' (PSucc PZero) (S (Z d)) = fromDecl d

toAST' :: PTwo ix -> PFAST' a ix -> (Cons (Expr a) (Cons (Decl a) Nil)) ix
toAST' PZero e         = Z (toExpr e)
toAST' (PSucc PZero) d = S (Z (toDecl d))
