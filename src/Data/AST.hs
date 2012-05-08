{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Data.AST where

import Universe
import Data.List


-- AST
infix 1 :=

data Expr a = Const Int
            | Add (Expr a) (Expr a)
            | EVar a
            | Let (Decl a) (Expr a)
  deriving Show

data Decl a = a := Expr a
            | Seq [Decl a]
  deriving Show

data ASTI = ExprI | DeclI

type ExprF = (SUM (SUM UNIT -- we have no K code yet...
                       (PROD (I (R ExprI)) (I (R ExprI))))
                  (SUM (I (L TT))
                       (PROD (I (R DeclI)) (I (R ExprI)))) :: Code (Sum Top ASTI) ASTI)

-- Bring lists to ASTI
type family LiftList1 :: ASTI -> Top
--type instance LiftList1 i = TT

type family LiftList2 :: Top -> ASTI
--type instance LiftList2 TT = ExprI -- ?

type ListAST = (X LiftList1 (Y LiftList2 List) :: Code ASTI ASTI)
{-
type DeclF = (SUM (PROD (I (L TT)) (I (R ExprI)))
                  (COMP ListAST (I (R ExprI)))
                  :: Code (Sum Top ASTI) ASTI)

-- AST family representation
type ASTF = (SUM (PROD (O ExprI) ExprF)
                 (PROD (O DeclI) DeclF)
             :: Code (Sum Top ASTI) ASTI)

type AST = (FIX ASTF :: Code Top ASTI)

data ASTG :: ASTI -> (* -> *) -> * where
  AST_E :: ASTG ExprI Expr
  AST_D :: ASTG DeclI Decl


--type family ASTG (i :: ASTI) :: * -> *
--type instance ASTG ExprI = Expr


-- Conversion functions
data ASTIndex :: Sum Top ASTI -> * where
  ASTIndex :: ASTIndex (L TT)

fromExpr :: ASTG o Expr -> Expr (r TT) -> Interprt AST r o
fromExpr AST_E (Add x y) = I_F (I_L (I_P I_O
                          (I_L (I_R (I_P (I_I (RR (fromExpr AST_E x)))
                                         (I_I (RR (fromExpr AST_E y))))))))

-- sigh
fromDecl :: ASTG o Decl -> Decl (r TT) -> Interprt AST r o
fromDecl AST_D (Seq ds) = I_F (I_R (I_P I_O
                         (I_R (I_C (undefined)))))


data ListASTI :: ASTI -> * where
  ListASTI :: ListASTI DeclI 

fromASTList :: ListASTI o -> [r o] -> Interprt ListAST r o
fromASTList ListASTI l = I_X undefined

fromASTList' :: [a] -> Interprt ListAST (Const a) o
fromASTList' l = I_X undefined

--fromAST :: ASTG o f -> f (r TT) -> Interprt AST r o
--fromAST AST_E (Const x) = I_F (I_L (I_L (I_P I_O (I_L (I_L I_U)))))
-}
