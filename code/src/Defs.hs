module Defs where

type RegisterName = Int
type MemoryName = String
type Op = String
type Cost = Int

type RegSet = [Walk]
type MemSet = [Walk]

type Walk = [Int]

infinity :: Int
infinity = 1000000000000000

data Annotation = Annotation
    { costs :: [Cost]
    , instructions :: [Instruction]
    , permuts :: [[Int]]
    } deriving (Show, Read)

data Expr = Fork Op [Expr] | Register RegisterName | Constant Int | Memory MemoryName deriving (Show, Read, Eq)

data AnnotatedExpr = ForkAnnotated Op [AnnotatedExpr] Annotation
                   | RegisterAnnotated RegisterName Annotation
                   | ConstantAnnotated Int Annotation
                   | MemoryAnnotated MemoryName Annotation deriving (Show, Read)

data Instruction = RegisterAssign RegisterName Expr Cost
                 | Load RegisterName MemoryName Cost
                 | LoadConstant RegisterName Int Cost
                 | Store MemoryName RegisterName Cost
                 | NoInstruction deriving (Read, Eq)

instance Show Instruction where
  show instr = 
    case instr of
        Load r m _ -> ("r" ++ (show r) ++ " <- " ++ m)
        LoadConstant r c _ -> ("r" ++ (show r) ++ " <- " ++ (show c))
        RegisterAssign r expr _ -> ("r" ++ (show r) ++ " <- " ++ (getInfixExpr expr))
        Store m r _ -> (m ++ " <- r" ++ (show r))
        otherwise -> error "Invalid instruction when writing code."

getInfixExpr (Memory m) = m
getInfixExpr (Constant c) = show c
getInfixExpr (Register r) = "r" ++ (show r)
getInfixExpr (Fork op exs) | length exs == 1 =  "(" ++ op ++ " " ++ (getInfixExpr (head exs)) ++ ")"
                           | length exs == 2 =  "(" ++ (getInfixExpr (head exs)) ++ " " ++ op ++ " " ++ (getInfixExpr (exs !! 1)) ++ ")"   
                           | length exs > 2 = "(" ++ op ++ (foldl afterInfix [] (exs)) ++ ")"
  where 
    afterInfix id expr = id ++ " " ++ (getInfixExpr expr)  

isStore ins = case ins of
    Store _ _ _ -> True
    otherwise -> False

removeLast [] = []
removeLast (x:[]) = []
removeLast (x:xs) = x : (removeLast xs)