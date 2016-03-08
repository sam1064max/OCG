module Main where

import System.Environment
import Data.List
import System.IO
import System.Process

import Defs
import Graph

parseInstruction :: String -> Instruction
parseInstruction s = read s

parseExpressionTree :: String -> Expr
parseExpressionTree s = read s

cover :: Instruction -> Expr -> (Bool, RegSet, MemSet)
cover i s = coverHelper i [] s

coverHelper (NoInstruction) w s = (False, [], [])
coverHelper (Store _ _ _) w s = (True, [w], []) -- Store covers all trees with k = 1, l = 0 and S1 = S
coverHelper (Load _ _ _) w s = (True, [], [w]) -- Load covers all trees with k = 0, l = 1 and T1 = S
coverHelper (LoadConstant _ _ _) w s =
  case s of
    Constant c -> (True, [], [])
    otherwise -> (False, [], [])
coverHelper (RegisterAssign _ (Register _) _) w s = (True, [w], [])
coverHelper (RegisterAssign _ (Memory _) _) w s = (True, [], [w])
coverHelper (RegisterAssign _ (Constant _) _) w s =
  case s of
    Constant c -> (True, [], [w])
    otherwise -> (False, [], [])
coverHelper (RegisterAssign _ (Fork op exs) _) w s = case s of
    Fork ops sxs -> (if (ops == op) && ((length exs) == (length sxs))
                      then (let (_, res, regSet, memSet) = foldl mergeCovers (0, True, [], []) (zip exs sxs)
                            in (res, regSet, memSet))
                      else (False, [], []))
    otherwise -> (False, [], [])
  where
    mergeCovers foldedRes (e, s) = let (current, ok1, regset, memset) = foldedRes
                                       (ok, regset1, memset1) = coverHelper (RegisterAssign 1 e 1) (w ++ [current]) s
                                   in (if not (ok && ok1)
                                           then (current + 1, False, [], [])
                                           else (current + 1, ok && ok1, regset ++ regset1, memset ++ memset1))

initAnnotation n =
  Annotation { costs = replicate (n + 1) infinity
             , instructions = replicate (n + 1) NoInstruction
             , permuts = replicate (n + 1) []
             }

initAnnotatedExprTree :: Int -> Expr -> AnnotatedExpr
initAnnotatedExprTree n (Fork op exs) =
  ForkAnnotated op (map (initAnnotatedExprTree n) exs) (initAnnotation n)
initAnnotatedExprTree n (Register r) = (RegisterAnnotated r) (initAnnotation n)
initAnnotatedExprTree n (Memory m) = (MemoryAnnotated m) (initAnnotation n)
initAnnotatedExprTree n (Constant c) = (ConstantAnnotated c) (initAnnotation n)


updateListAt :: [a] -> Int -> a -> [a]
updateListAt xs ind newVal = (take ind xs) ++ (newVal : (drop (ind + 1) xs)) 


getNonAnnotatedTree :: AnnotatedExpr -> Expr
getNonAnnotatedTree (RegisterAnnotated r _) = Register r
getNonAnnotatedTree (ConstantAnnotated r _) = Constant r
getNonAnnotatedTree (MemoryAnnotated m _) = Memory m
getNonAnnotatedTree (ForkAnnotated op exs _) = Fork op (map getNonAnnotatedTree exs)

phase1 n instructions (RegisterAnnotated r annot) = error "RegisterAnnotated in expression tree in phase 1."
phase1 n instructions t@(MemoryAnnotated m annot) =
  let n = length (costs annot)
      loadinstmaybe = find (\x -> case x of
                                     Load _ _ _ -> True
                                     otherwise -> False) instructions 
      loadinst = case loadinstmaybe of
                     Just i -> i
                     otherwise -> error "Load instruction not found in instruction set."
      loadinstcost = case loadinst of
                         Load _ _ c -> c
                         otherwise -> error "?"
  in MemoryAnnotated m 
         Annotation { costs = 0 : (replicate (n - 1) loadinstcost)
                    , instructions = NoInstruction : (replicate (n - 1) loadinst)
                    , permuts = replicate (n + 1) []
                    }
phase1 n instructions t@(ConstantAnnotated c annot) =
  let n = length (costs annot)
      loadinstmaybe = find (\x -> case x of
                                     LoadConstant _ _ _ -> True
                                     otherwise -> False) instructions 
      loadinst = case loadinstmaybe of
                     Just i -> i
                     otherwise -> error "LoadConstant instruction not found in instruction set."
      loadinstcost = case loadinst of
                         LoadConstant _ _ c -> c
                         otherwise -> error "?"
      storeinstmaybe = find (\x -> case x of
                                     Store _ _ _ -> True
                                     otherwise -> False) instructions 
      storeinst = case storeinstmaybe of
                     Just i -> i
                     otherwise -> error "Store instruction not found in instruction set."
      storeinstcost = case storeinst of
                         Store _ _ c -> c
                         otherwise -> error "?"
  in ConstantAnnotated c 
         Annotation { costs = (storeinstcost + loadinstcost) : (replicate (n - 1) loadinstcost) --load + store cost in c(0)
                    , instructions = storeinst : (replicate (n - 1) loadinst)
                    , permuts = replicate (n + 1) []
                    }

phase1 n ins t@(ForkAnnotated op exs annot) =
    let t1 = ForkAnnotated op (map (phase1 n ins) exs) annot
    in phase1AtNode n ins t1
  where
    phase1AtNode :: Int -> [Instruction] -> AnnotatedExpr -> AnnotatedExpr
    phase1AtNode n instructions (RegisterAnnotated _ _) = error "RegisterAnnotated in expression tree in phase 1."
    phase1AtNode n instructions t@(MemoryAnnotated _ _) = t -- already calculated
    phase1AtNode n instructions t@(ConstantAnnotated _ _) = t --already calculated
    phase1AtNode n [] t@(ForkAnnotated op exs annot) =
        --done with all the instructions
        let annot1 = considerStorePossibility annot
        in ForkAnnotated op exs (considerLoadPossibility annot1)
    phase1AtNode n instructions@(x:xs) t@(ForkAnnotated op exs _) =
        let (result, regSet, memSet) = cover x (getNonAnnotatedTree t)
        in if (not result)
               then phase1AtNode n xs t --try the next instruction
               else (let t1 = (ForkAnnotated op exs (calculateCost x regSet memSet t))
                     in phase1AtNode n xs t1) --try the next instruction
  
    considerStorePossibility annot =
      let costs1 = costs annot
          instrs1 = instructions annot
          perms1 = permuts annot
          c0 = head costs1
          cn = costs1 !! n
          storeinstmaybe = find (\x -> case x of
                                         Store _ _ _ -> True
                                         otherwise -> False) ins 
          storeinst = case storeinstmaybe of
                         Just i -> i
                         otherwise -> error "Store instruction not found in instruction set."
          storeinstcost = case storeinst of
                             Store _ _ c -> c
                             otherwise -> error "?"
          in (if c0 > (cn + 1)
                then annot {costs = updateListAt costs1 0 (cn + storeinstcost)
                                , instructions = updateListAt instrs1 0 storeinst
                                , permuts = updateListAt perms1 0 []}
                else annot)

    considerLoadPossibility annot =
      let costs1 = costs annot
          c0 = head costs1
          instrs1 = instructions annot
          perms1 = permuts annot
          loadinstmaybe = find (\x -> case x of
                                     Load _ _ _ -> True
                                     otherwise -> False) ins 
          loadinst = case loadinstmaybe of
                        Just i -> i
                        otherwise -> error "Load instruction not found in instruction set."
          loadinstcost = case loadinst of
                            Load _ _ c -> c
                            otherwise -> error "?"
      in ( annot
           { costs = map (\x -> min x (c0 + 1)) costs1
           , instructions = map (\(x, y) -> if (x > (c0 + loadinstcost)) then loadinst else y) (zip costs1 instrs1)
           , permuts = map (\(x, y) -> if (x > (c0 + loadinstcost)) then [] else y) (zip costs1 perms1)
           }
         )

    phase1AtWalk :: Walk -> AnnotatedExpr -> AnnotatedExpr
    phase1AtWalk [] t = t
    phase1AtWalk walk t = phase1AtWalkRec walk t

    phase1AtWalkRec :: Walk -> AnnotatedExpr -> AnnotatedExpr
    phase1AtWalkRec [] t = phase1AtNode n ins t
    phase1AtWalkRec (w:ws) (ConstantAnnotated _ _) = error "Invalid walk"
    phase1AtWalkRec (w:ws) (MemoryAnnotated _ _) = error "Invalid walk"
    phase1AtWalkRec (w:ws) (RegisterAnnotated _ _) = error "Invalid walk"
    phase1AtWalkRec (w:ws) (ForkAnnotated op exs annot) =
        ForkAnnotated op (updateListAt exs w (phase1AtWalkRec ws (exs !! w))) annot

    calculateCost :: Instruction -> RegSet -> MemSet -> AnnotatedExpr -> Annotation
    calculateCost instr regWalks memWalks t@(ForkAnnotated op exs annot) =
      let k = length regWalks
          regCosts = map (getCostForWalk t) regWalks
          permuts = permutations [1..k] 
          permutedCosts = permutations regCosts
          memCosts = map (getCostForWalk t) memWalks
          memoryPartCost = sum ((map (\x -> head x) memCosts))
      in foldr (g instr k n memoryPartCost) annot (zip permuts permutedCosts)

    g instr k n memoryPartCost (perm, permCosts) annot =
      let costs1 = costs annot
          instrs1 = instructions annot
          perms1 = permuts annot
          instrcost = case instr of
                          NoInstruction -> 0
                          Load _ _ c -> c
                          LoadConstant _ _ c -> c
                          Store _ _ c -> c
                          RegisterAssign _ _ c -> c
                          --otherwise -> error "Invalid instruction in calculateCost."
          newCost = calculateForPermutation k n instrcost memoryPartCost permCosts costs1
      in Annotation
         { costs = newCost
         , instructions = map (\(x, y, z) -> if (x <= y) then z else instr) (zip3 costs1 newCost instrs1)
         , permuts = map (\(x, y, z) -> if (x <= y) then z else perm) (zip3 costs1 newCost perms1)
         }

    calculateForPermutation :: Int -> Int -> Cost -> Cost -> [[Cost]] -> [Cost] -> [Cost]
    calculateForPermutation k n instrcost memoryPartCost permutedCost costs =
        foldr (calulateMinCosts instrcost memoryPartCost permutedCost k) costs [k..n]

    calulateMinCosts :: Cost -> Cost -> [[Cost]] -> Int -> Int -> [Cost] -> [Cost]
    calulateMinCosts instrcost memoryPartCost perm k j costs =
        updateListAt costs j (min (costs !! j) ((loopOverI perm j k) + memoryPartCost + instrcost))

    loopOverI :: [[Cost]] -> Int -> Int -> Int
    loopOverI perm j k = foldr (\i y -> y + ((perm !! (i - 1)) !! (j - i + 1))) 0 [1..k]

    getCostForWalk (ForkAnnotated _ _ annot) [] = costs annot
    getCostForWalk (RegisterAnnotated _ annot) [] = costs annot
    getCostForWalk (ConstantAnnotated _ annot) [] = costs annot
    getCostForWalk (MemoryAnnotated _ annot) [] = costs annot
    getCostForWalk (ForkAnnotated op exs _) (w:ws) = getCostForWalk (exs !! w) ws
    getCostForWalk t (w:ws) = error "Wrong walk"

-- Phase 2 : Determining the subtrees to be stored in memory ---------------------------------------------------------

getPermutation :: [a] -> [Int] -> [a]
getPermutation [] (p:ps) = error "Invalid permutation"
getPermutation xs [] = []
getPermutation xs (p:ps) = (xs !! (p - 1)) : (getPermutation xs ps)

phase2 :: Int -> AnnotatedExpr -> [Walk]
phase2 n tree = mark n n [] [] tree

mark :: Int -> Int -> Walk -> [Walk] -> AnnotatedExpr -> [Walk]
mark n j currentwalk storewalks t =
    let annot = (case t of
                       MemoryAnnotated _ annot -> annot
                       ConstantAnnotated _ annot -> annot
                       RegisterAnnotated _ annot -> annot
                       ForkAnnotated _ _ annot -> annot)
        optInstr = (instructions annot) !! j
        optPerm = (permuts annot) !! j
        (result, regSet, memSet) = cover optInstr (getNonAnnotatedTree t)
        permutedRegSet = getPermutation regSet optPerm
        k = length regSet
        l = length memSet
    in if (not result)
           then if j == 0 && optInstr == NoInstruction
                   then storewalks
                   else error $ "Optimal instruction does not cover this node " ++ (show t) ++ "\n" ++ (show optInstr)
           else (if (j == 0) && (isStore optInstr)
                     then let recChanged = mark n n currentwalk storewalks t
                          in recChanged ++ [currentwalk]
                     else let regchanged = foldl (\z (x, i) -> markAtWalkRec x (j - i + 1) currentwalk z t)
                                  storewalks (zip permutedRegSet [1..k])
                          in foldl (\z x -> markAtWalkRec x 0 currentwalk z t) regchanged memSet
                )
  where
    markAtWalkRec [] j currentwalk storewalks t = mark n j currentwalk storewalks t
    markAtWalkRec (x:xs) j currentwalk storewalks (ForkAnnotated _ exs _) =
        markAtWalkRec xs j (currentwalk ++ [x]) storewalks (exs !! x)
    markAtWalkRec (x:xs) _ _ _ (MemoryAnnotated _ _) = error "Invalid walk"
    markAtWalkRec (x:xs) _ _ _ (ConstantAnnotated _ _) = error "Invalid walk"
    markAtWalkRec (x:xs) _ _ _ (RegisterAnnotated _ _) = error "Invalid walk"

-- Phase 3 : Code generation --------------------------------------------------------------------------------------
free :: [RegisterName] -> [RegisterName] -> [RegisterName]
free toFree regList = regList ++ toFree

alloc :: [RegisterName] -> (RegisterName,[RegisterName])
alloc (reg:regList) = (reg,regList)

getNode :: Walk -> AnnotatedExpr -> AnnotatedExpr
getNode [] t = t
getNode (x:xs) (ForkAnnotated _ children _) = getNode xs (children !! x)

buildInstruction :: RegisterName -> Instruction -> AnnotatedExpr -> Instruction
buildInstruction a (RegisterAssign _ expr cost) _ = error "Assign to register but k = 0"
buildInstruction a (Load _ expr cost) (MemoryAnnotated m _) = Load a m cost
buildInstruction a (LoadConstant _ expr cost) (ConstantAnnotated c _) = LoadConstant a c cost
buildInstruction a ins t1 = error "Invalid instruction in k = 0"

buildTree :: Walk -> String -> AnnotatedExpr -> AnnotatedExpr
buildTree [] newName t =
  let annot1 = (case t of
                  MemoryAnnotated _ annot -> annot
                  ConstantAnnotated _ annot -> annot
                  RegisterAnnotated _ annot -> annot
                  ForkAnnotated _ _ annot -> annot)
  in (MemoryAnnotated newName annot1)

buildTree (x:xs) newName (ForkAnnotated op exs costs) =
    let changed = buildTree xs newName (exs !! x)
    in ForkAnnotated op (updateListAt exs x changed) costs
buildTree (x:xs) _ (MemoryAnnotated _ _) = error "Invalid walk in buildTree"
buildTree (x:xs) _ (ConstantAnnotated _ _) = error "Invalid walk in buildTree"
buildTree (x:xs) _ (RegisterAnnotated _ _) = error "Invalid walk in buildTree"

code :: Walk -> Int -> AnnotatedExpr -> [RegisterName] -> [Instruction] -> (RegisterName, [Instruction], [RegisterName])
code x j t reglist generatedCode =
    let node = getNode x t
        annot = (case node of
                       MemoryAnnotated _ annot -> annot
                       ConstantAnnotated _ annot -> annot
                       RegisterAnnotated _ annot -> annot
                       ForkAnnotated _ _ annot -> annot)
        optInstr = (instructions annot) !! j
        optPerm = (permuts annot) !! j
        (result, regSet, _) = cover optInstr (getNonAnnotatedTree node)
        permutedRegSet = getPermutation regSet optPerm
        k = length regSet
    in if (k == 0)
           then let (reg, newReglist) = alloc reglist
                    newInstruction = buildInstruction reg optInstr node
                in (reg, generatedCode ++ [newInstruction], newReglist)
           else let (subtreeRegs, genCode1, reglist1) = foldl (mergeResults j node)
                        ([], generatedCode, reglist) (zip permutedRegSet [1..k])
                    modifiedExpr = modifyExpr optInstr subtreeRegs node permutedRegSet
                    walkForRegName = getSameRegisterWalk optInstr
                    thisReg = extractRegisterFromWalk modifiedExpr walkForRegName
                    regsToFree = filter (/= thisReg) subtreeRegs
                    thisInstr = RegisterAssign thisReg modifiedExpr 0
                in  (thisReg, genCode1 ++ [thisInstr], free regsToFree reglist1)
  where
    mergeResults j node (subtreeRegs, genCode, regList) (walk, i) =
      let (r, is, rs) = code walk (j - i + 1) node regList genCode
      in (subtreeRegs ++ [r], is, rs)

    modifyExpr instr regs tree regWalks =
        case instr of
          Load _ _ _ ->
              case tree of
                  MemoryAnnotated m _ -> Memory m
                  otherwise -> error "Invalid cover"
          LoadConstant _ _ _ ->
              case tree of
                  ConstantAnnotated c _ -> Constant c
                  otherwise -> error "Invalid cover"
          Store _ _ _ -> error "Store instruction in phase 3"
          RegisterAssign _ expr _ -> 
              let modifiedMemoryExpr = modifyMemory expr tree
              in foldl (modifyExprRec) modifiedMemoryExpr (zip regs regWalks)
    
    modifyMemory (Memory m) t@(MemoryAnnotated m1 _) = Memory m1
    modifyMemory (Fork op1 exs1) t@(ForkAnnotated op2 exs2 _) =
        Fork op1 (map (\(x, y) -> modifyMemory x y) (zip exs1 exs2))  
    modifyMemory t t2 = t

    modifyExprRec :: Expr -> (RegisterName, Walk) -> Expr
    modifyExprRec expr (reg, []) = Register reg
    modifyExprRec (Fork op exs) (reg, (x:xs)) =
        let changed = modifyExprRec (exs !! x)  (reg, xs)
        in Fork op (updateListAt exs x changed)
    modifyExprRec (Memory _) (_, (x:xs)) = error "Invalid walk in modifyExprRec"
    modifyExprRec (Constant _) (_, (x:xs)) = error "Invalid walk in modifyExprRec"
    modifyExprRec (Register _) (_, (x:xs)) = error "Invalid walk in modifyExprRec"

    getSameRegisterWalk (Store _ _ _) = error "Store instruction in getSameRegisterWalk"
    getSameRegisterWalk (RegisterAssign r expr _) =
      getSameRegisterWalkInternal r expr []

    getSameRegisterWalkInternal leftRegName (Register r) walk = walk
    getSameRegisterWalkInternal leftRegName (Memory m) walk = walk
    getSameRegisterWalkInternal leftRegName (Fork _ exs) walk =
      let trueChildIndex = foldl (\v (x, y) -> if checkForRegisterName leftRegName y then x else v) 0 (zip [0..(length exs) - 1] exs)
      in getSameRegisterWalkInternal leftRegName (exs !! trueChildIndex) (trueChildIndex : walk)

    checkForRegisterName regName (Register r) = regName == r
    checkForRegisterName regName (Fork _ exs) = foldr (\x y -> y || (checkForRegisterName regName x)) True exs
    checkForRegisterName regName t = False

    extractRegisterFromWalk (Register r) [] = r
    extractRegisterFromWalk (Memory m) [] = error "Invalid walk when extracting register"
    extractRegisterFromWalk (Fork _ _) [] = error "Invalid walk when extracting register"
    extractRegisterFromWalk (Fork _ exs) (x:xs) = extractRegisterFromWalk (exs !! x) xs
    extractRegisterFromWalk t walk = error "Invalid walk when extracting register"

phase3 :: Int -> AnnotatedExpr -> [Walk] -> [Instruction]
phase3 n tree storewalks =
    removeLast (invokecode tree (storewalks ++ [[]]) 1 [1..n] [])
  where
    invokecode t [] i _ generatedCode = generatedCode
    invokecode t (x:xs) i reglist generatedCode = 
      let (a, newGeneratedCode, regList1) = code x n t reglist generatedCode
          newRegList = free [a] regList1
          memName = "m" ++ (show i)
          newInstruction = Store memName a 1
          newTree = buildTree x memName t 
      in (invokecode newTree xs (i + 1) newRegList (newGeneratedCode ++ [newInstruction]))

writeCode :: [Instruction] -> String -> IO ()
writeCode instructions filename = do
    handle <- openFile filename WriteMode
    writeCodeHelper instructions handle
    hClose handle
  where
    writeCodeHelper [] handle = return ()
    writeCodeHelper (x:xs) handle = do
      hPrint handle x
      writeCodeHelper xs handle

verifyRegisterCount instructions n = all (verifyNumberOfRegisters n) instructions
  where
    verifyNumberOfRegisters n x = (getRegCount x) <= n

    getRegCount (Load _ _ _) = 1
    getRegCount (LoadConstant _ _ _ ) = 1
    getRegCount (Store _ _ _) = 1
    getRegCount (RegisterAssign _ (Register _) _) = 1
    getRegCount (RegisterAssign _ (Fork _ exs) _) =
      let res = foldr (\x y -> (getRegCount (RegisterAssign 1 x 0)) + y)  0 exs
      in if res == 0
           then 1
           else res
    getRegCount (RegisterAssign _ expr _) = 0

verifyInstructions xs = (any matchesLoad xs)
    && (any matchesLoadConstant xs) && (any matchesStore xs)
  where
    matchesLoad (Load _ _ _) = True
    matchesLoad _ = False

    matchesLoadConstant (LoadConstant _ _ _) = True
    matchesLoadConstant _ = False

    matchesStore (Store _ _ _) = True
    matchesStore _ = False

verifyPhase1Output :: AnnotatedExpr -> Bool
verifyPhase1Output (ForkAnnotated _ exs annot) =
  let costs1 = costs annot
  in (all (< infinity) costs1) && (foldl (\y x -> y && (verifyPhase1Output x)) True exs)
verifyPhase1Output t =
  let annot1 = (case t of
                  MemoryAnnotated _ annot -> annot
                  ConstantAnnotated _ annot -> annot
                  RegisterAnnotated _ annot -> annot)
      costs1 = costs annot1
  in all (< infinity) costs1

main = do
    args <- getArgs
    if length args < 4
      then putStrLn "Usage:\nMain <numberOfRegisters> <instr-file> <expr-file> <out-file>"
      else do
        content <- readFile (args !! 1)
        let numberOfRegisters = read (args !! 0)
        let instructions = map parseInstruction (lines content)
        content <- readFile (args !! 2)
        let expressionTree = parseExpressionTree content

        if not $ verifyRegisterCount instructions numberOfRegisters
          then putStrLn "Bad machine: Not enough registers to support instructions."
          else if not (verifyInstructions instructions)
                then putStrLn "Bad machine: Instruction set should contain Load, Store and LoadConstant."
                else do
                  let initTree = initAnnotatedExprTree numberOfRegisters expressionTree
                  let costTree = phase1 numberOfRegisters instructions initTree
                  if not (verifyPhase1Output costTree)
                    then putStrLn "Bad expression: Instructions do not cover all nodes of the expression."
                    else do
                      let dotFileName = (args !! 2) ++ ".dot"
                      let pdfFileName = (args !! 2) ++ ".pdf"
                      generateGraph expressionTree dotFileName
                      callProcess "dot" ["-Tpdf", dotFileName, "-o", pdfFileName]
                      putStrLn $ "Expression tree written to : " ++ (pdfFileName)

                      let dotFileName = (args !! 2) ++ "_phase1.dot"
                      let pdfFileName = (args !! 2) ++ "_phase1.pdf"
                      generateAnnotatedGraph False [] instructions costTree dotFileName
                      callProcess "dot" ["-Tpdf", dotFileName, "-o", pdfFileName]
                      putStrLn $ "Phase 1 output written to : " ++ (pdfFileName)
                      
                      let marked = phase2 numberOfRegisters costTree
                      let dotFileName = (args !! 2) ++ "_phase2.dot"
                      let pdfFileName = (args !! 2) ++ "_phase2.pdf"
                      generateAnnotatedGraph True marked instructions costTree dotFileName
                      callProcess "dot" ["-Tpdf", dotFileName, "-o", pdfFileName]
                      putStrLn $ "Phase 2 output written to : " ++ (pdfFileName)
                      
                      let generatedCode = phase3 numberOfRegisters costTree marked
                      writeCode generatedCode (args !! 3)
                      putStrLn $ "Phase 3 output written to : " ++ (args !! 3)
