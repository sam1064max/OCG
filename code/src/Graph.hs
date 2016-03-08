module Graph where

import Defs

import System.IO
import Data.List

generateGraph :: Expr -> String -> IO ()
generateGraph t filename = do
    handle <- openFile filename WriteMode
    hPutStrLn handle "digraph g {"
    case t of
        Register i -> do
            hPutStrLn handle ("n0 [label=\"r" ++ (show i) ++ "\"] ; \n}")
            hClose handle
        Memory m -> do
            hPutStrLn handle ("n0 [label=\"" ++ m ++ "\"] ;}")
            hClose handle
        Constant c -> do
            hPutStrLn handle ("n0 [label=\"" ++ (show c) ++ "\"] ;}")
            hClose handle
        Fork op exs -> do
            hPutStrLn handle ("n0 [label=\"" ++ op ++ "\"] ;")
            foldl (f handle 0) (return 0) exs
            hPutStrLn handle "}\n"
            hClose handle
  where
      generateGraphRec :: Handle -> Expr -> Int -> Int -> IO Int
      generateGraphRec handle (Register i) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"r" ++ (show i) ++ "\"] ;")
          return thisName
      
      generateGraphRec handle (Constant c) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ (show c) ++ "\"] ;")
          return thisName

      generateGraphRec handle (Memory m) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ m ++ "\"] ;")
          return thisName

      generateGraphRec handle (Fork op exs) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ op ++ "\"] ;")
          foldl (f handle thisName) (return thisName) exs

      f handle parent n t = do
          x <- n
          generateGraphRec handle t parent x

generateAnnotatedGraph :: Bool -> [Walk] -> [Instruction] -> AnnotatedExpr -> String -> IO ()
generateAnnotatedGraph isphase2 marked instrs t filename = do
    handle <- openFile filename WriteMode
    hPutStrLn handle "digraph g {"
    case t of
        RegisterAnnotated i annot -> do
            hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
            if not isphase2
                then do (hPutStrLn handle ("n0 [label=\"r" ++ (show i) ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n0 [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"r" ++ (show i) ++ "\"] ;")
                          else do (hPutStrLn handle ("n0 [label=\"r" ++ (show i) ++ "\"] ;"))
                     )
            hPutStrLn handle ("n0 -> node0 [arrowhead=none;style=dotted];")
            hPutStrLn handle ("node0 [shape = record,height=.1,label = \""
              ++ (getCostString (costs annot)) ++ "\"];")
            hPutStrLn handle ("}\n}")
            hClose handle
        ConstantAnnotated c annot -> do
            hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
            if not isphase2
                then do (hPutStrLn handle ("n0 [label=\"" ++ (show c) ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n0 [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"" ++ (show c) ++ "\"] ;")
                          else do (hPutStrLn handle ("n0 [label=\"" ++ (show c) ++ "\"] ;"))
                     )
            hPutStrLn handle ("n0 -> node0 [arrowhead=none;style=dotted];")
            hPutStrLn handle ("node0 [shape = record,height=.1,label = \"" 
              ++ (getCostString (costs annot)) ++ "\"];")
            hPutStrLn handle ("}\n}")
            hClose handle
        MemoryAnnotated m annot -> do
            hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
            if not isphase2
                then do (hPutStrLn handle ("n0 [label=\"" ++ m ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n0 [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"" ++ m ++ "\"] ;")
                          else do (hPutStrLn handle ("n0 [label=\"" ++ m ++ "\"] ;"))
                     )
            hPutStrLn handle ("n0 -> node0 [arrowhead=none;style=dotted];")
            hPutStrLn handle ("node0 [shape = record,height=.1,label = \""
              ++ (getCostString (costs annot)) ++ "\"];")
            hPutStrLn handle ("}\n}")
            hClose handle
        ForkAnnotated op exs annot -> do
            hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
            if not isphase2
                then do (hPutStrLn handle ("n0 [label=\"" ++ op ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n0 [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"" ++ op ++ "\"] ;")
                          else do (hPutStrLn handle ("n0 [label=\"" ++ op ++ "\"] ;"))
                     )
            hPutStrLn handle ("n0 -> node0 [arrowhead=none;style=dotted];")
            hPutStrLn handle ("node0 [shape = record,height=.1,label = \""
              ++ (getCostString (costs annot)) ++ "\"];")
            hPutStrLn handle ("}")
            foldl (f isphase2 marked handle 0) (return 0) (zip exs [0..(length exs) - 1])
            hPutStrLn handle "}\n"
            hClose handle
  where
      generateAnnotatedGraphRec :: Bool -> [Walk] -> Handle -> AnnotatedExpr -> Int -> Int -> IO Int
      
      generateAnnotatedGraphRec isphase2 marked handle (ConstantAnnotated c annot) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
          if not isphase2
                then do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ (show c) ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n" ++ (show thisName) ++ " [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"" ++ (show c) ++ "\"] ;")
                          else do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ (show c) ++ "\"] ;"))
                     )
          hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ (show c) ++ "\"] ;")
          hPutStrLn handle ("n" ++ (show thisName) ++ " -> node" ++ (show thisName) ++ " [arrowhead=none;style=dotted];")
          hPutStrLn handle ("node" ++ (show thisName) ++ " [shape = record,height=.1,label = \""
            ++ (getCostString (costs annot)) ++ "\"];")
          hPutStrLn handle ("}")
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          return thisName

      generateAnnotatedGraphRec isphase2 marked handle (RegisterAnnotated i annot) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
          if not isphase2
                then do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"r" ++ (show i) ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n" ++ (show thisName) ++ " [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"r" ++ (show i) ++ "\"] ;")
                          else do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"r" ++ (show i) ++ "\"] ;"))
                     )
          hPutStrLn handle ("n" ++ (show thisName) ++ " -> node" ++ (show thisName) ++ " [arrowhead=none;style=dotted];")
          hPutStrLn handle ("node" ++ (show thisName) ++ " [shape = record,height=.1,label = \""
            ++ (getCostString (costs annot)) ++ "\"];")
          hPutStrLn handle ("}")
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          return thisName

      generateAnnotatedGraphRec isphase2 marked handle (MemoryAnnotated m annot) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
          if not isphase2
                then do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ m ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n" ++ (show thisName) ++ " [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"" ++ m ++ "\"] ;")
                          else do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ m ++ "\"] ;"))
                     )
          hPutStrLn handle ("n" ++ (show thisName) ++ " -> node" ++ (show thisName) ++ " [arrowhead=none;style=dotted];")
          hPutStrLn handle ("node" ++ (show thisName) ++ " [shape = record,height=.1,label = \""
            ++ (getCostString (costs annot)) ++ "\"];")
          hPutStrLn handle ("}")
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          return thisName

      generateAnnotatedGraphRec isphase2 marked handle (ForkAnnotated op exs annot) parent n = do
          let thisName = n + 1
          hPutStrLn handle ("{\nrank = same;\nrankdir=LR;")
          if not isphase2
                then do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ op ++ "\"] ;"))
                else (if ([] `elem` marked)
                          then do hPutStrLn handle ("n" ++ (show thisName) ++ " [shape=\"box\";style=\"filled\";fillcolor=\"azure2\";label=\"" ++ op ++ "\"] ;")
                          else do (hPutStrLn handle ("n" ++ (show thisName) ++ " [label=\"" ++ op ++ "\"] ;"))
                     )
          hPutStrLn handle ("n" ++ (show thisName) ++ " -> node" ++ (show thisName) ++ " [arrowhead=none;style=dotted];")
          hPutStrLn handle ("node" ++ (show thisName) ++ " [shape = record,height=.1,label = \""
            ++ (getCostString (costs annot)) ++ "\"];")
          hPutStrLn handle ("}")
          hPutStrLn handle ("n" ++ (show parent) ++ " -> n" ++ (show thisName) ++ " [arrowhead=none];")
          foldl (f isphase2 marked handle thisName) (return thisName) (zip exs [0..(length exs) - 1])

      f isphase2 marked handle parent n (t, ind) = do
          x <- n
          let marked1 = filter (\x -> (length x) > 0 ) marked
          let marked2 = map tail (filter (\x -> (head x) == ind ) marked1)
          generateAnnotatedGraphRec isphase2 marked2 handle t parent x

      getCostString [] = ""
      getCostString (x:[]) = if x /= infinity then (show x) else "&#8734;"
      getCostString (x:xs) = (getCostString [x]) ++ "|" ++ (getCostString xs)

      --getInstructionString instrs [] = ""
      --getInstructionString instrs (NoInstruction:[]) = "-"
      --getInstructionString instrs (x:[]) = case (elemIndex x instrs) of
      --                                         Just ind -> (show (ind + 1))
      --                                         Nothing -> "?"
      --getInstructionString instrs (x:xs) =
      --  (getInstructionString instrs [x]) ++ "|" ++ (getInstructionString instrs xs)