module TestGenerator where

import System.Environment
import Data.List
import System.IO
import System.Random

import Defs

generate 0 cnt = do
  dice <- (getStdRandom (randomR (1, 2))) :: IO Int
  case dice of
       1 -> return (Memory ("m" ++ (show cnt)), cnt + 1)
       2 -> return (Constant cnt, cnt + 1)

generate n cnt = do
      dice <- (getStdRandom (randomR (1, 4))) :: IO Int
      let label = case dice of
                1 -> "+"
                2 -> "-"
                3 -> "/"
                4 -> "*"
      let left_half = div (n - 1) 2
      let right_half = n - 1 - left_half
      left <- generate left_half (cnt + 1)
      right <- generate right_half (snd left)
      return (Fork label [fst left, fst right], snd right)

main = do
    args <- getArgs
    if length args < 2
      then putStrLn "Usage:\nTestGenerator <numberOfNodes> <out-file>"
      else do
        let numberOfNodes = read (args !! 0)
        handle <- openFile (args !! 1) WriteMode
        res <- generate numberOfNodes 0
        hPrint handle (fst res)
        hClose handle