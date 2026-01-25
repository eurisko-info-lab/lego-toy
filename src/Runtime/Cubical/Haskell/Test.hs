{-# LANGUAGE LambdaCase #-}

-- | Test runner for Cubical Runtime tests (Haskell)
module Main where

import Cubical.Runtime

main :: IO ()
main = do
  putStrLn "Running Cubical Standard Tests (Haskell Runtime)"
  putStrLn "============================================="
  runStandardTests
  if allTestsPass
    then putStrLn "\nSUCCESS: All tests passed!"
    else do
      putStrLn "\nFAIL: Some tests failed"
      error "Test failure"
