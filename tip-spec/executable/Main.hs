{-# LANGUAGE CPP #-}
#ifdef STACK
{-# LANGUAGE TemplateHaskell #-}
#endif
module Main where

import System.Environment

import Tip.Haskell.Translate
import Options.Applicative
import Tip.QuickSpec
import Tip.Parser (parse)
#ifdef STACK
import Language.Haskell.TH.Syntax
import System.Process
#endif

import qualified Tip.Pretty.SMT as SMT
import Data.List.Split
import Data.Monoid

parseParams :: Parser QuickSpecParams
parseParams =
  QuickSpecParams <$> bFuns <*> bPreds <*> useObs <*> useCompletion <*> size <*> depth <*> testSize <*> observerSize <*> timeout <*> intIsNat <*> onlyRecursiveFunctions
  where
    bFuns = fmap Just (commaSep <$> some (strOption (long "foreground" <> short 'f' <> metavar "NAME" <> help "Foreground function (to explore)"))) <|> pure Nothing
    bPreds = fmap Just (commaSep <$> some (strOption (long "predicates" <> short 'P' <> metavar "NAME" <> help "Predicates (to use as conditions)"))) <|> pure Nothing
    useObs = switch (long "observers" <> short 'o' <> help "Use observers to explore codatatypes")
    useCompletion = switch (long "prune" <> short 'p' <> help "Filter out redundant conjectures")
    size = option auto (long "size" <> short 's' <> help "Maximum term size to explore") <|> pure 7
    depth = option auto (long "depth" <> short 'd' <> help "Maximum term depth to explore") <|> pure maxBound
    testSize = option auto (long "test-size" <> short 'S' <> help "Maximum test case size") <|> pure 20
    observerSize = option auto (long "observer-size" <> short 'O' <> help "Maximum observer size") <|> pure 20
    timeout = fmap Just (option auto (long "exploration-timeout" <> short 'T'<> help "Timeout in seconds to finish exploration")) <|> pure Nothing
    intIsNat = switch (long "int-is-nat" <> help "Integer variables should range only over natural numbers")
    onlyRecursiveFunctions = switch (long "only-recursive-functions" <> help "Only include recursive functions in signature")

commaSep :: [String] -> [String]
commaSep = concatMap (splitOn ",")

optionParser :: Parser (Maybe String, QuickSpecParams)
optionParser =
  (,) <$> parseFile <*> parseParams
  where
    parseFile =
      fmap Just (strArgument (metavar "FILENAME")) <|> pure Nothing

main :: IO ()
main = do
#ifdef STACK
  let pkgdb = $(qRunIO (readProcess "stack" ["exec", "--", "sh", "-c", "echo $GHC_PACKAGE_PATH"] "") >>= lift)

  setEnv "GHC_PACKAGE_PATH" (head (lines pkgdb))
#endif

  (files, params) <-
    execParser $
      info (helper <*> optionParser)
        (fullDesc <>
         progDesc "Speculate conjectures about a TIP problem" <>
         header "tip-spec - conjecture synthesis for TIP problems")
  case files of
    Nothing  -> handle params =<< getContents
    Just "-" -> handle params =<< getContents
    Just f   -> handle params =<< readFile f

handle :: QuickSpecParams -> String -> IO ()
handle params s =
  case parse s of
    Left err  -> error $ "Parse failed: " ++ err
    Right thy ->
      do thy' <- exploreTheory params thy
         print (SMT.ppTheory SMT.tipConfig thy')
