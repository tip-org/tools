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
  QuickSpecParams <$> bFuns <*> useObs
  where
    bFuns = commaSep <$>
      many (strOption (long "background" <> short 'b' <> metavar "NAME" <> help "Background function"))
    useObs = switch (long "Use observers" <> short 'o' <> help "Using observers to explore codatatypes")

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
         print (SMT.ppTheory [] thy')

