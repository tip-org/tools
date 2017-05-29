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
  QuickSpecParams <$>
    backgroundFuns <*>
    obsModule <*>
    observerFuns
  where
    backgroundFuns =
      commaSep <$>
      many (strOption (long "background" <> short 'b' <> metavar "NAME" <> help "Background function"))
    obsModule = strOption (long "obs-module" <> short 'm' <> metavar "MODULE-NAME" <> help "Module containing observer functions")
    observerFuns =
      commaSep <$>
      many (explType, obsType, obsFun)
    explType = strOption (long "explType" <> short 'e' <> metavar "TYPE" <> help "Type that requires observer")
    obsType = strOption (long "obsType" <> short 'o' <> metavar "TYPE" <> help "Observable type")
    obsFun = strOption (long "obsfun" <> short 'f' <> metavar "FUN" <> help "Observer function")

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

