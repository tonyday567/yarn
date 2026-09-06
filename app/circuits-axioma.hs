module Main (main) where

import Axioma.Common (Verbosity (..))
import Axioma.Container (containerTopic)
import Axioma.Effect (effectTopic)
import Axioma.Equip (equipTopic)
import Axioma.FinRel (finRelTopic)
import Axioma.Machine (machineTopic)
import Axioma.Optic (opticTopic)
import Axioma.Poles (polesTopic)
import Axioma.Process (processTopic)
import Axioma.Pullback (pullbackTopic)
import Axioma.Shared (sharedTopic)
import Axioma.Span (spanTopic)
import Axioma.Split (splitTopic)
import Control.Category ((.))
import Options.Applicative
import Prelude hiding (id, (.))

data Topic
  = All
  | Container
  | Equip
  | Machine
  | Effect
  | FinRel
  | Optic
  | Poles
  | Process
  | Pullback
  | Shared
  | Span
  | Split
  deriving (Show, Eq, Bounded, Enum)

topicName :: Topic -> String
topicName All = "all"
topicName Container = "container"
topicName Equip = "equip"
topicName Machine = "machine"
topicName Effect = "effect"
topicName FinRel = "finrel"
topicName Optic = "optic"
topicName Poles = "poles"
topicName Process = "process"
topicName Pullback = "pullback"
topicName Shared = "shared"
topicName Span = "span"
topicName Split = "split"

topicDesc :: Topic -> String
topicDesc All = "run all topics"
topicDesc Container = "Container oracles: fibred view, skeleton positions, flat/fibre bridges"
topicDesc Equip = "Arrow-equipment oracles: squares, feedback laws, and carriers"
topicDesc Machine = "Machine oracles"
topicDesc Effect = "Effectful K IO and Trace (,) (K IO) oracles"
topicDesc FinRel = "FinRel bimonoid, dagger, and trace oracles"
topicDesc Optic = "Mixed equipment-optic oracles"
topicDesc Poles = "Poles, Stamped, Boundary, and markProcess oracles"
topicDesc Process = "Process, Moore, Body, Trace, and Net oracles"
topicDesc Pullback = "Pullback oracles: chain rule under feedback for cotangent nets"
topicDesc Shared = "Shared-medium scheduling, centrality, and Channel These oracles"
topicDesc Span = "Finite-span equipment oracles"
topicDesc Split = "Split-pole bridge oracles: carrier placements between K m and CoK c"

topicParser :: Parser Topic
topicParser =
  subparser $
    foldr
      (<>)
      (commandGroup "Topics:")
      [ command
          (topicName t)
          (info (pure t <**> helper) (progDesc (topicDesc t)))
      | t <- [minBound .. maxBound],
        t /= All
      ]
      <> command
        "all"
        (info (pure All <**> helper) (progDesc (topicDesc All)))

verbosityParser :: Parser Verbosity
verbosityParser =
  option
    (eitherReader readVerbosity)
    ( long "verbosity"
        <> short 'v'
        <> metavar "LEVEL"
        <> value Axioms
        <> showDefault
        <> help "package | topic | axioms"
    )
  where
    readVerbosity "package" = Right Package
    readVerbosity "topic" = Right Topic
    readVerbosity "axioms" = Right Axioms
    readVerbosity other = Left ("unknown verbosity: " ++ other)

data Options = Options Topic Verbosity

optionsParser :: Parser Options
optionsParser = Options <$> topicParser <*> verbosityParser

opts :: ParserInfo Options
opts =
  info
    (optionsParser <**> helper)
    ( fullDesc
        <> progDesc "Run circuits oracles by topic"
        <> header "circuits-axioma — topic-selectable axiom oracles"
    )

runTopic :: Topic -> Verbosity -> IO [Bool]
runTopic Container = containerTopic
runTopic Equip = equipTopic
runTopic Machine = machineTopic
runTopic Effect = effectTopic
runTopic FinRel = finRelTopic
runTopic Optic = opticTopic
runTopic Poles = polesTopic
runTopic Process = processTopic
runTopic Pullback = pullbackTopic
runTopic Shared = sharedTopic
runTopic Span = spanTopic
runTopic Split = splitTopic
runTopic All = error "runTopic All is handled by the dispatcher"

allTopics :: [Topic]
allTopics = [Container, Equip, Effect, FinRel, Machine, Optic, Poles, Process, Pullback, Shared, Span, Split]

greenCircle :: String
greenCircle = "🟢"

redCircle :: String
redCircle = "🔴"

printCircle :: Bool -> IO ()
printCircle ok = putStr (if ok then greenCircle else redCircle)

runAxioms :: Topic -> IO ()
runAxioms topic = do
  results <- case topic of
    All -> concat <$> mapM (\t -> putStrLn ("=== " ++ topicName t ++ " ===") *> runTopic t Axioms) allTopics
    t -> runTopic t Axioms
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."

runTopicLevel :: Topic -> IO ()
runTopicLevel topic = do
  ok <- case topic of
    All -> do
      results <- mapM (\t -> (t,) <$> runTopic t Topic) allTopics
      mapM_ (\(t, rs) -> putStr (topicName t ++ " ") *> printCircle (and rs) *> putStrLn "") results
      pure (all (and . snd) results)
    t -> do
      results <- runTopic t Topic
      putStr (topicName t ++ " ")
      printCircle (and results)
      putStrLn ""
      pure (and results)
  putStrLn (if ok then "All tests passed." else "Some tests failed.")

runPackage :: Topic -> IO ()
runPackage topic = do
  results <- case topic of
    All -> concat <$> mapM (\t -> runTopic t Package) allTopics
    t -> runTopic t Package
  printCircle (and results)
  putStrLn ""

main :: IO ()
main = do
  Options topic verbosity <- execParser opts
  case verbosity of
    Axioms -> runAxioms topic
    Topic -> runTopicLevel topic
    Package -> runPackage topic
