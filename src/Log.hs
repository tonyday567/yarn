{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

module Log
  ( EntryId,
    Log,
    Entry (..),
    Message (..),
    ContentItem (..),
    Role (..),
    Agent (..),
    getId,
    getParentId,
    newLog,
    appendEntry,
    getEntry,
    getChildren,
    getBranch,
    loadJSONL,
    fork,
  )
where

import Control.Applicative ((<|>))
import Data.Aeson (FromJSON, ToJSON, Value (..), object, (.=))
import Data.Aeson qualified as JSON
import Data.Aeson.Types (Parser, withObject, (.:), (.:?))
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy qualified as BL
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)

-- | Entry identifier — short UUID string from pi sessions
type EntryId = Text

-- | Log ⟜ immutable sequence of entries
newtype Log = Log [Entry]
  deriving stock (Show, Eq, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Entry ⟜ one node in the session tree
data Entry
  = SessionEntry
      { sessionId :: EntryId,
        timestamp :: Text,
        cwd :: FilePath
      }
  | MessageEntry
      { msgId :: EntryId,
        msgParentId :: Maybe EntryId,
        msgTimestamp :: Text,
        msg :: Message
      }
  | ModelChangeEntry
      { modelId :: EntryId,
        modelParentId :: Maybe EntryId,
        provider :: Text,
        model :: Text
      }
  | ThinkingLevelEntry
      { thinkId :: EntryId,
        thinkParentId :: Maybe EntryId,
        level :: Text
      }
  deriving (Show, Eq, Generic, ToJSON)

-- | Message ⟜ user or assistant message with polymorphic content
data Message = Message
  { role :: Role,
    content :: [ContentItem]
  }
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

-- | ContentItem ⟜ text, thinking, tool call, or tool result
data ContentItem
  = TextContent {text :: Text}
  | ThinkingContent {thinking :: Text}
  | ToolCallContent
      { toolCallId :: Text,
        toolName :: Text,
        arguments :: JSON.Object
      }
  | ToolResultContent
      { resultCallId :: Text,
        resultToolName :: Text,
        resultContent :: [ContentItem]
      }
  deriving (Show, Eq, Generic, ToJSON)

instance FromJSON ContentItem where
  parseJSON = withObject "ContentItem" $ \v -> do
    typ <- v .: "type" :: Parser String
    case typ of
      "text" -> TextContent <$> v .: "text"
      "thinking" -> ThinkingContent <$> v .: "thinking"
      "toolCall" ->
        ToolCallContent
          <$> v .: "id"
          <*> v .: "name"
          <*> v .: "arguments"
      "toolResult" ->
        ToolResultContent
          <$> v .: "toolCallId"
          <*> v .: "toolName"
          <*> v .: "content"
      _ -> fail ("Unknown content type: " ++ typ)

-- | Role ⟜ speaker identity
data Role = User | Assistant | ToolResult
  deriving (Show, Eq, Generic, ToJSON)

instance FromJSON Role where
  parseJSON (JSON.String "user") = pure User
  parseJSON (JSON.String "assistant") = pure Assistant
  parseJSON (JSON.String "toolResult") = pure ToolResult
  parseJSON v = fail ("Unknown role: " ++ show v)

-- | Extract entry ID from any Entry
getId :: Entry -> EntryId
getId (SessionEntry eid _ _) = eid
getId (MessageEntry eid _ _ _) = eid
getId (ModelChangeEntry eid _ _ _) = eid
getId (ThinkingLevelEntry eid _ _) = eid

-- | Extract parent ID from any Entry (Nothing for roots)
getParentId :: Entry -> Maybe EntryId
getParentId (SessionEntry _ _ _) = Nothing
getParentId (MessageEntry _ p _ _) = p
getParentId (ModelChangeEntry _ p _ _) = p
getParentId (ThinkingLevelEntry _ p _) = p

-- | Create empty log
--
-- >>> newLog
-- Log []
newLog :: Log
newLog = Log []

-- | Append entry to log
--
-- >>> import qualified Data.Text as T
-- >>> let e1 = SessionEntry (T.pack "id1") (T.pack "2026-03-11T00:00:00Z") "."
-- >>> let log0 = newLog
-- >>> appendEntry log0 e1 `seq` True
-- True
appendEntry :: Log -> Entry -> Log
appendEntry (Log es) e = Log (es ++ [e])

-- | Look up entry by ID
getEntry :: Log -> EntryId -> Maybe Entry
getEntry (Log es) eid =
  case filter (\e -> getId e == eid) es of
    [e] -> Just e
    _ -> Nothing

-- | Get all children of an entry
getChildren :: Log -> EntryId -> [Entry]
getChildren (Log es) eid =
  filter (\e -> getParentId e == Just eid) es

-- | Get path from root to leaf (inclusive)
--
-- >>> import qualified Data.Text as T
-- >>> let s = SessionEntry (T.pack "session-1") (T.pack "2026-01-01T00:00:00Z") "/home/user"
-- >>> let m = MessageEntry (T.pack "msg-1") (Just (T.pack "session-1")) (T.pack "2026-01-01T00:01:00Z") (Message User [])
-- >>> getBranch newLog (Just (T.pack "msg-1"))
-- []
--
-- >>> getBranch newLog (Just (T.pack "nonexistent"))
-- []
getBranch :: Log -> Maybe EntryId -> [Entry]
getBranch (Log es) leafId = go leafId []
  where
    go Nothing acc = reverse acc
    go (Just eid) acc =
      case filter (\e -> getId e == eid) es of
        [e] -> go (getParentId e) (e : acc)
        _ -> reverse acc

-- | Load JSONL file line-by-line, parse each as Entry, construct Log
loadJSONL :: FilePath -> IO (Either String Log)
loadJSONL fp = do
  content <- BL.readFile fp
  let linesBS = BL.split 10 content
      nonEmptyLines = filter (not . BL.null) linesBS
  case mapM (JSON.eitherDecode' :: ByteString -> Either String Entry) nonEmptyLines of
    Left err -> pure (Left err)
    Right es -> pure (Right (Log es))

-- | Custom FromJSON for Entry (union type dispatch on "type" field)
instance FromJSON Entry where
  parseJSON = withObject "Entry" $ \v -> do
    typ <- v .: "type" :: Parser String
    case typ of
      "session" -> do
        sid <- v .: "id"
        ts <- v .: "timestamp"
        cwd <- v .: "cwd"
        pure (SessionEntry sid ts cwd)
      "message" -> do
        mid <- v .: "id"
        mpid <- v .:? "parentId"
        ts <- v .: "timestamp"
        msg <- v .: "message"
        pure (MessageEntry mid mpid ts msg)
      "model_change" -> do
        mid <- v .: "id"
        mpid <- v .:? "parentId"
        prov <- v .: "provider"
        mdl <- v .: "modelId"
        pure (ModelChangeEntry mid mpid prov mdl)
      "thinking_level_change" -> do
        tid <- v .: "id"
        tpid <- v .:? "parentId"
        lvl <- v .: "thinkingLevel"
        pure (ThinkingLevelEntry tid tpid lvl)
      _ -> fail ("Unknown entry type: " ++ typ)

-- | Fork a Log: extract path from root to a leaf (creates new sub-conversation)
--
-- >>> import qualified Data.Text as T
-- >>> let err = fork newLog (Just (T.pack "missing"))
-- >>> case err of { Left _ -> True; Right _ -> False }
-- True
--
-- >>> case fork newLog Nothing of { Left _ -> True; Right _ -> False }
-- True
fork :: Log -> Maybe EntryId -> Either String Log
fork log leafId =
  let branch = getBranch log leafId
   in if null branch
        then Left ("No entries found for leaf: " ++ show leafId)
        else Right (Log branch)

-- | Agent ⟜ reads a Log window, returns response Log + next Agent state
newtype Agent = Agent {step :: Log -> (Agent, Log)}
  deriving (Generic)
