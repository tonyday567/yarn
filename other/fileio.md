

``` haskell 

-- If the handle doesn't exist, create it.
--
-- error handling would go here.
open_ :: FilePath -> Maybe Handle -> IO (Maybe Handle)
open_ fp = \case ->
  Nothing -> openFile fp ReadWriteMode
  Just h -> pure (Just h)

open :: FilePath -> Circuit (Kleisli IO) (Maybe Handle) (Maybe Handle)
open = Loop . Kleisli . open_

-- | Takes a file path and creates e read/write circuit that both reads and appends. 
fileIO :: FilePath -> Circuit (Kleisli IO) Either String (Either String String)
fileIO fp = Loop (Kleisli (go))
     where
       body h = \case
         Right filename -> do
           h <- openFile filename ReadMode
           firstLine <- hGetLine h
           return (Left (Just h, firstLine))

         Left (Just h, line) -> do
           eof <- hIsEOF h
           if eof
             then do
               hClose h
               return (Right "done")
             else do
               nextLine <- hGetLine h
               -- process line, feedback with updated state
               return (Left (Just h, nextLine))

         Left (Nothing, _) -> error "handle not open"

```
