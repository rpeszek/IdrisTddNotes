{-# LANGUAGE TemplateHaskell
      , GADTs
      , ScopedTypeVariables
      , StandaloneDeriving
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

-----------------------------------------------------------------------------
-- | Example (not very good) implementation of channel thread communication
-- that mimics Idris' System.Concurrency.Channels
-- this approach requires explict channel destruction (to prevent memory leak)
-- and I am ignoring it
-----------------------------------------------------------------------------
module Control.Concurrent.Primitives(
   Channel
  , PID
  , dump
  , spawn
  , connect
  , listen 
  , destroyChannel
  , unsafeSend
  , unsafeRecv
)
where

import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Unsafe.Coerce
import Prelude (String, not)
import Protolude hiding (Nat, forever)

data Box where
  MkBox :: a -> Box 

unsafeUnbox :: Box -> a
unsafeUnbox (MkBox x) = unsafeCoerce x

data Channel where
   MkChannel :: PID -> Chan (Box) -> Chan (Box) -> Channel

serverChannel :: Channel -> Channel
serverChannel (MkChannel pid inp out) = MkChannel pid out inp

channelPid :: Channel -> PID 
channelPid (MkChannel pid _ _) = pid 
 
mkChannel :: PID -> IO Channel
mkChannel pid =  MkChannel pid <$> (newChan :: IO (Chan Box)) <*> (newChan :: IO (Chan Box))

matchChannel :: PID -> Channel -> Bool 
matchChannel upid (MkChannel pid _ _) = upid == pid 

type PID = ThreadId

dump :: String -> MVar [Channel] -> IO ()
dump msg mchs = do 
    chs <- readMVar mchs
    putStrLn msg
    mapM (\ch -> print . channelPid $ ch) chs
    return ()

spawn :: MVar [Channel] -> IO () -> IO PID
spawn mchs comp = do
           ready <- newEmptyMVar 
           pid <- forkIO (takeMVar ready >> comp)
           ch <- mkChannel pid
           putStrLn $ "New thread created " ++ (show pid)
           modifyMVar_ mchs (pure . (ch :))
           putMVar ready () -- wake up thread
           pure pid


-- race condition!! between connect and listen!
-- TODO needs to findOrCreate channel ??
-- needs to destroy channel
connect :: MVar [Channel] -> PID -> IO (Maybe Channel)
connect mchs pid = do
            chs <- readMVar mchs
            let res = headMay (filter (matchChannel pid) chs)
            pure res

destroyChannel :: MVar [Channel] -> PID -> IO ()
destroyChannel mchs pid = do
      modifyMVar_ mchs (pure . filter (not . matchChannel pid))    
 
listen :: MVar [Channel] -> IO (Maybe Channel)
listen mchs = do
           pid <- myThreadId 
           maych <- connect mchs pid
           pure $ serverChannel <$> maych

unsafeSend :: Channel -> a -> IO ()
unsafeSend ch a 
        = case ch of 
            MkChannel _ _ outch -> do
              writeChan outch (MkBox a)
              return ()
-- 
unsafeRecv :: Channel -> IO expected
unsafeRecv ch 
            = case ch of 
                MkChannel _ inch _ -> do  
                  res <- readChan inch 
                  pure $ unsafeUnbox res
