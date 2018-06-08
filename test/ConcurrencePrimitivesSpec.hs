{-# OPTIONS_GHC -Wno-unused-imports #-}

--------------------------------------------
-- Tests of Idris' like channel primitives
--------------------------------------------
module ConcurrencePrimitivesSpec where

import           Control.Concurrent.Primitives  
import           Test.Hspec
import           Control.Concurrent.Chan
import           Control.Concurrent.MVar

testSrv :: MVar [Channel] -> IO () 
testSrv mchs = do
   Just ch <- listen mchs
   msg <- unsafeRecv ch :: IO String
   unsafeSend ch $ "hello " ++ msg

testClient :: IO String
testClient = do 
          mchs <- newMVar []
          pid <- spawn mchs (testSrv mchs)
          Just ch <- connect mchs pid
          unsafeSend ch "ping"
          msg <- unsafeRecv ch :: IO String
          return msg

spec :: Spec
-- spec = describe "channel tests" $  
--         runIO testClient >>= (\x -> do 
--           it "sanity" $
--             x `shouldBe` "hello ping")
spec = describe "channel tests" $ do 
         it "sanity" $ do
            testClient `shouldReturn` "hello ping"
