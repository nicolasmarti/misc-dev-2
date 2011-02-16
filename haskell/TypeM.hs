{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- this is the monad used for typechecking 

module TypeM where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.RWS

import Def

-- here we need a monad that supports
-- 1) state
-- 2) log
-- 3) error / exception
-- 4) IO ???

data TCErr = PlainErr String
           | ErrNoDef String Position
           | ErrNoModule ModulePath Position
           | ErrTermNotTypeChecked Position
             deriving (Eq, Show, Ord, Read)

instance Error TCErr where
    -- strMsg :: String -> a
    strMsg = PlainErr
    
    
data TCLog = TCLog ()
           deriving (Eq, Show, Ord, Read)


instance Monoid TCLog where 
    -- mempty :: a
    mempty = error ""
    -- mappend :: a -> a -> a
    mappend = error ""


type TypeM a = ErrorT TCErr (ReaderT TCGlobal (WriterT TCLog (StateT TCEnv IO))) a

-- from MonadError
-- throwError :: e -> m a
-- catchError :: m a -> (e -> m a) -> m a

-- from MonadReader
-- ask :: m r
-- localSource :: (r -> r) -> m a -> m a

-- from MonadWriter
-- tell :: w -> m ()
-- listen :: m a -> m (a, w)
-- pass :: m (a, w -> w) -> m a

-- from MonadState
-- get :: m s
-- put :: s -> m ()

runTypeM :: TypeM a -> TCGlobal -> TCEnv -> IO (Either (TCErr, TCLog) (a, TCEnv, TCLog))
runTypeM fct globals env = do {
    -- runErrorT :: m (Either e a)
    ; let res1 = runErrorT fct -- ReaderT TCGlobal (WriterT TCLog (StateT TCEnv IO)) (Either TCerr, a)
    -- runReaderT :: r -> m a
    ; let res2 = runReaderT res1 globals -- WriterT TCLog (StateT TCEnv IO) (Either TCerr a)
    -- runWriterT :: m (a, w)      
    ; let res3 = runWriterT res2 -- StateT TCEnv IO ((Either TCerr a), TCLog)
    -- runStateT :: s -> m (a, s)      
    ; (((res4), log), env) <- runStateT res3 env -- IO (((Either TCerr a), TCLog), TCenv)
    ; case res4 of
        Left err -> return $ Left (err, log)
        Right res -> return $ Right (res, env, log)
    }
