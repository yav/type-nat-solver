module TypeNatSolver (tcPlugin) where

import Type      ( Type, Kind, TyVar
                 , getTyVar_maybe, isNumLitTy, splitTyConApp_maybe
                 , getEqPredTys, mkTyVarTy, mkTyConApp, mkNumLitTy, mkEqPred
                 )
import TyCon     ( TyCon )
import TcEvidence ( EvTerm(..), mkTcAxiomRuleCo )
import CoAxiom   ( Role(..), CoAxiomRule(..) )
import Name      ( nameOccName, nameUnique )
import OccName   ( occNameString )
import Var       ( tyVarName, tyVarKind )
import TcRnMonad ( TcPlugin(..), TcPluginResult(..), Xi
                 , Ct(..), CtEvidence(..), CtLoc, ctLoc, ctPred
                 , mkNonCanonical
                 , TcPluginM, tcPluginIO, tcPluginTrace
                 )

import TcTypeNats ( typeNatAddTyCon
                  , typeNatMulTyCon
                  , typeNatSubTyCon
                  , typeNatLeqTyCon
                  )
import TysWiredIn ( typeNatKindCon
                  , promotedBoolTyCon
                  , promotedFalseDataCon, promotedTrueDataCon
                  )
import Pair       ( Pair(..) )
import FastString ( fsLit )
import UniqFM     ( UniqFM, emptyUFM, plusUFM, unitUFM, eltsUFM )

import Outputable

import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.IORef ( IORef, newIORef, readIORef
                            , modifyIORef'
                            , atomicModifyIORef, atomicModifyIORef' )
import           Data.Char (isSpace)
import           System.Process (runInteractiveProcess, waitForProcess)
import           System.IO (hPutStrLn, hGetLine, hGetContents, hFlush)
import           Data.List (unfoldr, foldl', partition)
import           Data.Maybe ( mapMaybe )
import           Data.Either ( partitionEithers )
import           Control.Concurrent(forkIO)
import           Control.Monad(forever, msum)
import qualified Control.Exception as X


data S = S SolverProcess (IORef VarInfo)

tcPlugin :: TcPlugin
tcPlugin = TcPlugin
  { tcPluginInit  = pluginInit
  , tcPluginSolve = pluginSolve
  , tcPluginStop  =  pluginStop
  }

pluginInit :: [String] -> TcPluginM S
pluginInit opts =
  do -- XXX
     let exe  = "cvc4"
         opts = [ "--incremental", "--lang=smtlib2" ]
     proc <- tcPluginIO $ startSolverProcess exe opts

     -- Prep the solver
     solverSimpleCmd proc [ "set-option", ":print-success", "true" ]
     solverSimpleCmd proc [ "set-option", ":produce-models", "true" ]
     solverSimpleCmd proc [ "set-logic", "QF_LIA" ]

     viRef <- tcPluginIO $ newIORef emptyVarInfo
     return (S proc viRef)

pluginStop :: S -> TcPluginM ()
pluginStop (S proc _) = solverStop proc


pluginSolve :: S -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
pluginSolve s@(S proc _) as _ bs =
  do dbg $ text "-- Givens ------------------------"
     dbg $ ppCts as
     dbg $ text "-- Wanted ------------------------"
     dbg $ ppCts bs
     res <- solverEntry s as bs
     case res of
       TcPluginOk solved new ->
          do dbg $ text "-- Solved -----------------------------"
             dbg $ ppCts solved
             dbg $ text "-- New work ---------------------------"
             dbg $ ppCts new
             dbg $ text "---------------------------------------"

       TcPluginContradiction bad ->
         do dbg $ text "-- Contradiction ------------------------"
            dbg $ ppCts bad
            dbg $ text "-----------------------------------------"

     return res

  where
  dbg = solverDebug proc

  ppCts [] = text "(empty)"
  ppCts cs = vcat (map ppr cs)


solverEntry :: S -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
solverEntry (S proc viRef) givens [] = solverImprove proc viRef True givens

solverEntry (S proc viRef) givens wanteds =
  do solverPush proc viRef
     (_, ourGivens) <- solverPrepare proc viRef givens
     let expr (_,e) = e
     mapM_ (solverAssume proc . expr) ourGivens

     res <- solverImprove proc viRef False wanteds

     final_res <-
       case res of
         TcPluginContradiction bad ->
            return (TcPluginContradiction bad)

         TcPluginOk [] new_cts ->
            do (solved,_) <- solverSimplify proc viRef wanteds
               return (TcPluginOk solved new_cts)

         TcPluginOk _ _ -> panic "solveImprove returned Solved!"
     solverPop proc viRef
     return final_res



-- | Make a fake equality evidence for an equality.
-- We just tag the evidence, so that we know who produced the evidence.
evBy :: (Type,Type) -> EvTerm
evBy (t1,t2) = EvCoercion $ mkTcAxiomRuleCo decisionProcedure [t1,t2] []

  where name = "SMT"
        decisionProcedure =
           CoAxiomRule
             { coaxrName      = fsLit name
             , coaxrTypeArity = 2
             , coaxrAsmpRoles = []
             , coaxrRole      = Nominal
             , coaxrProves    = \ts cs ->
                 case (ts,cs) of
                   ([s,t],[]) -> return (Pair s t)
                   _          -> Nothing
             }


--------------------------------------------------------------------------------
-- Misc.

bool :: Bool -> Type
bool b = if b then mkTyConApp promotedTrueDataCon []
              else mkTyConApp promotedFalseDataCon []

isBoolLitTy :: Type -> Maybe Bool
isBoolLitTy ty =
  do (tc,[]) <- splitTyConApp_maybe ty
     case () of
       _ | tc == promotedFalseDataCon -> return False
         | tc == promotedTrueDataCon  -> return True
         | otherwise                   -> Nothing


--------------------------------------------------------------------------------
-- Higher level operations on collections of constraints.


-- Identify our constraints, and declare their variables in the current scope.
solverPrepare :: SolverProcess -> IORef VarInfo ->
                 [Ct] -> TcPluginM ([Ct], [(Ct,SExpr)])
solverPrepare proc viRef = go [] []
  where
  go others ours [] = return (others, ours)
  go others ours (ct : cts) =
    case knownCt ct of
      Just (vars,e) ->
        do mapM_ (solverDeclare proc viRef) (eltsUFM vars)
           go       others ((ct,e) : ours) cts
      Nothing ->
           go (ct : others)          ours  cts


{- | Check a list of constraints for consistency, and compute derived work.
Does not affect set off assertions in the solver.
-}
solverImprove :: SolverProcess -> IORef VarInfo
              -> Bool -- ^ Should we generate given constraints?
                      -- If not, we generate derived ones.
              -> [Ct]
              -> TcPluginM TcPluginResult
solverImprove proc viRef withEv cts =
  do push   -- declare variables
     (others,ours') <- solverPrepare proc viRef cts
     let ours = [ (ct,e) | (ct,e) <- ours' ]
     case ours of
       [] -> do pop -- declarations
                return (TcPluginOk [] [])

       (oneOfOurs,_) : _ ->
         do push -- assumptions
            mapM_ (assume . snd) ours
            status <- check

            res <-
              case status of

                -- Inconsistent: find a smaller example, then stop.
                Unsat  ->
                  do pop -- assumptions
                     mbRes <- solverFindContraidction proc viRef others ours
                     case mbRes of
                       Nothing ->
                         fail "Bug: Failed to reporoduce contradiciton."
                       Just (core,_) ->
                         return $ TcPluginContradiction core

                -- We don't know: treat as consistent.
                Unknown -> do pop -- assumptions
                              return (TcPluginOk [] [])

                -- Consistent: try to compute derived work.
                Sat ->
                  do m <- solverGetModel proc =<< tcPluginIO (readIORef viRef)

                     imps <- solverImproveModel proc viRef m
                     pop -- assumptions

                     vi   <- tcPluginIO $ readIORef viRef

                     let loc    = ctLoc oneOfOurs -- XXX: Better location?
                         toCt (x,e) =
                           do tv <- varToTyVar x vi
                              ty <- sExprToType vi e
                              return $ mkNonCanonical
                                     $ mkNewFact loc withEv (mkTyVarTy tv, ty)
                     return $ TcPluginOk [] $ mapMaybe toCt imps

            pop -- declarations
            return res
  where
  push    = solverPush   proc viRef
  pop     = solverPop    proc viRef
  assume  = solverAssume proc
  check   = solverCheck  proc


{- Identify a sub-set of constraints that leads to a contradiction.

We call this when we find out that a collection of constraints is
inconsistent:  instead of marking them _all_ as insoluable,
we identify a sub-set that is the real cause of the problem.

* Assumes that the variables in our constarints have been declared.
* Does not change the assertions in the solver.
-}
solverFindContraidction ::
  SolverProcess ->      -- ^ Solver
  IORef VarInfo ->      -- ^ Scoping of variables
  [Ct] ->               -- ^ Constraints not relevant to us
  [(Ct,SExpr)] ->       -- ^ Our constraints
  TcPluginM (Maybe ( [Ct]      -- Constraints that cause a contradiciotn
                   , [Ct]      -- All other constraints (both others and ours)
                   ))
solverFindContraidction proc viRef others ours =
  do push  -- scope for `needed`
     minimize others [] ours

  where
  check   = solverCheck   proc
  push    = solverPush    proc viRef
  pop     = solverPop     proc viRef
  assume  = solverAssume  proc

  minimize notNeeded needed maybeNeeded =
    do res <- check
       case res of
         Unsat -> do pop  -- remove `needed` scope.
                     return $ Just (needed, map fst maybeNeeded ++ notNeeded)
         _     -> do push -- scope for `maybeNeeded`
                     search notNeeded needed [] maybeNeeded

  search _ needed _ [] =
    do pop  -- Remove `maybeNeeded`
       pop  -- Remove `needed`
       case needed of
         [] -> return Nothing    -- No definite contradictions
         _  -> fail "Bug: we found a contradiction, and then lost it!"

  search notNeeded needed maybeNeeded ((ct,e) : more) =
    do assume e    -- Add to `maybeNeeded`
       res <- check
       case res of

         Unsat -> -- We found a contradiction using `needed` and `maybeNeeded`.
           do pop       -- remove `maybeNedded`
              assume e  -- add to `needed`
              minimize (map fst more ++ notNeeded) (ct : needed) maybeNeeded

         -- No contradiction, keep searching.
         _ -> search notNeeded needed ((ct,e) : maybeNeeded) more



{- Try to solve as much as possible from the given list of constraints.
Returns the solved constraints (with evidence), and all other constraints.
-}
{-
Note [In What Order to Solve Wanteds?]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider this example:

ex4 :: p a -> p b -> p ((a + a) + b) -> p (2 * a + b)
ex4 _ = id

A: a + a = u
B: u + b = v
C: 2 * a = w
D: w + b = x

If we solve `B` or `D` first, then we are essnetially done,
as all the others can be substituted within each other.

However, what if we happen to consider `C` first?

(A,B,D) => C

This goal is essentially:

((a + a) + b ~ (2 * a) + b) => (a + a) ~ 2 * a

which can be proved by cancelling `b` on both sides.

Now, we are left with just `A,B,D`, which amounts to having
to prove:

(a + a) + b   ~   w + b

We can't do this because we've lost the information about `w`.
To avoid this, we first try to solve equations that have the same varibal
on the RHS (e.g., F xs ~ a, G ys ~ a).
-}


{-
Note [Incompleteness of the General Approach]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Another tricky example, which illustrates the incompleteness of
the general method:

x :: f (n + 2)
x = undefined

y :: f (m + 1)
y = x

The definition for `x` is accepted, but `y` is rejected.
The reason is that to accept it we need to infer that `m` must
be instantiated to `n + 1`.  The current system does not support this
kind of improvement, because it only ever tries to instantiate variables
to constants or other variables and here we need to instantiate `m`
with a more complex expression, namely, `n + 1`.
-}


solverSimplify :: SolverProcess -> IORef VarInfo ->
                  [Ct] -> TcPluginM ([(EvTerm,Ct)], [Ct])
solverSimplify proc viRef cts =
  do push     -- `unsolved` scope
     (others,ours) <- solverPrepare proc viRef cts
     let (our_eqs, our_rest) = partition isSimpleEq ours
     mapM_ (assume . snd) our_rest
     eithers <- mapM tryToSolve our_eqs
     pop
     let (unsolved, solved) = partitionEithers eithers
     return (solved, unsolved ++ map fst our_rest ++ others)
  where
  push    = solverPush    proc viRef
  pop     = solverPop     proc viRef
  assume  = solverAssume  proc

  isSimpleEq (CTyEqCan {}, _) = True
  isSimpleEq _                = False

  tryToSolve (ct,e) =
    do proved <- solverProve proc viRef e
       if proved then return $ Right (evBy (getEqPredTys (ctPred ct)), ct)
                 else return $ Left ct








--------------------------------------------------------------------------------
-- Recognizing constraints that we can work with.


data Ty       = TNat | TBool
type VarTypes = UniqFM (TyVar,String,Ty)


{- | See if this constraint is one ofthe ones that we understand.
If the constraint is of the form `F ts ~ a`, where `a` is a type-variable,
we also return `a`.  This is used to decide in what order to solve
constraints, see `solverSimplify`. -}
-- XXX: Maybe get rid of the tyVar
knownCt :: Ct -> Maybe (VarTypes, SExpr)
knownCt ct =
  case ct of
    CFunEqCan _ f args rhs ->
      do (vs1,e1) <- knownTerm f args
         (vs2,e2) <- knownVar rhs
         return (plusUFM vs1 vs2, smtEq e1 e2)
    CTyEqCan _ x rhs ->
      do (vs1,e1) <- knownVar x
         (vs2,e2) <- knownXi rhs
         return (plusUFM vs1 vs2, smtEq e1 e2)
    _ -> Nothing

knownTerm :: TyCon -> [Xi] -> Maybe (VarTypes, SExpr)
knownTerm tc xis =
  do op <- knownTC tc
     as <- mapM knownXi xis
     -- XXX: Check for linearity here?
     let (varMaps,es) = unzip as
     return (foldl' plusUFM emptyUFM varMaps, SList (op : es))

knownTC :: TyCon -> Maybe SExpr
knownTC tc
  | tc == typeNatAddTyCon = Just $ SAtom "+"
  | tc == typeNatSubTyCon = Just $ SAtom "-"
  | tc == typeNatMulTyCon = Just $ SAtom "*"
  | tc == typeNatLeqTyCon = Just $ SAtom "<="
  | otherwise             = Nothing

knownXi :: Xi -> Maybe (VarTypes, SExpr)
knownXi xi
  | Just x <- getTyVar_maybe xi   = knownVar x
  | Just x <- isNumLitTy xi       = Just (emptyUFM, smtNum x)
  | Just x <- isBoolLitTy xi      = Just (emptyUFM, smtBool x)
  | otherwise                     = Nothing

knownVar :: TyVar -> Maybe (VarTypes, SExpr)
knownVar x =
  do t <- knownKind (tyVarKind x)
     let v = thyVarName x
     return (unitUFM x (x, v, t), SAtom v)

knownKind :: Kind -> Maybe Ty
knownKind k =
  case splitTyConApp_maybe k of
    Just (tc,[])
      | tc == promotedBoolTyCon -> Just TBool
      | tc == typeNatKindCon    -> Just TNat
    _ -> Nothing


-- From a value back into a type
sExprToType :: VarInfo -> SExpr -> Maybe Type
sExprToType vi expr =
  case expr of
    SAtom "false" -> Just (bool False)
    SAtom "true"  -> Just (bool True)
    SAtom s
      | [(n,"")] <- reads s -> Just (mkNumLitTy n)
    SAtom s
      | Just v <- varToTyVar s vi -> Just (mkTyVarTy v)
    _ -> Nothing



-- A command with no interesting result.
solverAckCmd :: SolverProcess -> SExpr -> TcPluginM ()
solverAckCmd proc c =
  do res <- solverDo proc c
     case res of
       SAtom "success" -> return ()
       _  -> fail $ unlines
                      [ "Unexpected result from the SMT solver:"
                      , "  Expected: success"
                      , "  Result: " ++ renderSExpr res ""
                      ]

-- A command entirely made out of atoms, with no interesting result.
solverSimpleCmd :: SolverProcess -> [String] -> TcPluginM ()
solverSimpleCmd proc = solverAckCmd proc . SList . map SAtom




--------------------------------------------------------------------------------

-- Information about declared variables, so that we know how to extarct
-- models, and map them back into types.
data VarInfo = VarInfo
  { smtCurScope     :: Map String TyVar
  , smtOtherScopes  :: [Map String TyVar]
  }

emptyVarInfo :: VarInfo
emptyVarInfo = VarInfo
  { smtCurScope     = Map.empty
  , smtOtherScopes  = []
  }

inScope :: VarInfo -> [String]
inScope vi = Map.keys $ Map.unions $ smtCurScope vi : smtOtherScopes vi

startScope :: VarInfo -> VarInfo
startScope vi = vi { smtCurScope    = Map.empty
                   , smtOtherScopes = smtCurScope vi : smtOtherScopes vi }

endScope :: VarInfo -> VarInfo
endScope vi =
  case smtOtherScopes vi of
    [] -> panic "endScope with no start scope"
    s : ss -> vi
      { smtCurScope     = s
      , smtOtherScopes  = ss
      }

-- | Turn an SMT variable to a Haskell type variable.
varToTyVar :: String -> VarInfo -> Maybe TyVar
varToTyVar x vi = msum $ map (Map.lookup x) $ smtCurScope vi : smtOtherScopes vi

-- | Pick an SMT name for a Haskell type variable.
thyVarName :: TyVar -> String
thyVarName x = occNameString (nameOccName n) ++ "_" ++ show u
  where n = tyVarName x
        u = nameUnique n



data VarStatus = Undeclared | Declared

-- | Update var info, and indicate if we need to declare the variable.
declareVar :: TyVar -> VarInfo -> (VarInfo, VarStatus)
declareVar tv vi
  | x `Map.member` smtCurScope vi            = (vi, Declared)
  | any (x `Map.member`) (smtOtherScopes vi) = (vi, Declared)
  | otherwise =
    ( vi { smtCurScope = Map.insert x tv (smtCurScope vi) }, Undeclared )
  where x = thyVarName tv


--------------------------------------------------------------------------------

smtTy :: Ty -> SExpr
smtTy ty =
  SAtom $
    case ty of
      TNat  -> "Int"
      TBool -> "Bool"

smtExtraConstraints :: String -> Ty -> [SExpr]
smtExtraConstraints x ty =
  case ty of
    TNat  -> [ smtLeq (smtNum 0) (smtVar x) ]
    TBool -> [ ]

smtVar :: String -> SExpr
smtVar = SAtom

smtEq :: SExpr -> SExpr -> SExpr
smtEq e1 e2 = SList [ SAtom "=", e1, e2 ]

smtLeq :: SExpr -> SExpr -> SExpr
smtLeq e1 e2 = SList [ SAtom "<=", e1, e2 ]

smtBool :: Bool -> SExpr
smtBool b = SAtom (if b then "true" else "false")

smtNum :: Integer -> SExpr
smtNum x = SAtom (show x)




--------------------------------------------------------------------------------
-- Low-level interaction with the solver process.

data SExpr = SAtom String | SList [SExpr]
             deriving Eq

instance Show SExpr where
  showsPrec _ = renderSExpr

data SolverProcess = SolverProcess
  { solverDo   :: SExpr -> TcPluginM SExpr
  , solverStop :: TcPluginM ()

  -- For debguggning

  -- | Record a debugging message.
  , solverDebug     :: SDoc -> TcPluginM ()

  -- | Increase indentation
  , solverDebugNext :: TcPluginM ()

  -- | Decrease indentation
  , solverDebugPrev :: TcPluginM ()
  }

startSolverProcess :: String -> [String] -> IO SolverProcess
startSolverProcess exe opts =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     dbgNest <- newIORef (0 :: Int)
     let dbgMsg x = do n <- tcPluginIO $ readIORef dbgNest
                       tcPluginTrace "[TYPE NAT]" (nest n x)
         dbgNext  = tcPluginIO $ modifyIORef' dbgNest (+2)
         dbgPrev  = tcPluginIO $ modifyIORef' dbgNest (subtract 2)

     -- XXX: Ignore errors for now.
     _ <- forkIO $ do forever (putStrLn =<< hGetLine hErr)
                        `X.catch` \X.SomeException {} -> return ()

     -- XXX: No real error-handling here.
     getResponse <-
       do txt <- hGetContents hOut
          ref <- newIORef (unfoldr parseSExpr txt)
          return $
            tcPluginIO $
            atomicModifyIORef ref $ \xs ->
               case xs of
                 []     -> (xs, Nothing)
                 y : ys -> (ys, Just y)

     let cmd' c = do let e = renderSExpr c ""
                     -- dbgMsg ("[->] " ++ e)
                     tcPluginIO $ do hPutStrLn hIn e
                                     hFlush hIn

     return SolverProcess
        { solverDo = \c -> do cmd' c
                              mb <- getResponse
                              case mb of
                                Just res ->
                                   do -- dbgMsg ("[<-] " ++ renderSExpr res "")
                                      return res
                                Nothing  -> fail "Missing response from solver"
        , solverStop =
            do cmd' (SList [SAtom "exit"])
               _exitCode <- tcPluginIO (waitForProcess h)
               return ()

        , solverDebug     = dbgMsg
        , solverDebugNext = dbgNext
        , solverDebugPrev = dbgPrev
        }

renderSExpr :: SExpr -> ShowS
renderSExpr ex =
  case ex of
    SAtom x  -> showString x
    SList es -> showChar '(' .
                foldr (\e m -> renderSExpr e . showChar ' ' . m)
                (showChar ')') es

parseSExpr :: String -> Maybe (SExpr, String)
parseSExpr (c : more) | isSpace c = parseSExpr more
parseSExpr ('(' : more) = do (xs,more1) <- list more
                             return (SList xs, more1)
  where
  list (c : txt) | isSpace c = list txt
  list (')' : txt) = return ([], txt)
  list txt         = do (v,txt1) <- parseSExpr txt
                        (vs,txt2) <- list txt1
                        return (v:vs, txt2)
parseSExpr txt     = case break end txt of
                       (as,bs) | not (null as) -> Just (SAtom as, bs)
                       _ -> Nothing
  where end x = x == ')' || isSpace x





--------------------------------------------------------------------------------
-- Concrete implementation

mkNewFact :: CtLoc -> Bool -> (Type,Type) -> CtEvidence
mkNewFact newLoc withEv (t1,t2)
  | withEv = CtGiven { ctev_pred = newPred
                     , ctev_evtm = evBy (t1,t2)
                     , ctev_loc  = newLoc
                     }
  | otherwise = CtDerived { ctev_pred = newPred
                          , ctev_loc  = newLoc
                          }
  where
  newPred = mkEqPred t1 t2



-- Checkpoint state
solverPush :: SolverProcess -> IORef VarInfo -> TcPluginM ()
solverPush proc viRef =
  do solverSimpleCmd proc [ "push", "1" ]
     tcPluginIO $ modifyIORef' viRef startScope

-- Restore to last check-point
solverPop :: SolverProcess -> IORef VarInfo -> TcPluginM ()
solverPop proc viRef =
  do solverSimpleCmd proc [ "pop", "1" ]
     tcPluginIO $ modifyIORef' viRef endScope


-- Assume a fact
solverAssume :: SolverProcess -> SExpr -> TcPluginM ()
solverAssume proc e = solverAckCmd proc $ SList [ SAtom "assert", e ]

-- Declare a new variable
solverDeclare :: SolverProcess -> IORef VarInfo ->
                 (TyVar, String, Ty) -> TcPluginM ()
solverDeclare proc viRef (tv,x,ty) =
  do status <- tcPluginIO $ atomicModifyIORef' viRef (declareVar tv)
     case status of
       Declared    -> return ()
       Undeclared  ->
         do solverAckCmd proc $
                SList [SAtom "declare-fun", SAtom x, SList [], smtTy ty]
            mapM_ (solverAssume proc) (smtExtraConstraints x ty)

data SmtRes = Unsat | Unknown | Sat

-- Check if assumptions are consistent. Does not return a model.
solverCheck :: SolverProcess -> TcPluginM SmtRes
solverCheck proc =
  do res <- solverDo proc (SList [ SAtom "check-sat" ])
     case res of
       SAtom "unsat"   -> return Unsat
       SAtom "unknown" -> return Unknown
       SAtom "sat"     -> return Sat
       _ -> fail $ unlines
              [ "Unexpected result from the SMT solver:"
              , "  Expected: unsat, unknown, or sat"
              , "  Result: " ++ renderSExpr res ""
              ]

-- Prove something by concluding that a counter-example is impossible.
solverProve :: SolverProcess -> IORef VarInfo -> SExpr -> TcPluginM Bool
solverProve proc viRef e =
  do solverPush proc viRef
     solverAssume proc $ SList [ SAtom "not", e ]
     res <- solverCheck proc
     solverPop proc viRef
     case res of
       Unsat -> return True
       _     -> return False


-- Get values for the variables that are in scope.
solverGetModel :: SolverProcess -> VarInfo -> TcPluginM [(String,SExpr)]
solverGetModel proc vi =
  do res <- solverDo proc
          $ SList [ SAtom "get-value", SList [ SAtom v | v <- inScope vi ] ]
     case res of
       SList xs -> return [ (x,v) | SList [ SAtom x, v ] <- xs ]
       _ -> fail $ unlines
                 [ "Unexpected response from the SMT solver:"
                 , "  Exptected: a list"
                 , "  Result: " ++ renderSExpr res ""
                 ]

{- Try to generalize some facts for a model.

In particular, we look for facts of the form:
  * x = K, where `K` is a constant, and
  * x = y, where `y` is a variable.

Returns only the new facts.
-}
solverImproveModel :: SolverProcess -> IORef VarInfo ->
                     [(String,SExpr)] -> TcPluginM [ (String,SExpr) ]
solverImproveModel proc viRef imps0 =
  do xs <- constEq [] imps0
     -- solverDebug proc $ "Improvements: " ++ unwords [ x ++ " = " ++ renderSExpr e "," | (x,e) <- xs ]
     return xs
  where

  constEq imps [] = return imps
  constEq imps ((x,v) : more) =
    -- First we check if this is the only possible concrete value for `x`:
    do proved <- solverProve proc viRef (SList [ SAtom "=", SAtom x, v ])
       if proved
         then constEq ((x,v) : imps) more
         -- If two variables `x` and `y` have the same value in this model,
         -- then we check if they must be equal in all models.
         else let (candidates,others) = partition ((== v) . snd) more
              in varEq x imps others candidates


  varEq _ imps more []  = constEq imps more
  varEq x imps more (def@(y,_) : ys) =
    do let e = SAtom y
       -- Check if `x` and `y` must be the same in all models.
       proved <- solverProve proc viRef (SList [ SAtom "=", SAtom x, e ])
       if proved
          then varEq x ((x, e) : imps)        more  ys
          else varEq x           imps  (def : more) ys





