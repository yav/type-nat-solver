module TypeNatSolver (plugin) where

import Type      ( PredType, Type, Kind, TyVar, eqType
                 , getTyVar_maybe, isNumLitTy, splitTyConApp_maybe
                 , getEqPredTys, mkTyConApp, mkNumLitTy, mkEqPred
                 , typeKind, classifyPredType, PredTree(..)
                 )
import TyCon     ( TyCon )
import TcEvidence ( EvTerm(..), mkTcAxiomRuleCo )
import CoAxiom   ( Role(..), CoAxiomRule(..) )
import Name      ( nameOccName, nameUnique )
import OccName   ( occNameString )
import Var       ( tyVarName )
import TcPluginM ( TcPluginM, tcPluginIO, tcPluginTrace )
import TcRnMonad ( TcPlugin(..), TcPluginResult(..)
                 , Ct(..), CtEvidence(..), CtLoc, ctLoc, ctPred
                 , mkNonCanonical, isTouchableTcM, unsafeTcPluginTcM
                 )
import Plugins    ( CommandLineOption, defaultPlugin, Plugin(..) )

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
import TrieMap    ( TypeMap, emptyTypeMap, lookupTypeMap, extendTypeMap )

import Outputable

import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef
                            , modifyIORef', atomicModifyIORef' )
import           Data.List ( find )
import           Data.Maybe ( isNothing )
import           Data.Either ( partitionEithers )
import           Control.Monad(ap, liftM, zipWithM)
import qualified Control.Applicative as A
import           SimpleSMT (SExpr,Value(..),Result(..))
import qualified SimpleSMT as SMT


plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . thePlugin }

thePlugin :: [CommandLineOption] -> TcPlugin
thePlugin opts = TcPlugin
  { tcPluginInit  = pluginInit opts
  , tcPluginSolve = pluginSolve
  , tcPluginStop  = pluginStop
  }

pluginInit :: [CommandLineOption] -> TcPluginM S
pluginInit opts = tcPluginIO $
  do -- XXX: Use `opts`
     let exe  = "cvc4"
         opts = [ "--incremental", "--lang=smtlib2" ]
     doLog <- SMT.newLogger
     proc  <- SMT.newSolver exe opts (Just doLog)

     SMT.setLogic proc "QF_LIA"

     viRef  <- newIORef emptyVarInfo
     impRef <- newIORef newImportS
     return S { solver = proc, declared = viRef, importS = impRef
              , dbgLogger = doLog
              }

pluginStop :: S -> TcPluginM ()
pluginStop s = do _ <- tcPluginIO (SMT.stop (solver s))
                  return ()

pluginSolve :: S -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
pluginSolve s gs ds ws =
  solverDebugFun s "pluginSolve" $
  do resetImportS s
     dbg $ text "-- Givens ------------------------"
     dbg $ ppCts gs
     dbg $ text "-- Wanted ------------------------"
     dbg $ ppCts ws
     res <- solverEntry s gs ds ws
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
  dbg = tcPluginTrace "NAT"

  ppCts [] = text "(empty)"
  ppCts cs = vcat (map ppr cs)


ctNotMember :: [PredType] -> Ct -> Bool
ctNotMember tys ct = isNothing (find (eqType ty) tys)
  where ty = ctPred ct

solverEntry :: S -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
solverEntry s givens _ [] =
  do res <- solverImprove s True givens
     case res of
       TcPluginOk [] new ->
         do let known = map ctPred givens
            return (TcPluginOk [] (filter (ctNotMember known) new))
       x -> return x

solverEntry s givens derived wanteds =
  solverPrepare s givens $ \_others ourGivens ->
  do mapM_ (solverAssume s . snd) ourGivens

     -- XXX: We can use derived here too
     res <- solverImprove s False wanteds

     case res of
       TcPluginContradiction bad ->
          return (TcPluginContradiction bad)

       TcPluginOk [] new_cts ->
          do (solved,_) <- solverSimplify s wanteds
             let known = map ctPred (derived ++ wanteds)
             return (TcPluginOk solved (filter (ctNotMember known) new_cts))

       TcPluginOk _ _ -> panic "solveImprove returned Solved!"



--------------------------------------------------------------------------------
-- Higher level operations on collections of constraints.


-- | Identify our constraints, and declare their variables, for the duration
-- of the given computation.
solverPrepare :: S -> [Ct]
              -> ([Ct] -> [(Ct,SExpr)] -> TcPluginM a)
              -> TcPluginM a
solverPrepare s cts0 k = solverDebugFun s "solverPrepare" $
                         do solverPush s
                            a <- go [] [] cts0
                            solverPop s
                            return a
  where
  go others ours [] = k others ours
  go others ours (ct : cts) =
    do res <- modifyImportS s $ \impS ->
                case knownCt ct impS of
                  Nothing -> (impS, Nothing)
                  Just (a,impS1,vars) -> (impS1, Just (vars,a))
       case res of
         Just (vars,e) -> do mapM_ (solverDeclare s) (Map.toList vars)
                             go       others ((ct,e) : ours) cts
         Nothing       ->    go (ct : others)          ours  cts


{- | Check a list of constraints for consistency, and compute derived work.
Does not affect set off assertions in the solver.
-}
solverImprove :: S
              -> Bool -- ^ Should we generate given constraints?
                      -- If not, we generate derived ones.
              -> [Ct]
              -> TcPluginM TcPluginResult
solverImprove s withEv cts =
  solverDebugFun s "solverImprove" $
  solverPrepare s cts $ \others ours ->
  case ours of
    [] -> return (TcPluginOk [] [])

    (oneOfOurs,_) : _ ->
      do solverPush s -- assumptions
         mapM_ (solverAssume s . snd) ours
         status <- solverCheck s

         case status of

           -- Inconsistent: find a smaller example, then stop.
           Unsat  ->
             do solverPop s -- assumptions
                mbRes <- solverFindContraidction s others ours
                case mbRes of
                  Nothing ->
                    fail "Bug: Failed to reprooduce contradiciton."
                  Just (core,_) ->
                    return (TcPluginContradiction core)

           -- We don't know: treat as consistent.
           Unknown -> do solverPop s -- assumptions
                         return (TcPluginOk [] [])

           -- Consistent: try to compute derived/given work.
           Sat ->
             do m <- solverGetModel s

                imps <- solverImproveModel s m
                solverPop s -- assumptions

                let loc    = ctLoc oneOfOurs -- XXX: Better location?
                    toCt (ty1,ty2) = mkNonCanonical
                                   $ mkNewFact loc withEv (ty1, ty2)

                return (TcPluginOk [] (map toCt imps))


{- Identify a sub-set of constraints that leads to a contradiction.

We call this when we find out that a collection of constraints is
inconsistent:  instead of marking them _all_ as insoluable,
we identify a sub-set that is the real cause of the problem.

* Assumes that the variables in our constarints have been declared.
* Does not change the assertions in the solver.
-}
solverFindContraidction ::
  S ->
  [Ct] ->               -- ^ Constraints not relevant to us
  [(Ct,SExpr)] ->       -- ^ Our constraints
  TcPluginM (Maybe ( [Ct]      -- Constraints that cause a contradiciotn
                   , [Ct]      -- All other constraints (both others and ours)
                   ))
solverFindContraidction s others ours =
  do solverPush s -- scope for `needed`
     minimize others [] ours

  where
  minimize notNeeded needed maybeNeeded =
    do res <- solverCheck s
       case res of
         Unsat -> do solverPop s -- remove `needed` scope.
                     return $ Just (needed, map fst maybeNeeded ++ notNeeded)
         _     -> do solverPush s -- scope for `maybeNeeded`
                     search notNeeded needed [] maybeNeeded

  search _ needed _ [] =
    do solverPop s -- Remove `maybeNeeded`
       solverPop s -- Remove `needed`
       case needed of
         [] -> return Nothing    -- No definite contradictions
         _  -> fail "Bug: we found a contradiction, and then lost it!"

  search notNeeded needed maybeNeeded ((ct,e) : more) =
    do solverAssume s e    -- Add to `maybeNeeded`
       res <- solverCheck s
       case res of

         Unsat -> -- We found a contradiction using `needed` and `maybeNeeded`.
           do solverPop s       -- remove `maybeNedded`
              solverAssume s e  -- add to `needed`
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


solverSimplify :: S -> [Ct] -> TcPluginM ([(EvTerm,Ct)], [Ct])
solverSimplify s wanteds =
  solverPrepare s wanteds $ \others our_wanteds ->
  do eithers <- mapM tryToSolve our_wanteds
     let (unsolved, solved) = partitionEithers eithers
     return (solved, unsolved ++ others)
  where
  tryToSolve (ct,e) =
    do proved <- solverProve s e
       if proved then return (Right (evBy (getEqPredTys (ctPred ct)), ct))
                 else return (Left ct)



{- Try to generalize some facts for a model.

In particular, we look for facts of the form:
  * x = K, where `K` is a constant, and
  * x = y, where `y` is a variable.

Returns only the new facts.
-}
solverImproveModel :: S -> [(String,Value)] -> TcPluginM [(Type,Type)]
solverImproveModel s model = go [] [] model
  where
  go imps _ [] = return imps
  go imps prevs ((x,v) : rest) =
    do let noImp = go imps ((x,v) : prevs) rest

       -- Try `x = K`
       perhaps <- mustBeK x v
       case perhaps of
         Right yes -> go (yes : imps) prevs rest
         Left m1 ->
           -- Try `x = y`
           do mb <- mustBeV x v rest
              case mb of
                Just yes -> go (yes : imps) prevs rest
                Nothing
                  | Int x1 <- v, Just (Int x2) <- lookup x m1 ->
                    do touch <- isTouchableSMT s x
                       if touch
                         -- Try `x = A * y + B`
                         then do mb1 <- mustBeL m1 x x1 x2 (prevs ++ rest)
                                 case mb1 of
                                   Just yes -> go (yes : imps) prevs rest
                                   Nothing  -> noImp
                         else noImp
                  | otherwise -> noImp


  -- Check if `x` must always have specific constant value
  mustBeK x v =
    do mbNot <- solverProve' s (SMT.eq (SMT.const x) (SMT.value v))
       case mbNot of
         -- proved
         Nothing ->
           do tx <- getVarType s x
              return $ Right (tx, constToTy v)

         -- not proved
         Just m1 -> return $ Left m1

  -- Check if `x` must always be equal to another variable.
  mustBeV _ _ [] = return Nothing
  mustBeV x v ((y,v1) : more)
    | v == v1 = do always <- solverProve s (SMT.eq (SMT.const x) (SMT.const y))
                   if always then do tx <- getVarType s x
                                     ty <- getVarType s y
                                     return $ Just (tx,ty)
                             else mustBeV x v more
    | otherwise = mustBeV x v more


  -- Check if `x = A * y + B`
  -- x  = A * y  + B  (we are trying to make one of these)
  -- x1 = A * y1 + B
  -- x2 = A * y2 + B
  -- (x1 - x2) = A * (y1 - y2)
  mustBeL m1 x x1 x2 ((y,Int y1) : _)
    | Just (Int y2) <- lookup y m1
    , y1 /= y2
    , let dx = x1 - x2
    , (a,0) <- divMod dx (y1 - y2)
    , a >= 0
    , let b = x1 - a * y1
    , b >= 0 = do tx <- getVarType s x
                  ty <- getVarType s y
                  let ay | a == 1    = ty
                         | otherwise = mkTyConApp typeNatMulTyCon
                                                            [mkNumLitTy a, ty]
                      rhs | b == 0   = ay
                          | otherwise = mkTyConApp typeNatAddTyCon
                                                            [ay, mkNumLitTy b ]
                  return $ Just (tx, rhs)

  mustBeL m1 x x1 x2 (_ : more) = mustBeL m1 x x1 x2 more

  mustBeL _ _ _ _ [] = return Nothing

  constToTy val = case val of
                    Int n | n >= 0 -> mkNumLitTy n
                    Bool b         -> bool b
                    _ -> panic ("Unexpecetd value in model: " ++ show val)



--------------------------------------------------------------------------------
-- Recognizing constraints that we can work with.

-- | The import operations happens in a mond like this.
newtype ImportM a = Imp (ImportS -> ( a, ImportS, NewVarDecls ))


-- | State used to translate Haskell types into SMT expressions.
data ImportS = ImportS
  { impNextName :: !Int
  -- ^ Used to generate new names, used to deal with terms
  -- from external theories.

  , impKnownTerms :: !(TypeMap SExpr)
  {- ^ Maps Haskell types to their SMT form.
  Used so that we can reuse SMT vars whenever possible
  (e.g., if an external term appears multiple times).

  This could also be used to save some work when importing,
  although it is not at present. -}
  }

-- | Initial import state.
newImportS :: ImportS
newImportS = ImportS { impNextName = 0
                     , impKnownTerms = emptyTypeMap
                     }

-- | When we import terms, we generate new SMT variable.
-- The variables are collected in a map of this type.
type NewVarDecls  = Map String (Type,Ty)


instance Monad ImportM where
 return a     = Imp (\s -> (a, s, Map.empty))
 fail err     = panic err
 Imp m >>= k  = Imp (\s -> let (a,s1,ds1) = m s
                               Imp m1     = k a
                               (b,s2,ds2) = m1 s1
                               ds3        = Map.union ds1 ds2
                           in ds3 `seq` (b, s2, ds3))

instance Functor ImportM where
  fmap = liftM

instance A.Applicative ImportM where
  pure  = return
  (<*>) = ap

runImportM :: ImportS -> ImportM a -> (a, ImportS, NewVarDecls)
runImportM s (Imp m) = m s


-- | Try to import a constraint.
knownCt :: Ct -> ImportS -> Maybe (SExpr, ImportS, NewVarDecls)
knownCt ct s =
  case classifyPredType (ctPred ct) of
    EqPred t1 t2
      | Just ty <- knownKind (typeKind t1) ->
         Just $ runImportM s $
         do lhs <- knownTerm ty t1
            rhs <- knownTerm ty t2 -- assumes kind correct, so reuse 'ty'
            return (SMT.eq lhs rhs)
    _ -> Nothing



-- | Add a new varible declaration required by the import.
recordVarDecl :: String -> Type -> Ty -> ImportM ()
recordVarDecl x term ty = Imp $ \s -> ((), s, Map.singleton x (term,ty))

-- | Name a term.  First we check to see if we already know this term,
-- and, if so, we reuse the name.
nameTerm :: Ty -> Type -> ImportM SExpr
nameTerm ty term = Imp $ \s ->
  case lookupTypeMap (impKnownTerms s) term of
    Just yes -> (yes, s, Map.empty)
    Nothing  ->
      let x = impNextName s
          n = "tn_" ++ show x
          e = SMT.const n
      in ( e
         , ImportS { impNextName   = x + 1
                   , impKnownTerms = extendTypeMap (impKnownTerms s) term e
                   }
         , Map.singleton n (term,ty)
         )

{- | Import a Haskell type (of the kind corresponding to 'ty') as an
SMT term.  If the type does not belong to our theory,
then we replace it with a variable. -}
knownTerm :: Ty -> Type -> ImportM SExpr
knownTerm ty term

  -- A variable?
  | Just tv <- getTyVar_maybe term
  = do let x = thyVarName tv
       recordVarDecl x term ty
       return (SMT.const x)

  -- A literal?
  | Just n <- isNumLitTy term  = return (SMT.int n)
  | Just b <- isBoolLitTy term = return (SMT.bool b)

  -- Application of a known function?
  | Just (tc,terms) <- splitTyConApp_maybe term
  , Just (op,tys)   <- knownTC tc =
    do es <- zipWithM knownTerm tys terms
       return (SMT.List (op : es))


  | otherwise = nameTerm ty term


--------------------------------------------------------------------------------
-- Our theory

data Ty  = TNat | TBool

-- | These are the functions that are part of our theory, with their kinds.
-- We could extract the kinds form the ty-con, but since we know them anyway
-- we just return them.
knownTC :: TyCon -> Maybe (SExpr, [Ty])
knownTC tc
  | tc == typeNatAddTyCon = natOp "+"
  | tc == typeNatSubTyCon = natOp "-"
  | tc == typeNatMulTyCon = natOp "*"
  | tc == typeNatLeqTyCon = natOp "<="
  | otherwise             = Nothing

  where natOp x = Just (SMT.const x, [TNat, TNat])

-- | Theser are the types (i.e., haskell kinds) that are part of our theory.
knownKind :: Kind -> Maybe Ty
knownKind k =
  case splitTyConApp_maybe k of
    Just (tc,[])
      | tc == promotedBoolTyCon -> Just TBool
      | tc == typeNatKindCon    -> Just TNat
    _ -> Nothing







--------------------------------------------------------------------------------
-- Manufacturing constraints and evidence


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


-- | Used when we generate new constraints.
-- The boolean indicates if we are generateing a given or
-- a derived constraint.
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





--------------------------------------------------------------------------------
-- Interacting with the solver.



-- | State of the plugin.
data S = S { solver    :: SMT.Solver      -- ^ A connection to SMT solver
           , declared  :: IORef VarInfo   -- ^ Variables in scope
           , importS   :: IORef ImportS   -- ^ Info about what's imported.
           , dbgLogger :: SMT.Logger
             -- ^ Just used for debugging.
           }


-- | Change importS related information.
modifyImportS :: S -> (ImportS -> (ImportS, a)) -> TcPluginM a
modifyImportS s f = tcPluginIO (atomicModifyIORef' (importS s) f)

-- | We do this before we start solving anything.
resetImportS :: S -> TcPluginM ()
resetImportS s = tcPluginIO (writeIORef (importS s) newImportS)


-- | Update information about declared variables.
modifyScope :: S -> (VarInfo -> (VarInfo,a)) -> TcPluginM a
modifyScope s f = tcPluginIO (atomicModifyIORef' (declared s) f)

-- | Update information about declared variables.
modifyScope_ :: S -> (VarInfo -> VarInfo) -> TcPluginM ()
modifyScope_ s f = tcPluginIO (modifyIORef' (declared s) f)

-- | Get information about the variables that are in scope.
getVarInfo :: S -> TcPluginM VarInfo
getVarInfo s = tcPluginIO (readIORef (declared s))

-- | Map a declared SMT variable, back into the type it corresponds to.
-- Panics if the variable does not exist.
getVarType :: S -> String -> TcPluginM Type
getVarType s x =
  do vi <- getVarInfo s
     case varToType x vi of
       Just t  -> return t
       Nothing -> panic ("getVarType: missing varibale: " ++ show x)

-- | Get the variables that we've declared.
getDeclared :: S -> TcPluginM [String]
getDeclared s = inScope `fmap` getVarInfo s

-- | Does this SMT variable correspond to a touchable variable?
isTouchableSMT :: S -> String -> TcPluginM Bool
isTouchableSMT s x =
  do ty <- getVarType s x
     case getTyVar_maybe ty of
       Just tv -> isTouchableTcPluginM tv
       Nothing -> return False


-- | Is this variable touchable?
-- XXX: This should probably be in GHC.
isTouchableTcPluginM :: TyVar -> TcPluginM Bool
isTouchableTcPluginM x = unsafeTcPluginTcM (isTouchableTcM x)



-- | Checkpoint state.
solverPush :: S -> TcPluginM ()
solverPush s =
  do tcPluginIO (SMT.push (solver s))
     modifyScope_ s startScope

-- | Restore to last check-point.
solverPop :: S -> TcPluginM ()
solverPop s =
  do tcPluginIO (SMT.pop (solver s))
     modifyScope_ s endScope

-- | Assume a fact.
solverAssume :: S -> SExpr -> TcPluginM ()
solverAssume s e = tcPluginIO (SMT.assert (solver s) e)

-- | Declare a new variable.
-- If the variable is already declared, do nothing.
solverDeclare :: S -> (String, (Type,Ty)) -> TcPluginM ()
solverDeclare s (x,(term,ty)) =
  do status <- modifyScope s (declareVar x term)
     case status of
       Declared    -> return ()
       Undeclared  ->
         do _ <- tcPluginIO (SMT.declare (solver s) x smtTy)
            mapM_ (solverAssume s) smtExtraConstraints
  where
  (smtTy, smtExtraConstraints) =
    case ty of
      TNat  -> (SMT.tInt,  [ SMT.leq (SMT.int 0) (SMT.const x) ])
      TBool -> (SMT.tBool, [ ])


-- | Get values for the variables that are in scope.
solverGetModel :: S -> TcPluginM [(String,SMT.Value)]
solverGetModel s =
  do consts <- getDeclared s
     tcPluginIO (SMT.getConsts (solver s) consts)

-- | Check if the current set of assertion is consistent.
-- Does not return a model.
solverCheck :: S -> TcPluginM SMT.Result
solverCheck s = tcPluginIO (SMT.check (solver s))

-- | Prove something by concluding that a counter-example is impossible.
-- Returns 'True' if we managed to prove the statemnt.
solverProve :: S -> SExpr -> TcPluginM Bool
solverProve s e =
  do solverPush s
     solverAssume s (SMT.not e)
     res <- solverCheck s
     solverPop s
     case res of
       Unsat -> return True
       _     -> return False

solverProve' :: S -> SExpr -> TcPluginM (Maybe [(String,SMT.Value)])
solverProve' s e =
  do solverPush s
     solverAssume s (SMT.not e)
     res <- solverCheck s
     mb  <- case res of
              Unsat   -> return Nothing
              Unknown -> return (Just [])
              Sat     -> Just `fmap` solverGetModel s
     solverPop s
     return mb

-- | Quick-and-dirty debugging.
-- We prefer this to `trace` because trace is too verbose.
-- This should not be used in "release" versions.
solverDebugFun :: S -> String -> TcPluginM a -> TcPluginM a
solverDebugFun s x m =
  do tcPluginIO (do SMT.logMessage l x
                    SMT.logTab l)
     a <- m
     tcPluginIO (do SMT.logUntab l
                    SMT.logMessage l ("end of " ++ x))
     return a
  where
  l = dbgLogger s


--------------------------------------------------------------------------------
-- Keeping Track of Variables.


-- | Information about declared variables, so that we know how to extarct
-- models, and map them back into types.
data VarInfo = VarInfo
  { smtCurScope     :: Map String Type
  , smtOtherScopes  :: [Map String Type]
  }

-- | Empty scope info.
emptyVarInfo :: VarInfo
emptyVarInfo = VarInfo
  { smtCurScope     = Map.empty
  , smtOtherScopes  = []
  }

-- | Variable that are currently in scope.
inScope :: VarInfo -> [String]
inScope vi = Map.keys $ Map.unions $ smtCurScope vi : smtOtherScopes vi

-- | Start a new scope.
startScope :: VarInfo -> VarInfo
startScope vi = vi { smtCurScope    = Map.empty
                   , smtOtherScopes = smtCurScope vi : smtOtherScopes vi }

-- | End a scope.
endScope :: VarInfo -> VarInfo
endScope vi =
  case smtOtherScopes vi of
    [] -> panic "endScope with no start scope"
    s : ss -> vi
      { smtCurScope     = s
      , smtOtherScopes  = ss
      }

-- | Is a variable declared?
data VarStatus = Undeclared | Declared
                 deriving Show

-- | Update var info, and indicate if we need to declare the variable.
declareVar :: String -> Type -> VarInfo -> (VarInfo, VarStatus)
declareVar x term vi
  | x `Map.member` smtCurScope vi            = (vi, Declared)
  | any (x `Map.member`) (smtOtherScopes vi) = (vi, Declared)
  | otherwise =
    ( vi { smtCurScope = Map.insert x term (smtCurScope vi) }, Undeclared )

-- | Map an SMT variable, back into the Haskell type it corresponds to.
varToType :: String -> VarInfo -> Maybe Type
varToType x vi = go (smtCurScope vi : smtOtherScopes vi)
  where go [] = Nothing
        go (s : ss) = case Map.lookup x s of
                        Nothing -> go ss
                        Just ty -> return ty

-- | Pick an SMT name for a Haskell type variable.
thyVarName :: TyVar -> String
thyVarName x = occNameString (nameOccName n) ++ "_" ++ show u
  where n = tyVarName x
        u = nameUnique n





--------------------------------------------------------------------------------
-- Lifted Booleans

-- | Make a lifted boolean literal.
bool :: Bool -> Type
bool b = if b then mkTyConApp promotedTrueDataCon []
              else mkTyConApp promotedFalseDataCon []

-- | Check if a type is a lifted boolean literal.
isBoolLitTy :: Type -> Maybe Bool
isBoolLitTy ty =
  do (tc,[]) <- splitTyConApp_maybe ty
     case () of
       _ | tc == promotedFalseDataCon -> return False
         | tc == promotedTrueDataCon  -> return True
         | otherwise                   -> Nothing



