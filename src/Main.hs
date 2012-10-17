module Main where

import Control.Monad.State
import Control.Monad.Error
import qualified Data.Map as Map
import System.Environment
import System.IO
import Text.ParserCombinators.Parsec

------------------------
-------- Parser --------
------------------------

-- HLisp expressions
data HLispExpr = HLispInt Integer
               | HLispSymbol String
               | HLispFn HLispResult [String]
               | HLispSpecialFn HLispResult [String]
               | HLispList [HLispExpr]
               | HLispSList [HLispExpr]

instance Show HLispExpr where
  show (HLispInt x) = "HLispInt " ++ show x
  show (HLispSymbol x) = "HLispSymbol " ++ x
  show (HLispFn _ _) = "<function>"
  show (HLispSpecialFn _ _) = "<special-form>"
  show (HLispList x) = "(" ++ unwords (map show x) ++ ")"
  show (HLispSList x) = "(list " ++ unwords (map show x) ++ ")"

-- Expressions parsing
parseInt :: Parser HLispExpr
parseInt = do sign <- option "" (string "-")
              number <- many1 digit
              return $ HLispInt (read (sign ++ number))

parseSymbol :: Parser HLispExpr
parseSymbol = do f <- firstAllowed
		 r <- many (firstAllowed <|> digit)
		 return $ HLispSymbol (f:r)
  where firstAllowed = oneOf "+-*/<=>" <|> letter

parseList :: Parser HLispExpr
parseList = do char '('
               skipMany space
	       x <- parseExpr' `sepEndBy` (skipMany1 space)
	       char ')'
	       return $ HLispList x

parseExpr' :: Parser HLispExpr
parseExpr' = (try parseInt)
         <|> (try parseSymbol)
         <|> (try parseList)

parseExpr :: Parser HLispExpr
parseExpr = do skipMany space
	       x <- parseExpr'
	       skipMany space
               eof
	       return x

parse :: String -> HLispResult
parse input = case (Text.ParserCombinators.Parsec.parse parseExpr "" input) of 
  Left error -> throwError $ HLispErrorParser error
  Right expr -> return expr

------------------------
------ Evaluator -------
------------------------

-- HLisp errors
data HLispError = HLispErrorInvalidArgs String [HLispExpr]
                | HLispErrorParser ParseError
                | HLispErrorUnboundSym String
                | HLispErrorDefault String
                  
instance Show HLispError where
  show (HLispErrorInvalidArgs expected found) = "Signature expected: " ++ expected
                                            ++ "; found values: " ++ unwordsList found
  show (HLispErrorUnboundSym sym) = "Symbol not bound: " ++ sym
  show (HLispErrorParser parseError) = "Parse error at " ++ show parseError

unwordsList :: [HLispExpr] -> String
unwordsList = unwords . map show

instance Error HLispError where
  noMsg = HLispErrorDefault "An error has occurred"
  strMsg = HLispErrorDefault

-- Context in which expressions will be evaluated
type SymbolTable = Map.Map String HLispExpr
data Context = Ctx SymbolTable (Maybe Context)

-- Helper context functions
updateSymbol sym expr = modify $ \(Ctx symTable parentCtx) -> (Ctx (Map.insert sym expr symTable)) parentCtx
updateSymbolInParent sym expr = modify $ \(Ctx symTable parentCtx) -> (Ctx symTable (updateCtx parentCtx))
  where updateCtx (Just (Ctx pSymTable gParentCtx)) = (Just (Ctx (Map.insert sym expr pSymTable) gParentCtx))
pushContext parentCtx = Ctx Map.empty (Just parentCtx)
popContext rootCtx@(Ctx _ Nothing) = rootCtx
popContext (Ctx _ (Just parentCtx)) = parentCtx

-- A state monad that holds a context and an evaluation result
type HLispErrorIO = ErrorT HLispError IO
type HLispResult = StateT Context HLispErrorIO HLispExpr

-- Evaluating HLisp expression
eval :: HLispExpr -> HLispResult
eval (HLispInt n) = return (HLispInt n)
eval (HLispFn f args) = return (HLispFn f args)
eval (HLispSpecialFn f args) = return (HLispSpecialFn f args)
eval (HLispSymbol s) = do context <- get
                          lookupSymbol context
  where lookupSymbol (Ctx symTable parentCtx) =
          if s `Map.member` symTable == True
          then return (symTable Map.! s)
          else case parentCtx of
            Nothing -> throwError $ HLispErrorUnboundSym s
            (Just parent) -> lookupSymbol parent
eval (HLispList (x:xs)) = do fn <- eval x
                             apply fn
  where apply (HLispSpecialFn f expectedArgs) = apply' f expectedArgs xs
        apply (HLispFn f expectedArgs) = do args <- mapM eval xs
                                            apply' f expectedArgs args
        apply _ = throwError $ HLispErrorUnboundSym (show x)
        apply' f expectedArgs args = do liftIO $ putStrLn $ "  ... " ++ show x ++ " : expected " ++ show expectedArgs ++ ", got " ++ show args
                                        modify pushContext
                                        applyArgsToContext expectedArgs args
                                        result <- f                                        
                                        modify popContext
                                        return result
          where applyArgsToContext ("...":_) args = updateSymbol "..." (HLispList args)
                applyArgsToContext (earg:expectedArgs) (arg:args) = updateSymbol earg arg >> applyArgsToContext expectedArgs args
                applyArgsToContext [] [] = return ()
                applyArgsToContext [] _ = throwError $ HLispErrorInvalidArgs (unwords expectedArgs) args
                applyArgsToContext _ [] = throwError $ HLispErrorInvalidArgs (unwords expectedArgs) args

------------------------
-- Standard functions --
------------------------

-- Arithmetic
hlispArithmeticArgs = ["..."]
hlispArithmetic :: (Integer -> Integer -> Integer) -> HLispResult
hlispArithmetic f  = do [HLispList args] <- getSymbols hlispArithmeticArgs
                        hlispBinary f args

hlispBinary :: (Integer -> Integer -> Integer) -> [HLispExpr] -> HLispResult
hlispBinary op args = foldM (hlispBinary' op) (head args) (tail args)
  where hlispBinary' op (HLispInt i) (HLispInt j) = return $ HLispInt (i `op` j)
        hlispBinary' op _ _ = throwError $ HLispErrorInvalidArgs "[Integer]" args

-- Equality
hlispEqArgs = ["..."]
hlispEq :: HLispResult
hlispEq = do [HLispList args] <- getSymbols hlispEqArgs
             foldM (hlispEq' args) (head args) (tail args)
  where hlispEq' _ (HLispInt i) (HLispInt j) = return $ HLispInt (if i == j then 1 else 0)
        hlispEq' args _ _ = throwError $ HLispErrorInvalidArgs "[Integer]" args

-- Set
hlispSetqArgs = ["symbol", "value"]
hlispSetq :: HLispResult
hlispSetq = do [(HLispSymbol s), val] <- getSymbols hlispSetqArgs
               eVal <- eval val
               updateSymbolInParent s eVal
               return eVal

-- Functions definition
hlispDefunArgs = ["symbol", "args", "..."]
hlispDefun :: HLispResult
hlispDefun = do [(HLispSymbol s), (HLispList args), (HLispList body)] <- getSymbols hlispDefunArgs
                let newFnResult = mapM eval body >>= return . last
                    newFn = HLispFn newFnResult (map (\(HLispSymbol arg)->arg) args)
                updateSymbolInParent s newFn
                return newFn

-- Lists

-- (list 1 2 3)
hlispSListArgs = ["..."]
hlispSList :: HLispResult
hlispSList = do [HLispList xs] <- getSymbols hlispSListArgs
                return $ HLispSList xs

-- Receives a list and returns an element
hlispSListOp1Args = ["slist"]
hlispSListOp1 :: ([HLispExpr] -> HLispExpr) -> HLispResult
hlispSListOp1 f = do [list] <- getSymbols hlispSListOp1Args
                     eList <- eval list
                     case eList of
                       HLispSList eSList -> return $ f eSList
                       x -> throwError $ HLispErrorInvalidArgs "List" [x]

-- Receives a list and returns a list
hlispSListOp2Args = ["slist"]
hlispSListOp2 :: ([HLispExpr] -> [HLispExpr]) -> HLispResult
hlispSListOp2 f = do [list] <- getSymbols hlispSListOp2Args
                     eList <- eval list
                     case eList of
                       HLispSList eSList -> return $ HLispSList (f eSList)
                       x -> throwError $ HLispErrorInvalidArgs "List" [x]

-- (Receives two lists and returns a list)
hlispSListOp3Args = ["slist1", "slist2"]
hlispSListOp3 :: ([HLispExpr] -> [HLispExpr] -> [HLispExpr]) -> HLispResult
hlispSListOp3 f = do [list1, list2] <- getSymbols hlispSListOp3Args
                     eList1 <- eval list1
                     eList2 <- eval list2
                     case eList1 of
                       HLispSList eSList1 -> 
                         case eList2 of
                           HLispSList eSList2 -> return $ HLispSList (eSList1 `f` eSList2)
                           x -> throwError $ HLispErrorInvalidArgs "List" [x]
                       x -> throwError $ HLispErrorInvalidArgs "List" [x]

-- Conditionals
-- (if 1 2 3)
hlispIfArgs = ["condition", "expr1", "expr2"]
hlispIf :: HLispResult
hlispIf = do [condExpr, expr1, expr2] <- getSymbols hlispIfArgs
             eCond <- eval condExpr
             if (0 `notEqual` eCond)
               then eval expr1
               else eval expr2
  where notEqual val1 (HLispInt val2) = val1 /= val2


-- Helper
getSymbol sym = eval $ (HLispSymbol sym)
getSymbols syms = mapM getSymbol syms

-- Symbol table
initialCtx = Ctx (Map.fromList [("+", HLispFn (hlispArithmetic (+)) hlispArithmeticArgs),
                                ("-", HLispFn (hlispArithmetic (-)) hlispArithmeticArgs),
                                ("*", HLispFn (hlispArithmetic (*)) hlispArithmeticArgs),
                                ("/", HLispFn (hlispArithmetic div) hlispArithmeticArgs),
                                ("=", HLispFn hlispEq hlispEqArgs),
                                ("setq", HLispSpecialFn hlispSetq hlispSetqArgs),
                                ("defun", HLispSpecialFn hlispDefun hlispDefunArgs),
                                ("list", HLispSpecialFn hlispSList hlispSListArgs),
                                ("first", HLispSpecialFn (hlispSListOp1 head) hlispSListOp1Args),
                                ("last", HLispSpecialFn (hlispSListOp1 last) hlispSListOp1Args),
                                ("rest", HLispSpecialFn (hlispSListOp2 tail) hlispSListOp2Args),
                                ("butlast", HLispSpecialFn (hlispSListOp2 init) hlispSListOp2Args),
                                ("reverse", HLispSpecialFn (hlispSListOp2 reverse) hlispSListOp2Args),
                                ("append", HLispSpecialFn (hlispSListOp3 (++)) hlispSListOp3Args),
                                ("if", HLispSpecialFn hlispIf hlispIfArgs)
                               ]) Nothing

-----------------------
-------- Main ---------
-----------------------

readPrompt prompt = liftIO $ putStr prompt >> hFlush stdout >> getLine

evalAndPrint input = catchError 
                     (Main.parse input >>= eval >>= liftIO . putStrLn . show) 
                     (liftIO . putStrLn . show)

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do input <- prompt
                               if pred input 
                                 then return ()
                                 else action input >> until_ pred prompt action

repl = until_ (== "(quit)") (readPrompt "HLisp>>> ") evalAndPrint
runRepl = runErrorT (evalStateT repl initialCtx) >> return ()

main = runRepl
