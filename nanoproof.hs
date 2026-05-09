{-# LANGUAGE MultilineStrings #-}

module Main where

import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, put, runStateT)
import Data.Char (isAlpha, isAlphaNum)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import System.Environment (getArgs)
import System.Exit (exitFailure)

-- Types
-- -----

type Name = String

type Ctx = Map Name Term

type Book = Map Name (Term, Term)

type Result = Either String

type Env = Map Name Term

type TermParser = Env -> Term

data Term
  = Var Name
  | Ref Name
  | Lam Name (Term -> Term)
  | App Term Term
  | Set
  | Emp
  | Uni
  | Bit
  | Fix Name (Term -> Term)
  | All Term Term
  | Sig Term Term
  | Eql Term Term
  | One
  | Boo Bool
  | Tup Term Term
  | Efq
  | Use Term
  | Mat Term Term
  | Get Term
  | Rfl
  | Rwt Term Term
  | Red Term Term

data Decl
  = Alias Name Term
  | Defn Name Term Term

-- Stringification
-- ---------------

fresh :: Int -> Name
fresh lvl = names !! lvl

names :: [Name]
names = map name_from_int [0 ..]

name_from_int :: Int -> Name
name_from_int num = if num < 26 then [toEnum (fromEnum 'a' + num)] else "x" ++ show num

show_term :: Int -> Term -> String
show_term lvl term = case term of
  Var nam     -> nam
  Ref nam     -> nam
  Lam _ bod   -> "λ" ++ x ++ "." ++ show_term (lvl + 1) (bod (Var x)) where x = fresh lvl
  App fun arg -> show_app lvl fun [arg]
  Set         -> "Set"
  Emp         -> "⊥"
  Uni         -> "⊤"
  Bit         -> "𝔹"
  Fix _ bod   -> "μ" ++ x ++ "." ++ show_term (lvl + 1) (bod (Var x)) where x = fresh lvl
  All dom cod -> "@" ++ show_term lvl dom ++ "." ++ show_term lvl cod
  Sig dom cod -> "&" ++ show_term lvl dom ++ "." ++ show_term lvl cod
  Eql lft rgt -> show_term lvl lft ++ " == " ++ show_term lvl rgt
  One         -> "()"
  Boo False   -> "0"
  Boo True    -> "1"
  Tup lft rgt -> "(" ++ show_term lvl lft ++ "," ++ show_term lvl rgt ++ ")"
  Efq         -> "λ{}"
  Use bod     -> "λ()" ++ show_term lvl bod
  Mat off on  -> "λ{0:" ++ show_term lvl off ++ ";1:" ++ show_term lvl on ++ ";}"
  Get bod     -> "λ<>" ++ show_term lvl bod
  Rfl         -> "{==}"
  Rwt eql bod -> "!" ++ show_term lvl eql ++ ";" ++ show_term lvl bod
  Red lft rgt -> show_term lvl (show_red lft rgt)

show_red :: Term -> Term -> Term
show_red _   (Red lft rgt) = show_red lft rgt
show_red lft rgt           = if is_stuck rgt then lft else rgt

is_stuck :: Term -> Bool
is_stuck (App _ _) = True
is_stuck _         = False

show_app :: Int -> Term -> [Term] -> String
show_app lvl (App fun arg) args = show_app lvl fun (arg : args)
show_app lvl (Red lft _)   args = show_app lvl lft args
show_app lvl fun           args = show_term lvl fun ++ "(" ++ show_args lvl args ++ ")"

show_args :: Int -> [Term] -> String
show_args _   []       = ""
show_args lvl [term]   = show_term lvl term
show_args lvl (x : xs) = show_term lvl x ++ "," ++ show_args lvl xs

show_book :: Book -> Term -> String
show_book book term = show_term 0 (short book (snf book term))

short :: Book -> Term -> Term
short book term = case alias_name book term of
  Just nam -> Ref nam
  Nothing  -> short_term book term

short_term :: Book -> Term -> Term
short_term _    (Var nam)     = Var nam
short_term _    (Ref nam)     = Ref nam
short_term book (Lam nam bod) = Lam nam (\x -> short book (bod x))
short_term book (App fun arg) = App (short book fun) (short book arg)
short_term _    Set           = Set
short_term _    Emp           = Emp
short_term _    Uni           = Uni
short_term _    Bit           = Bit
short_term book (Fix nam bod) = Fix nam (\x -> short book (bod x))
short_term book (All dom cod) = All (short book dom) (short book cod)
short_term book (Sig dom cod) = Sig (short book dom) (short book cod)
short_term book (Eql lft rgt) = Eql (short book lft) (short book rgt)
short_term _    One           = One
short_term _    (Boo val)     = Boo val
short_term book (Tup lft rgt) = Tup (short book lft) (short book rgt)
short_term _    Efq           = Efq
short_term book (Use bod)     = Use (short book bod)
short_term book (Mat off on)  = Mat (short book off) (short book on)
short_term book (Get bod)     = Get (short book bod)
short_term _    Rfl           = Rfl
short_term book (Rwt eql bod) = Rwt (short book eql) (short book bod)
short_term book (Red lft rgt) = Red (short book lft) (short book rgt)

alias_name :: Book -> Term -> Maybe Name
alias_name book term = alias_name_go book term (Map.toList book)

alias_name_go :: Book -> Term -> [(Name, (Term, Term))] -> Maybe Name
alias_name_go _    _    []                         = Nothing
alias_name_go book term ((nam, (typ, bod)) : rest) = alias_name_pick book term nam typ bod rest

alias_name_pick :: Book -> Term -> Name -> Term -> Term -> [(Name, (Term, Term))] -> Maybe Name
alias_name_pick book term nam typ bod rest = alias_pick book term nam rest (alias_hit book term typ bod)

alias_pick :: Book -> Term -> Name -> [(Name, (Term, Term))] -> Bool -> Maybe Name
alias_pick _    _    nam _    True  = Just nam
alias_pick book term _   rest False = alias_name_go book term rest

alias_hit :: Book -> Term -> Term -> Term -> Bool
alias_hit book term typ bod = equal (snf book typ) Set && equal (snf book bod) term

-- Parsing
-- -------

type Parser = StateT String Result

parse_defs :: String -> Either String [Decl]
parse_defs src = case runStateT parse_decls src of
  Right (defs, rest) | all is_space rest -> Right defs
  Right (_, rest)                        -> Left ("parse error near " ++ take 32 rest)
  Left msg                               -> Left msg

parse_expr :: String -> Either String Term
parse_expr src = case runStateT parse_expr_body src of
  Right (term, _) -> Right term
  Left msg        -> Left msg

parse_expr_body :: Parser Term
parse_expr_body = do
  term <- parse_term
  rest <- look
  if null rest
    then pure (term Map.empty)
    else fail_parse ("parse error near " ++ take 32 rest)

parse_decls :: Parser [Decl]
parse_decls = do
  src <- look
  if null src
    then pure []
    else do
      decl <- parse_decl
      rest <- parse_decls
      pure (decl : rest)

parse_decl :: Parser Decl
parse_decl = do
  nam <- parse_name
  has_typ <- eat ":"
  if has_typ
    then do
      typ <- parse_term
      need "="
      bod <- parse_term
      need ";"
      pure (Defn nam (typ Map.empty) (bod Map.empty))
    else do
      need "="
      bod <- parse_term
      need ";"
      pure (Alias nam (bod Map.empty))

parse_term :: Parser TermParser
parse_term = do
  lft <- parse_head
  got <- eat "=="
  if got
    then do
      rgt <- parse_term
      pure (\env -> Eql (lft env) (rgt env))
    else pure lft

parse_head :: Parser TermParser
parse_head = do
  src <- look
  parse_head_src src

parse_head_src :: String -> Parser TermParser
parse_head_src src = case src of
  '@' : _ -> do
    need "@"
    parse_quant All
  '&' : _ -> do
    need "&"
    parse_quant Sig
  _ -> parse_app

parse_quant :: (Term -> Term -> Term) -> Parser TermParser
parse_quant con = do
  is_bound <- bound_ahead
  if is_bound then parse_quant_bound con else parse_quant_plain con

parse_quant_bound :: (Term -> Term -> Term) -> Parser TermParser
parse_quant_bound con = do
  nam <- parse_name
  need ":"
  dom <- parse_term
  need "."
  cod <- parse_term
  pure (\env -> con (dom env) (Lam nam (\x -> cod (Map.insert nam x env))))

parse_quant_plain :: (Term -> Term -> Term) -> Parser TermParser
parse_quant_plain con = do
  dom <- parse_term
  need "."
  cod <- parse_term
  pure (\env -> con (dom env) (cod env))

parse_app :: Parser TermParser
parse_app = do
  fun <- parse_atom
  args <- parse_args
  pure (\env -> foldl App (fun env) (map (\arg -> arg env) args))

parse_args :: Parser [TermParser]
parse_args = do
  got <- eat "("
  if got
    then do
      end <- eat ")"
      args <- if end then pure [] else parse_args_body
      more <- parse_args
      pure (args ++ more)
    else pure []

parse_args_body :: Parser [TermParser]
parse_args_body = do
  arg <- parse_term
  more <- eat ","
  if more
    then do
      rest <- parse_args_body
      pure (arg : rest)
    else do
      need ")"
      pure [arg]

parse_atom :: Parser TermParser
parse_atom = do
  src <- look
  parse_atom_src src

parse_atom_src :: String -> Parser TermParser
parse_atom_src src = case src of
  'λ' : _ -> do
    need "λ"
    parse_lam
  'μ' : _ -> do
    need "μ"
    parse_fix
  '⊥' : _ -> do
    need "⊥"
    pure (\_ -> Emp)
  '⊤' : _ -> do
    need "⊤"
    pure (\_ -> Uni)
  '𝔹' : _ -> do
    need "𝔹"
    pure (\_ -> Bit)
  '0' : _ -> do
    need "0"
    pure (\_ -> Boo False)
  '1' : _ -> do
    need "1"
    pure (\_ -> Boo True)
  '!' : _ -> parse_rwt
  '{' : _ -> parse_rfl
  '(' : _ -> parse_parens
  []      -> fail_parse "unexpected end of input"
  _       -> parse_var

parse_lam :: Parser TermParser
parse_lam = do
  src <- look
  parse_lam_src src

parse_lam_src :: String -> Parser TermParser
parse_lam_src src = case src of
  '(' : _ -> do
    need "()"
    bod <- parse_term
    pure (\env -> Use (bod env))
  '<' : _ -> do
    need "<>"
    bod <- parse_term
    pure (\env -> Get (bod env))
  '{' : _ -> parse_cases
  _ -> do
    nam <- parse_name
    need "."
    bod <- parse_term
    pure (\env -> Lam nam (\x -> bod (Map.insert nam x env)))

parse_cases :: Parser TermParser
parse_cases = do
  need "{"
  done <- eat "}"
  if done
    then pure (\_ -> Efq)
    else do
      need "0"
      need ":"
      off <- parse_term
      need ";"
      need "1"
      need ":"
      on <- parse_term
      _ <- eat ";"
      need "}"
      pure (\env -> Mat (off env) (on env))

parse_fix :: Parser TermParser
parse_fix = do
  nam <- parse_name
  need "."
  bod <- parse_term
  pure (\env -> Fix nam (\x -> bod (Map.insert nam x env)))

parse_rwt :: Parser TermParser
parse_rwt = do
  need "!"
  eql <- parse_term
  need ";"
  bod <- parse_term
  pure (\env -> Rwt (eql env) (bod env))

parse_rfl :: Parser TermParser
parse_rfl = do
  need "{==}"
  pure (\_ -> Rfl)

parse_parens :: Parser TermParser
parse_parens = do
  need "("
  done <- eat ")"
  if done
    then pure (\_ -> One)
    else do
      lft <- parse_term
      is_tup <- eat ","
      if is_tup
        then do
          rgt <- parse_term
          need ")"
          pure (\env -> Tup (lft env) (rgt env))
        else do
          need ")"
          pure lft

parse_var :: Parser TermParser
parse_var = do
  nam <- parse_name
  if nam == "Set"
    then pure (\_ -> Set)
    else pure (\env -> Map.findWithDefault (Ref nam) nam env)

parse_name :: Parser Name
parse_name = do
  src <- look
  parse_name_src src

parse_name_src :: String -> Parser Name
parse_name_src src = case src of
  c : cs | is_name_start c -> parse_name_hit src (c : takeWhile is_name_char cs)
  c : _ -> fail_parse ("unexpected " ++ [c])
  []    -> fail_parse "unexpected end of input"

parse_name_hit :: String -> Name -> Parser Name
parse_name_hit src nam = do
  put (drop (length nam) src)
  pure nam

is_name_start :: Char -> Bool
is_name_start c = isAlpha c || c == '_'

is_name_char :: Char -> Bool
is_name_char c = isAlphaNum c || c == '_'

is_space :: Char -> Bool
is_space c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

look :: Parser String
look = do
  skip
  get

eat :: String -> Parser Bool
eat tag = do
  src <- look
  eat_pick tag src (eat_match tag src)

eat_match :: String -> String -> Bool
eat_match tag src = take (length tag) src == tag

eat_pick :: String -> String -> Bool -> Parser Bool
eat_pick tag src True  = do
  put (drop (length tag) src)
  pure True
eat_pick _   _   False = pure False

need :: String -> Parser ()
need tag = do
  got <- eat tag
  if got then pure () else fail_parse ("expected " ++ tag)

bound_ahead :: Parser Bool
bound_ahead = do
  src <- look
  pure (is_bound_head src)

is_bound_head :: String -> Bool
is_bound_head src = case src of
  c : cs | is_name_start c -> is_bound_tail (dropWhile is_name_char cs)
  _                        -> False

is_bound_tail :: String -> Bool
is_bound_tail src = case dropWhile is_space src of
  ':' : _ -> True
  _       -> False

skip :: Parser ()
skip = do
  src <- get
  put (skip_space_comments src)

skip_space_comments :: String -> String
skip_space_comments src = case dropWhile is_space src of
  '/' : '/' : rest -> skip_space_comments (skip_line rest)
  rest             -> rest

skip_line :: String -> String
skip_line src = case src of
  '\n' : rest -> rest
  _    : rest -> skip_line rest
  []          -> []

fail_parse :: String -> Parser a
fail_parse msg = lift (Left msg)

-- Evaluation
-- ----------

wnf :: Book -> Term -> Term
wnf book (Ref nam)     = wnf_ref book nam
wnf book (App fun arg) = wnf_app book (wnf book fun) arg
wnf _    term          = term

-- f = t ∈ Book
-- ------------ ref
-- f ~> t
wnf_ref :: Book -> Name -> Term
wnf_ref book nam = case Map.lookup nam book of
  Just (_, bod) -> Red (Ref nam) bod
  Nothing       -> Ref nam

wnf_app :: Book -> Term -> Term -> Term
wnf_app book (Lam _ bod)   arg = wnf_app_lam book bod arg
wnf_app _    Efq           arg = App Efq arg
wnf_app book (Use bod)     arg = wnf_use book bod arg
wnf_app book (Mat off on)  arg = wnf_mat book off on arg
wnf_app book (Get bod)     arg = wnf_get book bod arg
wnf_app book (Red lft rgt) arg = wnf_red book lft rgt arg
wnf_app _    fun           arg = App fun arg

-- (λx.f)(v)
-- --------- app-lam
-- f(v)
wnf_app_lam :: Book -> (Term -> Term) -> Term -> Term
wnf_app_lam book bod arg = wnf book (bod arg)

wnf_use :: Book -> Term -> Term -> Term
wnf_use book bod arg = case wnf book arg of
  One         -> wnf_use_one book bod
  Red lft rgt -> wnf_use_red book bod lft rgt
  got         -> App (Use bod) got

-- λ()f(())
-- ----------- app-use
-- f
wnf_use_one :: Book -> Term -> Term
wnf_use_one book bod = wnf book bod

-- λ()f(l ~> r)
-- ---------------- app-use-red
-- λ()f(l) ~> λ()f(r)
wnf_use_red :: Book -> Term -> Term -> Term -> Term
wnf_use_red book bod lft rgt = Red (App (Use bod) lft) (wnf book (App (Use bod) rgt))

wnf_mat :: Book -> Term -> Term -> Term -> Term
wnf_mat book off on arg = case wnf book arg of
  Boo False   -> wnf_mat_false book off
  Boo True    -> wnf_mat_true book on
  Red lft rgt -> wnf_mat_red book off on lft rgt
  got         -> App (Mat off on) got

-- λ{0:f;1:g}(0)
-- -------------- app-mat-0
-- f
wnf_mat_false :: Book -> Term -> Term
wnf_mat_false book off = wnf book off

-- λ{0:f;1:g}(1)
-- -------------- app-mat-1
-- g
wnf_mat_true :: Book -> Term -> Term
wnf_mat_true book on = wnf book on

-- λ{0:f;1:g}(l ~> r)
-- ------------------- app-mat-red
-- λ{0:f;1:g}(l) ~> λ{0:f;1:g}(r)
wnf_mat_red :: Book -> Term -> Term -> Term -> Term -> Term
wnf_mat_red book off on lft rgt = Red (App (Mat off on) lft) (wnf book (App (Mat off on) rgt))

wnf_get :: Book -> Term -> Term -> Term
wnf_get book bod arg = case wnf book arg of
  Tup lft rgt -> wnf_get_tup book bod lft rgt
  Red lft rgt -> wnf_get_red book bod lft rgt
  got         -> App (Get bod) got

-- λ<>f((a,b))
-- --------------- app-get
-- f(a)(b)
wnf_get_tup :: Book -> Term -> Term -> Term -> Term
wnf_get_tup book bod lft rgt = wnf book (App (App bod lft) rgt)

-- λ<>f(l ~> r)
-- ---------------- app-get-red
-- λ<>f(l) ~> λ<>f(r)
wnf_get_red :: Book -> Term -> Term -> Term -> Term
wnf_get_red book bod lft rgt = Red (App (Get bod) lft) (wnf book (App (Get bod) rgt))

wnf_red :: Book -> Term -> Term -> Term -> Term
wnf_red book lft rgt arg = case wnf book rgt of
  Red _ got   -> wnf_red_red book lft got arg
  Lam _ bod   -> wnf_red_lam book lft bod arg
  Efq         -> wnf_red_efq book lft arg
  Use bod     -> wnf_red_use book lft bod arg
  Mat off on  -> wnf_red_mat book lft off on arg
  Get bod     -> wnf_red_get book lft bod arg
  got         -> Red (App lft arg) (App got arg)

-- (l ~> (m ~> r))(v)
-- ------------------ app-red-red
-- (l ~> r)(v)
wnf_red_red :: Book -> Term -> Term -> Term -> Term
wnf_red_red book lft got arg = wnf_red book lft got arg

-- (l ~> λx.f)(v)
-- --------------- app-red-lam
-- l(v) ~> f(v)
wnf_red_lam :: Book -> Term -> (Term -> Term) -> Term -> Term
wnf_red_lam book lft bod arg = Red (App lft arg) (wnf book (bod arg))

-- (l ~> λ{})(v)
-- ------------- app-red-efq
-- l(v) ~> λ{}(v)
wnf_red_efq :: Book -> Term -> Term -> Term
wnf_red_efq book lft arg = case wnf book arg of
  Red a b -> Red (App lft a) (wnf book (App Efq b))
  got     -> Red (App lft got) (App Efq got)

-- (l ~> λ()f)(v)
-- ------------------ app-red-use
-- l(v) ~> λ()f(v)
wnf_red_use :: Book -> Term -> Term -> Term -> Term
wnf_red_use book lft bod arg = case wnf book arg of
  One     -> Red (App lft One) (wnf book bod)
  Red a b -> Red (App lft a) (wnf book (App (Use bod) b))
  got     -> Red (App lft got) (App (Use bod) got)

-- (l ~> λ{0:f;1:g})(v)
-- --------------------- app-red-mat
-- l(v) ~> λ{0:f;1:g}(v)
wnf_red_mat :: Book -> Term -> Term -> Term -> Term -> Term
wnf_red_mat book lft off on arg = case wnf book arg of
  Boo False -> Red (App lft (Boo False)) (wnf book off)
  Boo True  -> Red (App lft (Boo True)) (wnf book on)
  Red a b   -> Red (App lft a) (wnf book (App (Mat off on) b))
  got       -> Red (App lft got) (App (Mat off on) got)

-- (l ~> λ<>f)(v)
-- ------------------ app-red-get
-- l(v) ~> λ<>f(v)
wnf_red_get :: Book -> Term -> Term -> Term -> Term
wnf_red_get book lft bod arg = case wnf book arg of
  Tup a b -> Red (App lft (Tup a b)) (wnf book (App (App bod a) b))
  Red a b -> Red (App lft a) (wnf book (App (Get bod) b))
  got     -> Red (App lft got) (App (Get bod) got)

-- Normalization
-- -------------

snf :: Book -> Term -> Term
snf book term = case wnf book term of
  Red lft rgt -> Red (snf_args book lft) (snf book rgt)
  Lam nam bod -> Lam nam bod
  App fun arg -> App (snf_args book fun) (snf book arg)
  Set         -> Set
  All dom cod -> All (snf book dom) (snf book cod)
  Sig dom cod -> Sig (snf book dom) (snf book cod)
  Eql lft rgt -> Eql (snf book lft) (snf book rgt)
  Tup lft rgt -> Tup (snf book lft) (snf book rgt)
  Use bod     -> Use bod
  Mat off on  -> Mat off on
  Get bod     -> Get bod
  Rwt eql bod -> Rwt (snf book eql) (snf book bod)
  got         -> got

snf_args :: Book -> Term -> Term
snf_args book (Red lft rgt) = Red (snf_args book lft) (snf_args book rgt)
snf_args book (App fun arg) = App (snf_args book fun) (snf book arg)
snf_args _    term          = term

-- Equality
-- --------

same :: Book -> Term -> Term -> Bool
same book a b = equal (snf book a) (snf book b)

equal :: Term -> Term -> Bool
equal = equal_at 0

equal_at :: Int -> Term -> Term -> Bool
equal_at lvl a b = case (a, b) of
  (Red al ar, Red bl br) -> equal_at lvl al bl || equal_at lvl ar br
  (Red _ ar, _)          -> equal_at lvl ar b
  (_, Red _ br)          -> equal_at lvl a br
  (Var x, Var y)         -> x == y
  (Ref x, Ref y)         -> x == y
  (Lam _ f, Lam _ g)     -> equal_bind lvl f g
  (App af aa, App bf ba) -> equal_at lvl af bf && equal_at lvl aa ba
  (Set, Set)             -> True
  (Emp, Emp)             -> True
  (Uni, Uni)             -> True
  (Bit, Bit)             -> True
  (Fix _ f, Fix _ g)     -> equal_bind lvl f g
  (All ad ac, All bd bc) -> equal_at lvl ad bd && equal_at lvl ac bc
  (Sig ad ac, Sig bd bc) -> equal_at lvl ad bd && equal_at lvl ac bc
  (Eql al ar, Eql bl br) -> equal_at lvl al bl && equal_at lvl ar br
  (One, One)             -> True
  (Boo x, Boo y)         -> x == y
  (Tup al ar, Tup bl br) -> equal_at lvl al bl && equal_at lvl ar br
  (Efq, Efq)             -> True
  (Use x, Use y)         -> equal_at lvl x y
  (Mat ax ay, Mat bx by) -> equal_at lvl ax bx && equal_at lvl ay by
  (Get x, Get y)         -> equal_at lvl x y
  (Rfl, Rfl)             -> True
  (Rwt ae ab, Rwt be bb) -> equal_at lvl ae be && equal_at lvl ab bb
  _                      -> False

equal_bind :: Int -> (Term -> Term) -> (Term -> Term) -> Bool
equal_bind lvl f g = equal_at (lvl + 1) (f (Var (fresh lvl))) (g (Var (fresh lvl)))

-- Rewrite
-- -------

rewrite :: Book -> Term -> Term -> Term -> Term
rewrite book src dst term = rewrite_norm book (snf book src) (snf book dst) term

rewrite_norm :: Book -> Term -> Term -> Term -> Term
rewrite_norm book src dst term = rewrite_pick book src dst term (snf book term)

rewrite_pick :: Book -> Term -> Term -> Term -> Term -> Term
rewrite_pick book src dst term got = if equal src got then dst else rewrite_term book src dst term

rewrite_term :: Book -> Term -> Term -> Term -> Term
rewrite_term _    _   _   (Var nam)     = Var nam
rewrite_term _    _   _   (Ref nam)     = Ref nam
rewrite_term book src dst (Lam nam bod) = Lam nam (\x -> rewrite_norm book src dst (bod x))
rewrite_term book src dst (App fun arg) = App (rewrite_norm book src dst fun) (rewrite_norm book src dst arg)
rewrite_term _    _   _   Set           = Set
rewrite_term _    _   _   Emp           = Emp
rewrite_term _    _   _   Uni           = Uni
rewrite_term _    _   _   Bit           = Bit
rewrite_term book src dst (Fix nam bod) = Fix nam (\x -> rewrite_norm book src dst (bod x))
rewrite_term book src dst (All dom cod) = All (rewrite_norm book src dst dom) (rewrite_norm book src dst cod)
rewrite_term book src dst (Sig dom cod) = Sig (rewrite_norm book src dst dom) (rewrite_norm book src dst cod)
rewrite_term book src dst (Eql lft rgt) = Eql (rewrite_norm book src dst lft) (rewrite_norm book src dst rgt)
rewrite_term _    _   _   One           = One
rewrite_term _    _   _   (Boo val)     = Boo val
rewrite_term book src dst (Tup lft rgt) = Tup (rewrite_norm book src dst lft) (rewrite_norm book src dst rgt)
rewrite_term _    _   _   Efq           = Efq
rewrite_term book src dst (Use bod)     = Use (rewrite_norm book src dst bod)
rewrite_term book src dst (Mat off on)  = Mat (rewrite_norm book src dst off) (rewrite_norm book src dst on)
rewrite_term book src dst (Get bod)     = Get (rewrite_norm book src dst bod)
rewrite_term _    _   _   Rfl           = Rfl
rewrite_term book src dst (Rwt eql bod) = Rwt (rewrite_norm book src dst eql) (rewrite_norm book src dst bod)
rewrite_term book src dst (Red lft rgt) = Red (rewrite_norm book src dst lft) (rewrite_norm book src dst rgt)

rewrite_ctx :: Book -> Term -> Term -> Ctx -> Ctx
rewrite_ctx book src dst ctx = Map.map (\typ -> rewrite book src dst (snf book typ)) ctx

-- Checking
-- --------

infer :: Book -> Ctx -> Term -> Result Term
infer _    ctx (Var nam)     = infer_var ctx nam
infer book _   (Ref nam)     = infer_ref book nam
infer book ctx (App fun arg) = infer_app book ctx fun arg
infer _    _   Set           = infer_set
infer _    _   Emp           = infer_type
infer _    _   Uni           = infer_type
infer _    _   Bit           = infer_type
infer book ctx (Fix nam bod) = infer_fix_type book ctx nam bod
infer book ctx (All dom cod) = infer_quant_type book ctx dom cod
infer book ctx (Sig dom cod) = infer_quant_type book ctx dom cod
infer book ctx (Eql lft rgt) = infer_eql_type book ctx lft rgt
infer _    _   One           = infer_one
infer _    _   (Boo val)     = infer_boo val
infer book ctx (Red _ rgt)   = infer_red book ctx rgt
infer _    _   term          = Left ("can't infer " ++ show_term 0 term)

-- x : A ∈ Γ
-- --------- infer-var
-- Γ ⊢ x ⇒ A
infer_var :: Ctx -> Name -> Result Term
infer_var ctx nam = do
  infer_var_type nam (Map.lookup nam ctx)

infer_var_type :: Name -> Maybe Term -> Result Term
infer_var_type _   (Just typ) = do
  pure typ
infer_var_type nam Nothing    = do
  Left ("unbound variable " ++ nam)

-- f : A = t ∈ Book
-- -------------- infer-ref
-- Γ ⊢ f ⇒ A
infer_ref :: Book -> Name -> Result Term
infer_ref book nam = do
  infer_ref_type nam (Map.lookup nam book)

infer_ref_type :: Name -> Maybe (Term, Term) -> Result Term
infer_ref_type _   (Just (typ, _)) = do
  pure typ
infer_ref_type nam Nothing         = do
  Left ("undefined reference " ++ nam)

-- Γ ⊢ f ⇒ @A.B    Γ ⊢ x ⇐ A
-- ----------------------------- infer-app
-- Γ ⊢ f(x) ⇒ B(x)
infer_app :: Book -> Ctx -> Term -> Term -> Result Term
infer_app book ctx fun arg = do
  typ <- infer book ctx fun
  infer_app_type book ctx fun arg (wnf book typ)

infer_app_type :: Book -> Ctx -> Term -> Term -> Term -> Result Term
infer_app_type book ctx fun arg (Red _ rgt)   = infer_app_red book ctx fun arg rgt
infer_app_type book ctx fun arg (Fix nam f)   = infer_app_fix book ctx fun arg nam f
infer_app_type book ctx _   arg (All dom cod) = infer_app_pi book ctx arg dom cod
infer_app_type _    _   fun _   _             = Left ("not a function " ++ show_term 0 fun)

-- A ~> B    Γ ⊢ f(x) ⇒ B(x)
-- -------------------------- infer-app-red
-- Γ ⊢ f(x) ⇒ A(x)
infer_app_red :: Book -> Ctx -> Term -> Term -> Term -> Result Term
infer_app_red book ctx fun arg rgt = do
  infer_app_type book ctx fun arg rgt

-- μX.F unfolds to F(μX.F)
-- ---------------------- infer-app-fix
-- Γ ⊢ f(x) ⇒ C
infer_app_fix :: Book -> Ctx -> Term -> Term -> Name -> (Term -> Term) -> Result Term
infer_app_fix book ctx fun arg nam f = do
  infer_app_type book ctx fun arg (f (Fix nam f))

-- Γ ⊢ x ⇐ A
-- ---------------- infer-app-pi
-- Γ ⊢ f(x) ⇒ B(x)
infer_app_pi :: Book -> Ctx -> Term -> Term -> Term -> Result Term
infer_app_pi book ctx arg dom cod = do
  check book ctx arg dom
  pure (wnf book (App cod arg))

-- ------------ infer-set
-- Γ ⊢ Set ⇒ Set
infer_set :: Result Term
infer_set = do
  pure Set

-- ------------ infer-type
-- Γ ⊢ T ⇒ Set
infer_type :: Result Term
infer_type = do
  pure Set

-- Γ,X:Set ⊢ F(X) ⇐ Set
-- ---------------------- infer-fix-type
-- Γ ⊢ μX.F ⇒ Set
infer_fix_type :: Book -> Ctx -> Name -> (Term -> Term) -> Result Term
infer_fix_type book ctx nam bod = do
  check book (Map.insert nam Set ctx) (bod (Var nam)) Set
  pure Set

-- Γ ⊢ A ⇐ Set    Γ ⊢ F ⇐ @A.λ_.Set
-- ----------------------------------- infer-quant-type
-- Γ ⊢ @A.F ⇒ Set
infer_quant_type :: Book -> Ctx -> Term -> Term -> Result Term
infer_quant_type book ctx dom cod = do
  check book ctx dom Set
  check book ctx cod (All dom type_family)
  pure Set

type_family :: Term
type_family = Lam "_" (\_ -> Set)

-- Γ ⊢ a ⇒ A    Γ ⊢ b ⇒ B    A ≡ B
-- -------------------------------- infer-eql-type
-- Γ ⊢ a == b ⇒ Set
infer_eql_type :: Book -> Ctx -> Term -> Term -> Result Term
infer_eql_type book ctx lft rgt = case infer book ctx lft of
  Right typ -> do
    check book ctx rgt typ
    pure Set
  Left lmsg -> case infer book ctx rgt of
    Right typ -> do
      check book ctx lft typ
      pure Set
    Left rmsg -> Left (lmsg ++ "\n" ++ rmsg)

-- ------------- infer-one
-- Γ ⊢ () ⇒ ⊤
infer_one :: Result Term
infer_one = do
  pure Uni

-- ------------- infer-bit
-- Γ ⊢ b ⇒ 𝔹
infer_boo :: Bool -> Result Term
infer_boo _ = do
  pure Bit

-- Γ ⊢ r ⇒ A
-- ----------- infer-red
-- Γ ⊢ l~>r ⇒ A
infer_red :: Book -> Ctx -> Term -> Result Term
infer_red book ctx rgt = do
  infer book ctx rgt

check :: Book -> Ctx -> Term -> Term -> Result ()
check book ctx term typ = check_term book ctx term typ (wnf book typ)

check_term :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_term book ctx term          typ (Red _ rgt)   = check_red book ctx term typ rgt
check_term book ctx term          typ (Fix nam f)   = check_fix book ctx term typ nam f
check_term book ctx term          _   (Eql lft rgt) = check_eql book ctx term lft rgt
check_term book ctx (Lam nam bod) _   (All dom cod) = check_lam book ctx nam bod dom cod
check_term book _   Efq           _   (All dom _)   = check_efq book dom
check_term book ctx (Use bod)     _   (All dom cod) = check_use book ctx bod dom cod
check_term book ctx (Mat off on)  _   (All dom cod) = check_mat book ctx off on dom cod
check_term book ctx (Get bod)     _   (All dom cod) = check_get book ctx bod (wnf book dom) cod
check_term book ctx (Tup lft rgt) _   (Sig dom cod) = check_tup book ctx lft rgt dom cod
check_term _    _   One           _   Uni           = check_one
check_term _    _   (Boo val)     _   Bit           = check_boo val
check_term _    _   (Lam _ _)     _   _             = Left "lambda against non-function"
check_term _    _   Efq           _   _             = Left "empty eliminator against non-function"
check_term _    _   (Use _)       _   _             = Left "unit eliminator against non-function"
check_term _    _   (Mat _ _)     _   _             = Left "bit eliminator against non-function"
check_term _    _   (Get _)       _   _             = Left "pair eliminator against non-function"
check_term _    _   (Tup _ _)     _   _             = Left "pair against non-sigma"
check_term book ctx term          typ _             = check_infer book ctx term typ

-- Γ ⊢ t ⇐ R
-- ---------- check-red
-- Γ ⊢ t ⇐ L~>R
check_red :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_red book ctx term typ rgt = do
  check_term book ctx term typ (wnf book rgt)

-- Γ ⊢ t ⇐ F(μX.F)
-- ---------------- check-fix
-- Γ ⊢ t ⇐ μX.F
check_fix :: Book -> Ctx -> Term -> Term -> Name -> (Term -> Term) -> Result ()
check_fix book ctx term typ nam f = do
  check_term book ctx term typ (wnf book (f (Fix nam f)))

-- Γ ⊢ p ⇐ a == b
-- ---------------- check-eql
-- Γ ⊢ p ⇐ a == b
check_eql :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_eql book ctx Rfl           lft rgt = check_rfl book ctx lft rgt
check_eql book ctx (Rwt eql bod) lft rgt = check_rwt book ctx eql bod (Eql lft rgt)
check_eql book ctx term          lft rgt = check_infer book ctx term (Eql lft rgt)

-- a ≡ b
-- ---------- check-rfl
-- Γ ⊢ {==} ⇐ a == b
check_rfl :: Book -> Ctx -> Term -> Term -> Result ()
check_rfl book ctx lft rgt = do
  if same book lft rgt
    then pure ()
    else do
      Left (mismatch book ctx lft rgt)

-- Γ ⊢ e ⇒ a == b    Γ[a↦b] ⊢ t ⇐ T[a↦b]
-- ---------------------------------------- check-rwt
-- Γ ⊢ !e; t ⇐ T
check_rwt :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_rwt book ctx eql bod typ = do
  eql_typ <- infer book ctx eql
  check_rwt_type book ctx bod typ (wnf book eql_typ)

check_rwt_type :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_rwt_type book ctx bod typ (Red _ rgt)   = check_rwt_type book ctx bod typ rgt
check_rwt_type book ctx bod typ (Fix nam f)   = check_rwt_type book ctx bod typ (f (Fix nam f))
check_rwt_type book ctx bod typ (Eql lft rgt) = do
  let new_ctx = rewrite_ctx book lft rgt ctx
  let new_typ = rewrite book lft rgt (snf book typ)
  check book new_ctx bod new_typ
check_rwt_type _    _   _   _   _             = Left "rewrite proof against non-equality"

-- Γ,x:A ⊢ f(x) ⇐ B(x)
-- -------------------- check-lam
-- Γ ⊢ λx.f ⇐ @A.B
check_lam :: Book -> Ctx -> Name -> (Term -> Term) -> Term -> Term -> Result ()
check_lam book ctx nam bod dom cod = do
  let var = Var nam
  check book (Map.insert nam dom ctx) (bod var) (wnf book (App cod var))

-- A ≡ ⊥
-- ------------------ check-efq
-- Γ ⊢ λ{} ⇐ @A.B
check_efq :: Book -> Term -> Result ()
check_efq book dom = do
  if same book dom Emp
    then pure ()
    else Left "empty eliminator against non-empty"

-- A ≡ ⊤    Γ ⊢ f ⇐ B(())
-- -------------------------- check-use
-- Γ ⊢ λ()f ⇐ @A.B
check_use :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_use book ctx bod dom cod = do
  if same book dom Uni
    then check book ctx bod (wnf book (App cod One))
    else Left "unit eliminator against non-unit"

-- A ≡ 𝔹    Γ ⊢ f ⇐ B(0)    Γ ⊢ g ⇐ B(1)
-- ---------------------------------------- check-mat
-- Γ ⊢ λ{0:f;1:g} ⇐ @A.B
check_mat :: Book -> Ctx -> Term -> Term -> Term -> Term -> Result ()
check_mat book ctx off on dom cod = do
  if same book dom Bit
    then do
      check book ctx off (wnf book (App cod (Boo False)))
      check book ctx on (wnf book (App cod (Boo True)))
    else Left "bit eliminator against non-bit"

check_get :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_get book ctx bod (Red _ rgt)           cod = check_get_red book ctx bod rgt cod
check_get book ctx bod (Fix nam f)           cod = check_get_fix book ctx bod nam f cod
check_get book ctx bod (Sig fst_typ snd_typ) cod = check_get_sig book ctx bod fst_typ snd_typ cod
check_get _    _   _   _                     _   = Left "pair eliminator against non-pair"

-- A ~> B    Γ ⊢ λ<>f ⇐ @B.C
-- ------------------------------ check-get-red
-- Γ ⊢ λ<>f ⇐ @A.C
check_get_red :: Book -> Ctx -> Term -> Term -> Term -> Result ()
check_get_red book ctx bod rgt cod = do
  check_get book ctx bod rgt cod

-- μX.F unfolds to F(μX.F)
-- ---------------------- check-get-fix
-- Γ ⊢ λ<>f ⇐ @μX.F.C
check_get_fix :: Book -> Ctx -> Term -> Name -> (Term -> Term) -> Term -> Result ()
check_get_fix book ctx bod nam f cod = do
  check_get book ctx bod (f (Fix nam f)) cod

-- Γ ⊢ f ⇐ @x:F.@y:G(x).B((x,y))
-- -------------------------------- check-get-sig
-- Γ ⊢ λ<>f ⇐ @(&F.G).B
check_get_sig :: Book -> Ctx -> Term -> Term -> Term -> Term -> Result ()
check_get_sig book ctx bod fst_typ snd_typ cod = do
  let typ = All fst_typ (Lam "x" (get_field book snd_typ cod))
  check book ctx bod typ

get_field :: Book -> Term -> Term -> Term -> Term
get_field book snd_typ cod fst_val = All (get_typ book snd_typ fst_val) (get_body book typ cod fst_val) where
  typ = get_typ book snd_typ fst_val

get_body :: Book -> Term -> Term -> Term -> Term
get_body book typ cod fst_val = Lam "y" (get_out book typ cod fst_val)

get_out :: Book -> Term -> Term -> Term -> Term -> Term
get_out book typ cod fst_val snd_val = wnf book (App cod (Tup fst_val (unit book typ snd_val)))

get_typ :: Book -> Term -> Term -> Term
get_typ book snd_typ fst_val = wnf book (App snd_typ fst_val)

-- Γ ⊢ a ⇐ A    Γ ⊢ b ⇐ B(a)
-- -------------------------- check-tup
-- Γ ⊢ (a,b) ⇐ &A.B
check_tup :: Book -> Ctx -> Term -> Term -> Term -> Term -> Result ()
check_tup book ctx lft rgt dom cod = do
  check book ctx lft dom
  check book ctx rgt (wnf book (App cod lft))

-- ------------- check-one
-- Γ ⊢ () ⇐ ⊤
check_one :: Result ()
check_one = do
  pure ()

-- ------------- check-bit
-- Γ ⊢ b ⇐ 𝔹
check_boo :: Bool -> Result ()
check_boo _ = do
  pure ()

unit :: Book -> Term -> Term -> Term
unit book typ val = case wnf book typ of
  Red _ rgt  -> unit book rgt val
  Fix nam f  -> unit book (f (Fix nam f)) val
  Uni        -> One
  _          -> val

-- Γ ⊢ t ⇒ A    A ≡ B
-- ------------------- check-infer
-- Γ ⊢ t ⇐ B
check_infer :: Book -> Ctx -> Term -> Term -> Result ()
check_infer book ctx term typ = do
  got <- infer book ctx term
  if same book got typ
    then pure ()
    else do
      Left (mismatch book ctx typ got)

mismatch :: Book -> Ctx -> Term -> Term -> String
mismatch book ctx expected observed = header ++ want ++ seen ++ body where
  body   = "Context:\n" ++ concatMap (mismatch_entry book) (Map.toList ctx)
  header = "Mismatch:\n"
  want   = "- expected: " ++ show_book book expected ++ "\n"
  seen   = "- observed: " ++ show_book book observed ++ "\n"

mismatch_entry :: Book -> (Name, Term) -> String
mismatch_entry book entry = "- " ++ fst entry ++ " : " ++ show_book book (snd entry) ++ "\n"

-- Tests
-- -----

build_book :: [Decl] -> Book
build_book decls = Map.fromList (map decl_entry decls)

decl_entry :: Decl -> (Name, (Term, Term))
decl_entry decl = case decl of
  Alias nam bod    -> (nam, (Set, bod))
  Defn nam typ bod -> (nam, (typ, bod))

tests :: [Decl] -> [(Name, Term, Term)]
tests []                        = []
tests (Alias nam bod : rest)    = (nam, Set, bod) : tests rest
tests (Defn nam typ bod : rest) = (nam ++ " type", Set, typ) : (nam, typ, bod) : tests rest

run_test :: Book -> (Name, Term, Term) -> IO Bool
run_test book (nam, typ, bod) = case check book Map.empty bod typ of
  Left msg -> do
    putStrLn ("✗ " ++ nam ++ "\n" ++ msg)
    pure False
  Right _ -> do
    putStrLn ("✓ " ++ nam)
    pure True

run_tests :: [Decl] -> IO Bool
run_tests decls = do
  oks <- mapM (run_test (build_book decls)) (tests decls)
  pure (and oks)

check_tests :: Book -> [(Name, Term, Term)] -> Result ()
check_tests _    []                      = pure ()
check_tests book ((nam, typ, bod) : rest) = case check book Map.empty bod typ of
  Left msg -> Left ("✗ " ++ nam ++ "\n" ++ msg)
  Right _  -> check_tests book rest

-- CLI
-- ---

main :: IO ()
main = do
  args <- getArgs
  cli args

cli :: [String] -> IO ()
cli [path] = do
  decls <- load_decls path
  ok <- run_tests decls
  unless ok exitFailure
cli _ = do
  putStrLn "usage: nanoproof file.npf"
  exitFailure

load_decls :: FilePath -> IO [Decl]
load_decls path = do
  src <- readFile path
  case parse_defs src of
    Left msg    -> putStrLn msg >> exitFailure
    Right decls -> pure decls
