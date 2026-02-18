import CCC.Syntax.AST

namespace CCC.Parse

inductive TokenKind where
  | intLit (val : Int)
  | charLit (val : Char)
  | stringLit (val : String)
  | ident (name : String)
  -- keywords
  | kw_int | kw_char | kw_long | kw_unsigned | kw_void | kw_bool | kw_struct
  | kw_if | kw_else | kw_while | kw_for | kw_return | kw_sizeof
  -- builtins (NOT identifiers)
  | kw_malloc | kw_free | kw_memcpy
  -- punctuation
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket
  | semi | comma | dot | arrow | amp | star
  -- operators
  | plus | minus | slash | percent
  | eq | ne | lt | gt | le | ge
  | assign
  | logAnd | logOr | bang
  | eof
  deriving Repr, Inhabited, BEq

structure Token where
  kind : TokenKind
  loc  : CCC.Syntax.Loc
  text : String
  deriving Repr, Inhabited

end CCC.Parse
