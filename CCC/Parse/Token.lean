import CCC.Syntax.AST

namespace CCC.Parse

inductive TokenKind where
  | intLit (val : Int)
  | charLit (val : Char)
  | stringLit (val : String)
  | floatLit (val : Float)
  | ident (name : String)
  -- keywords (Phase 1)
  | kw_int | kw_char | kw_long | kw_unsigned | kw_void | kw_bool | kw_struct
  | kw_if | kw_else | kw_while | kw_for | kw_return | kw_sizeof
  -- builtins (NOT identifiers)
  | kw_malloc | kw_free | kw_memcpy
  -- keywords (Phase 2)
  | kw_switch | kw_case | kw_default | kw_break | kw_continue
  | kw_do | kw_goto
  | kw_enum | kw_union | kw_typedef
  | kw_extern | kw_static | kw_inline | kw_register
  | kw_const | kw_volatile | kw_restrict
  | kw_float | kw_double
  | kw_short | kw_signed
  | kw_NULL
  -- punctuation (Phase 1)
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket
  | semi | comma | dot | arrow | amp | star
  -- punctuation (Phase 2)
  | question | colon    -- ternary
  | tilde               -- bitwise not
  | caret               -- bitwise xor
  | pipe                -- bitwise or
  | ellipsis            -- ...  (for varargs)
  -- operators (Phase 1)
  | plus | minus | slash | percent
  | eq | ne | lt | gt | le | ge
  | assign
  | logAnd | logOr | bang
  -- operators (Phase 2)
  | shl | shr                  -- << >>
  | plusAssign | minusAssign    -- += -=
  | starAssign | slashAssign   -- *= /=
  | percentAssign              -- %=
  | ampAssign | pipeAssign     -- &= |=
  | caretAssign                -- ^=
  | shlAssign | shrAssign      -- <<= >>=
  | plusPlus | minusMinus      -- ++ --
  | eof
  deriving Repr, Inhabited, BEq

structure Token where
  kind : TokenKind
  loc  : CCC.Syntax.Loc
  text : String
  deriving Repr, Inhabited

end CCC.Parse
