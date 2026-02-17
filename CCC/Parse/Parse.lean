import CCC.Parse.Lex

namespace CCC.Parse

open CCC.Syntax

structure ParseState where
  tokens : Array Token
  pos : Nat
  deriving Repr

abbrev Parser (α : Type) := ExceptT String (StateM ParseState) α

def fallbackToken : Token :=
  { kind := .eof, loc := { line := 1, col := 1 }, text := "" }

def runParser {α : Type} (p : Parser α) (tokens : List Token) : Except String α :=
  let init : ParseState := { tokens := tokens.toArray, pos := 0 }
  let (result, _st) := p.run init
  result

def currentToken : Parser Token := do
  let st : ParseState ← get
  match st.tokens[st.pos]? with
  | some tok => pure tok
  | none =>
      match st.tokens.back? with
      | some tok => pure tok
      | none => pure fallbackToken

def peekTokenAt (offset : Nat) : Parser Token := do
  let st : ParseState ← get
  let idx : Nat := st.pos + offset
  match st.tokens[idx]? with
  | some tok => pure tok
  | none =>
      match st.tokens.back? with
      | some tok => pure tok
      | none => pure fallbackToken

def advance : Parser Token := do
  let st : ParseState ← get
  let tok : Token :=
    match st.tokens[st.pos]? with
    | some t => t
    | none =>
        match st.tokens.back? with
        | some t => t
        | none => fallbackToken
  let newPos : Nat :=
    if st.pos < st.tokens.size then
      st.pos + 1
    else
      st.pos
  set { st with pos := newPos }
  pure tok

def tokenTextForError (tok : Token) : String :=
  if tok.text = "" then reprStr tok.kind else tok.text

def expectKind (expected : TokenKind) (label : String) : Parser Token := do
  let tok : Token ← currentToken
  if tok.kind == expected then
    advance
  else
    throw s!"Expected {label} at {tok.loc.line}:{tok.loc.col}, found {tokenTextForError tok}"

def checkKind (expected : TokenKind) : Parser Bool := do
  let tok : Token ← currentToken
  pure (tok.kind == expected)

def consumeIfKind (expected : TokenKind) : Parser Bool := do
  let ok : Bool ← checkKind expected
  if ok then
    let _ ← advance
    pure true
  else
    pure false

def expectIdent : Parser (String × Loc) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .ident name =>
      let _ ← advance
      pure (name, tok.loc)
  | _ =>
      throw s!"Expected identifier at {tok.loc.line}:{tok.loc.col}, found {tokenTextForError tok}"

def isTypeStartKind (k : TokenKind) : Bool :=
  match k with
  | .kw_int | .kw_char | .kw_long | .kw_unsigned | .kw_void | .kw_bool | .kw_struct => true
  | .ident name => name = "size_t"
  | _ => false

partial def parseType : Parser CType := do
  let tok : Token ← currentToken
  match tok.kind with
  | .kw_int =>
      let _ ← advance
      pure .int
  | .kw_char =>
      let _ ← advance
      pure .char
  | .kw_long =>
      let _ ← advance
      pure .long
  | .kw_void =>
      let _ ← advance
      pure .void
  | .kw_bool =>
      let _ ← advance
      pure .bool
  | .kw_unsigned =>
      let _ ← advance
      let innerTok : Token ← currentToken
      match innerTok.kind with
      | .kw_int =>
          let _ ← advance
          pure (.unsigned .int)
      | .kw_char =>
          let _ ← advance
          pure (.unsigned .char)
      | .kw_long =>
          let _ ← advance
          pure (.unsigned .long)
      | _ =>
          throw s!"Expected int/char/long after unsigned at {innerTok.loc.line}:{innerTok.loc.col}"
  | .kw_struct =>
      let _ ← advance
      let (name, _) ← expectIdent
      pure (.struct_ name)
  | .ident name =>
      if name = "size_t" then
        let _ ← advance
        pure .sizeT
      else
        throw s!"Unknown type name '{name}' at {tok.loc.line}:{tok.loc.col}"
  | _ =>
      throw s!"Expected type at {tok.loc.line}:{tok.loc.col}, found {tokenTextForError tok}"

inductive InfixOp where
  | bin (op : BinOp)
  | assign

def infixInfo (k : TokenKind) : Option (Nat × Bool × InfixOp) :=
  match k with
  | .assign => some (0, true, .assign)
  | .logOr => some (1, false, .bin .or_)
  | .logAnd => some (2, false, .bin .and_)
  | .eq => some (3, false, .bin .eq)
  | .ne => some (3, false, .bin .ne)
  | .lt => some (4, false, .bin .lt)
  | .gt => some (4, false, .bin .gt)
  | .le => some (4, false, .bin .le)
  | .ge => some (4, false, .bin .ge)
  | .plus => some (5, false, .bin .add)
  | .minus => some (5, false, .bin .sub)
  | .star => some (6, false, .bin .mul)
  | .slash => some (6, false, .bin .div)
  | .percent => some (6, false, .bin .mod)
  | _ => none

mutual

partial def parseExpr (minPrec : Nat := 0) : Parser Expr := do
  let lhs : Expr ← parsePrimary
  parseExprLoop minPrec lhs

partial def parseExprLoop (minPrec : Nat) (lhs : Expr) : Parser Expr := do
  let tok : Token ← currentToken
  match infixInfo tok.kind with
  | none => pure lhs
  | some (prec, rightAssoc, op) =>
      if prec < minPrec then
        pure lhs
      else
        let _ ← advance
        let rhsMinPrec : Nat := if rightAssoc then prec else prec + 1
        let rhs : Expr ← parseExpr rhsMinPrec
        let loc : Loc := Expr.loc lhs
        let combined : Expr :=
          match op with
          | .assign => .assign lhs rhs loc
          | .bin binOp => .binOp binOp lhs rhs loc
        parseExprLoop minPrec combined

partial def parsePrimary : Parser Expr := do
  let unary : Expr ← parseUnary
  parsePostfix unary

partial def parseUnary : Parser Expr := do
  let tok : Token ← currentToken
  match tok.kind with
  | .minus =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .neg operand tok.loc)
  | .bang =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .not_ operand tok.loc)
  | .star =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .deref operand tok.loc)
  | .amp =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .addrOf operand tok.loc)
  | .kw_sizeof =>
      let _ ← advance
      let _ ← expectKind .lparen "'(' after sizeof"
      let ty : CType ← parseType
      let _ ← expectKind .rparen "')' after sizeof(type)"
      pure (.sizeOf ty tok.loc)
  | _ => parseAtom

partial def parseAtom : Parser Expr := do
  let tok : Token ← currentToken
  match tok.kind with
  | .intLit val =>
      let _ ← advance
      pure (.intLit val tok.loc)
  | .charLit val =>
      let _ ← advance
      pure (.charLit val tok.loc)
  | .stringLit _value =>
      let _ ← advance
      pure (.var tok.text tok.loc)
  | .ident name =>
      let _ ← advance
      pure (.var name tok.loc)
  | .kw_malloc =>
      let _ ← advance
      pure (.var "malloc" tok.loc)
  | .kw_free =>
      let _ ← advance
      pure (.var "free" tok.loc)
  | .kw_memcpy =>
      let _ ← advance
      pure (.var "memcpy" tok.loc)
  | .lparen =>
      let _ ← advance
      let expr : Expr ← parseExpr 0
      let _ ← expectKind .rparen "')'"
      pure expr
  | _ =>
      throw s!"Expected expression at {tok.loc.line}:{tok.loc.col}, found {tokenTextForError tok}"

partial def parseCallArgs : Parser (List Expr) := do
  let done : Bool ← consumeIfKind .rparen
  if done then
    pure []
  else
    let first : Expr ← parseExpr 0
    parseCallArgsRest [first]

partial def parseCallArgsRest (revArgs : List Expr) : Parser (List Expr) := do
  let hasComma : Bool ← consumeIfKind .comma
  if hasComma then
    let nextArg : Expr ← parseExpr 0
    parseCallArgsRest (nextArg :: revArgs)
  else
    let _ ← expectKind .rparen "')'"
    pure revArgs.reverse

partial def parsePostfix (base : Expr) : Parser Expr := do
  let tok : Token ← currentToken
  match tok.kind with
  | .lbracket =>
      let _ ← advance
      let idx : Expr ← parseExpr 0
      let _ ← expectKind .rbracket "']'"
      let node : Expr := .index base idx (Expr.loc base)
      parsePostfix node
  | .dot =>
      let _ ← advance
      let (field, _) ← expectIdent
      let node : Expr := .member base field (Expr.loc base)
      parsePostfix node
  | .arrow =>
      let _ ← advance
      let (field, _) ← expectIdent
      let node : Expr := .arrow base field (Expr.loc base)
      parsePostfix node
  | .lparen =>
      let callLoc : Loc := Expr.loc base
      let _ ← advance
      let args : List Expr ← parseCallArgs
      match base with
      | .var fnName _ =>
          let node : Expr := .call fnName args callLoc
          parsePostfix node
      | _ =>
          throw s!"Can only call named functions at {callLoc.line}:{callLoc.col}"
  | _ => pure base

end

partial def parsePointerSuffix (ty : CType) : Parser CType := do
  let tok : Token ← currentToken
  match tok.kind with
  | .star =>
      let _ ← advance
      parsePointerSuffix (.pointer ty)
  | _ => pure ty

def intToNatChecked (value : Int) : Except String Nat :=
  if value < 0 then
    .error s!"Expected non-negative array size, found {value}"
  else
    .ok value.toNat

partial def parseArraySuffix (ty : CType) : Parser CType := do
  let hasArray : Bool ← consumeIfKind .lbracket
  if hasArray then
    let sizeTok : Token ← currentToken
    let size : Nat ←
      match sizeTok.kind with
      | .intLit n =>
          match intToNatChecked n with
          | .ok v =>
              let _ ← advance
              pure v
          | .error msg =>
              throw s!"{msg} at {sizeTok.loc.line}:{sizeTok.loc.col}"
      | _ =>
          throw s!"Expected integer array size at {sizeTok.loc.line}:{sizeTok.loc.col}"
    let _ ← expectKind .rbracket "']'"
    pure (.array ty size)
  else
    pure ty

partial def parseDeclarator (baseTy : CType) : Parser (String × CType × Loc) := do
  let tyWithPointers : CType ← parsePointerSuffix baseTy
  let (name, nameLoc) ← expectIdent
  let finalTy : CType ← parseArraySuffix tyWithPointers
  pure (name, finalTy, nameLoc)

partial def parseVarDeclCore (expectSemi : Bool) : Parser Stmt := do
  let startTok : Token ← currentToken
  let baseTy : CType ← parseType
  let (name, declTy, _nameLoc) ← parseDeclarator baseTy
  let hasInit : Bool ← consumeIfKind .assign
  let initExpr : Option Expr ←
    if hasInit then
      let e : Expr ← parseExpr 0
      pure (some e)
    else
      pure none
  if expectSemi then
    let _ ← expectKind .semi "';'"
    pure ()
  else
    pure ()
  pure (.varDecl name declTy initExpr startTok.loc)

partial def parseFieldDecl : Parser (String × CType) := do
  let baseTy : CType ← parseType
  let (name, fieldTy, _nameLoc) ← parseDeclarator baseTy
  let _ ← expectKind .semi "';'"
  pure (name, fieldTy)

partial def parseStructFields (revAcc : List (String × CType)) : Parser (List (String × CType)) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .rbrace => pure revAcc.reverse
  | .eof => throw s!"Unexpected end of file in struct definition at {tok.loc.line}:{tok.loc.col}"
  | _ =>
      let fld : String × CType ← parseFieldDecl
      parseStructFields (fld :: revAcc)

partial def parseStructDef : Parser StructDef := do
  let startTok : Token ← expectKind .kw_struct "'struct'"
  let (name, _nameLoc) ← expectIdent
  let _ ← expectKind .lbrace "'{'"
  let fields : List (String × CType) ← parseStructFields []
  let _ ← expectKind .rbrace "'}'"
  let _ ← expectKind .semi "';'"
  pure { name := name, fields := fields, loc := startTok.loc }

partial def parseParam : Parser Param := do
  let baseTy : CType ← parseType
  let tyWithPointers : CType ← parsePointerSuffix baseTy
  let (name, _nameLoc) ← expectIdent
  pure { name := name, ty := tyWithPointers }

partial def parseParamsRest (revAcc : List Param) : Parser (List Param) := do
  let hasComma : Bool ← consumeIfKind .comma
  if hasComma then
    let nextParam : Param ← parseParam
    parseParamsRest (nextParam :: revAcc)
  else
    let _ ← expectKind .rparen "')'"
    pure revAcc.reverse

partial def parseParams : Parser (List Param) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .rparen =>
      let _ ← advance
      pure []
  | .kw_void =>
      let nextTok : Token ← peekTokenAt 1
      match nextTok.kind with
      | .rparen =>
          let _ ← advance
          let _ ← advance
          pure []
      | _ =>
          let first : Param ← parseParam
          parseParamsRest [first]
  | _ =>
      let first : Param ← parseParam
      parseParamsRest [first]

partial def parseForInit : Parser (Option Stmt) := do
  let tok : Token ← currentToken
  if tok.kind == .semi then
    let _ ← advance
    pure none
  else if isTypeStartKind tok.kind then
    let decl : Stmt ← parseVarDeclCore false
    let _ ← expectKind .semi "';'"
    pure (some decl)
  else
    let expr : Expr ← parseExpr 0
    let _ ← expectKind .semi "';'"
    pure (some (.exprStmt expr (Expr.loc expr)))

partial def parseForCond : Parser (Option Expr) := do
  let tok : Token ← currentToken
  if tok.kind == .semi then
    let _ ← advance
    pure none
  else
    let cond : Expr ← parseExpr 0
    let _ ← expectKind .semi "';'"
    pure (some cond)

partial def parseForStep : Parser (Option Expr) := do
  let tok : Token ← currentToken
  if tok.kind == .rparen then
    pure none
  else
    let stepExpr : Expr ← parseExpr 0
    pure (some stepExpr)

mutual

partial def parseStmt : Parser Stmt := do
  let tok : Token ← currentToken
  match tok.kind with
  | .lbrace => parseBlockStmt
  | .kw_if => parseIfStmt
  | .kw_while => parseWhileStmt
  | .kw_for => parseForStmt
  | .kw_return => parseReturnStmt
  | _ =>
      if isTypeStartKind tok.kind then
        parseVarDeclCore true
      else
        parseExprStmt

partial def parseBlockStmt : Parser Stmt := do
  let lbraceTok : Token ← expectKind .lbrace "'{'"
  let stmts : List Stmt ← parseStmtListUntilRBrace []
  pure (.block stmts lbraceTok.loc)

partial def parseStmtListUntilRBrace (revAcc : List Stmt) : Parser (List Stmt) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .rbrace =>
      let _ ← advance
      pure revAcc.reverse
  | .eof =>
      throw s!"Unexpected end of file in block at {tok.loc.line}:{tok.loc.col}"
  | _ =>
      let stmt : Stmt ← parseStmt
      parseStmtListUntilRBrace (stmt :: revAcc)

partial def parseBracedStmtList : Parser (List Stmt) := do
  let _ ← expectKind .lbrace "'{'"
  parseStmtListUntilRBrace []

partial def parseStmtBodyList : Parser (List Stmt) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .lbrace => parseBracedStmtList
  | _ =>
      let single : Stmt ← parseStmt
      pure [single]

partial def parseIfStmt : Parser Stmt := do
  let ifTok : Token ← expectKind .kw_if "'if'"
  let _ ← expectKind .lparen "'('"
  let cond : Expr ← parseExpr 0
  let _ ← expectKind .rparen "')'"
  let thenBody : List Stmt ← parseStmtBodyList
  let hasElse : Bool ← consumeIfKind .kw_else
  let elseBody : List Stmt ←
    if hasElse then
      parseStmtBodyList
    else
      pure []
  pure (.ifElse cond thenBody elseBody ifTok.loc)

partial def parseWhileStmt : Parser Stmt := do
  let whileTok : Token ← expectKind .kw_while "'while'"
  let _ ← expectKind .lparen "'('"
  let cond : Expr ← parseExpr 0
  let _ ← expectKind .rparen "')'"
  let body : List Stmt ← parseStmtBodyList
  pure (.while_ cond body whileTok.loc)

partial def parseForStmt : Parser Stmt := do
  let forTok : Token ← expectKind .kw_for "'for'"
  let _ ← expectKind .lparen "'('"
  let init : Option Stmt ← parseForInit
  let cond : Option Expr ← parseForCond
  let step : Option Expr ← parseForStep
  let _ ← expectKind .rparen "')'"
  let body : List Stmt ← parseStmtBodyList
  pure (.for_ init cond step body forTok.loc)

partial def parseReturnStmt : Parser Stmt := do
  let retTok : Token ← expectKind .kw_return "'return'"
  let endsNow : Bool ← consumeIfKind .semi
  if endsNow then
    pure (.ret none retTok.loc)
  else
    let value : Expr ← parseExpr 0
    let _ ← expectKind .semi "';'"
    pure (.ret (some value) retTok.loc)

partial def parseExprStmt : Parser Stmt := do
  let expr : Expr ← parseExpr 0
  let _ ← expectKind .semi "';'"
  pure (.exprStmt expr (Expr.loc expr))

end

partial def parseFunDef : Parser FunDef := do
  let startTok : Token ← currentToken
  let retBase : CType ← parseType
  let retTy : CType ← parsePointerSuffix retBase
  let (name, _nameLoc) ← expectIdent
  let _ ← expectKind .lparen "'('"
  let params : List Param ← parseParams
  let body : List Stmt ← parseBracedStmtList
  pure { name := name, ret := retTy, params := params, body := body, loc := startTok.loc }

def isStructDefStart : Parser Bool := do
  let t0 : Token ← peekTokenAt 0
  let t1 : Token ← peekTokenAt 1
  let t2 : Token ← peekTokenAt 2
  pure (
    match t0.kind, t1.kind, t2.kind with
    | .kw_struct, .ident _, .lbrace => true
    | _, _, _ => false
  )

partial def parseTopLevel (revStructs : List StructDef) (revFuns : List FunDef) : Parser Program := do
  let tok : Token ← currentToken
  match tok.kind with
  | .eof =>
      pure { structs := revStructs.reverse, functions := revFuns.reverse }
  | _ =>
      let structStart : Bool ← isStructDefStart
      if structStart then
        let sdef : StructDef ← parseStructDef
        parseTopLevel (sdef :: revStructs) revFuns
      else
        let fdef : FunDef ← parseFunDef
        parseTopLevel revStructs (fdef :: revFuns)

def parseProgramTokens : Parser Program :=
  parseTopLevel [] []

def parseProgram (source : String) : Except String Program := do
  let toks : List Token ← tokenize source
  runParser parseProgramTokens toks

end CCC.Parse
