import CCC.Parse.Lex

namespace CCC.Parse

open CCC.Syntax

structure ParseState where
  tokens : Array Token
  pos : Nat
  typedefNames : List String := []
  pendingGlobals : List GlobalDecl := []
  pendingExterns : List ExternDecl := []
  lastParamsVariadic : Bool := false
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
  | .kw_float | .kw_double | .kw_short | .kw_signed => true
  | .kw_enum | .kw_union | .kw_typedef => true
  | .kw_const | .kw_volatile | .kw_restrict => true
  | .kw_extern | .kw_static | .kw_inline | .kw_register => true
  | .ident _ => true  -- might be a typedef name; checked in context
  | _ => false

/-- Check if current token starts a type, considering known typedef names. -/
def isTypeStart : Parser Bool := do
  let tok ← currentToken
  match tok.kind with
  | .ident name =>
      let st ← get
      -- Only treat as type start if it's a known typedef name or size_t
      pure (name == "size_t" || st.typedefNames.contains name)
  | k => pure (isTypeStartKind k)

partial def parseType : Parser CType := do
  let tok : Token ← currentToken
  match tok.kind with
  | .kw_int =>
      let _ ← advance
      pure .int
  | .kw_char =>
      let _ ← advance
      pure .char
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
          -- check for "unsigned long long"
          let next : Token ← currentToken
          if next.kind == .kw_long then
            let _ ← advance
            pure (.unsigned .longLong)
          else
            pure (.unsigned .long)
      | .kw_short =>
          let _ ← advance
          pure (.unsigned .short)
      | _ =>
          pure (.unsigned .int)  -- bare "unsigned" means "unsigned int"
  | .kw_signed =>
      let _ ← advance
      let innerTok : Token ← currentToken
      match innerTok.kind with
      | .kw_int =>
          let _ ← advance
          pure (.signed .int)
      | .kw_char =>
          let _ ← advance
          pure (.signed .char)
      | .kw_long =>
          let _ ← advance
          pure (.signed .long)
      | .kw_short =>
          let _ ← advance
          pure (.signed .short)
      | _ =>
          pure .int  -- bare "signed" means "signed int" = "int"
  | .kw_short =>
      let _ ← advance
      -- "short" or "short int"
      let next : Token ← currentToken
      if next.kind == .kw_int then
        let _ ← advance
      pure .short
  | .kw_float =>
      let _ ← advance
      pure .float_
  | .kw_double =>
      let _ ← advance
      pure .double_
  | .kw_struct =>
      let _ ← advance
      let (name, _) ← expectIdent
      pure (.struct_ name)
  | .kw_union =>
      let _ ← advance
      let (name, _) ← expectIdent
      pure (.union_ name)
  | .kw_enum =>
      let _ ← advance
      let (name, _) ← expectIdent
      pure (.enum_ name)
  | .kw_const =>
      let _ ← advance
      let inner ← parseType
      pure (.const_ inner)
  | .kw_volatile =>
      let _ ← advance
      let inner ← parseType
      pure (.volatile_ inner)
  | .kw_restrict =>
      let _ ← advance
      let inner ← parseType
      pure (.restrict_ inner)
  -- Storage class specifiers — consume and parse the actual type
  | .kw_static | .kw_extern | .kw_inline | .kw_register =>
      let _ ← advance
      parseType
  | .kw_long =>
      let _ ← advance
      -- check for "long long", "long int", "long double"
      let next : Token ← currentToken
      match next.kind with
      | .kw_long =>
          let _ ← advance
          -- check for "long long int"
          let next2 : Token ← currentToken
          if next2.kind == .kw_int then
            let _ ← advance
          pure .longLong
      | .kw_double =>
          let _ ← advance
          pure .double_  -- long double → treat as double
      | .kw_int =>
          let _ ← advance
          pure .long
      | _ =>
          pure .long
  | .ident name =>
      if name = "size_t" then
        let _ ← advance
        pure .sizeT
      else
        -- Could be a typedef name — treat as typedef reference
        let _ ← advance
        pure (.typedef_ name)
  | _ =>
      throw s!"Expected type at {tok.loc.line}:{tok.loc.col}, found {tokenTextForError tok}"

inductive InfixOp where
  | bin (op : BinOp)
  | assign
  | ternary
  | compAssign (op : BinOp)
  | commaOp

def infixInfo (k : TokenKind) : Option (Nat × Bool × InfixOp) :=
  match k with
  -- Comma expression (lowest precedence, below assignment)
  -- NOTE: This means parseExpr(0) parses comma. Call parseExpr(1) for arg lists.
  | .comma => some (0, false, .commaOp)
  -- Assignment (right-assoc, prec 1)
  | .assign => some (1, true, .assign)
  | .plusAssign => some (1, true, .compAssign .addAssign)
  | .minusAssign => some (1, true, .compAssign .subAssign)
  | .starAssign => some (1, true, .compAssign .mulAssign)
  | .slashAssign => some (1, true, .compAssign .divAssign)
  | .percentAssign => some (1, true, .compAssign .modAssign)
  | .ampAssign => some (1, true, .compAssign .andAssign)
  | .pipeAssign => some (1, true, .compAssign .orAssign)
  | .caretAssign => some (1, true, .compAssign .xorAssign)
  | .shlAssign => some (1, true, .compAssign .shlAssign)
  | .shrAssign => some (1, true, .compAssign .shrAssign)
  -- Ternary (right-assoc, prec 2)
  | .question => some (2, true, .ternary)
  -- Logical
  | .logOr => some (3, false, .bin .or_)
  | .logAnd => some (4, false, .bin .and_)
  -- Bitwise
  | .pipe => some (5, false, .bin .bitOr)
  | .caret => some (6, false, .bin .bitXor)
  | .amp => none  -- ambiguous with address-of; handled in unary
  -- Equality
  | .eq => some (8, false, .bin .eq)
  | .ne => some (8, false, .bin .ne)
  -- Relational
  | .lt => some (9, false, .bin .lt)
  | .gt => some (9, false, .bin .gt)
  | .le => some (9, false, .bin .le)
  | .ge => some (9, false, .bin .ge)
  -- Shift
  | .shl => some (10, false, .bin .shl)
  | .shr => some (10, false, .bin .shr)
  -- Additive
  | .plus => some (11, false, .bin .add)
  | .minus => some (11, false, .bin .sub)
  -- Multiplicative
  | .star => some (12, false, .bin .mul)
  | .slash => some (12, false, .bin .div)
  | .percent => some (12, false, .bin .mod)
  | _ => none

partial def parsePointerSuffix (ty : CType) : Parser CType := do
  let tok : Token ← currentToken
  match tok.kind with
  | .star =>
      let _ ← advance
      -- Handle const/volatile/restrict after *
      let nextTok ← currentToken
      if nextTok.kind == .kw_const then
        let _ ← advance
        parsePointerSuffix (.const_ (.pointer ty))
      else if nextTok.kind == .kw_volatile then
        let _ ← advance
        parsePointerSuffix (.volatile_ (.pointer ty))
      else if nextTok.kind == .kw_restrict then
        let _ ← advance
        parsePointerSuffix (.restrict_ (.pointer ty))
      else
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
    match sizeTok.kind with
    | .intLit n =>
        match intToNatChecked n with
        | .ok v =>
            let _ ← advance
            let _ ← expectKind .rbracket "']'"
            pure (.array ty v)
        | .error msg =>
            throw s!"{msg} at {sizeTok.loc.line}:{sizeTok.loc.col}"
    | .rbracket =>
        -- T[] → pointer (unsized array)
        let _ ← advance
        pure (.pointer ty)
    | _ =>
        -- Complex expression as array size — skip to ]
        let rec skipToRBracket : Parser Unit := do
          let t ← currentToken
          match t.kind with
          | .rbracket => pure ()
          | .eof => pure ()
          | _ => let _ ← advance; skipToRBracket
        skipToRBracket
        let _ ← expectKind .rbracket "']'"
        pure (.array ty 0)  -- size 0 as placeholder
  else
    pure ty

mutual

partial def parseExpr (minPrec : Nat := 0) : Parser Expr := do
  let lhs : Expr ← parsePrimary
  parseExprLoop minPrec lhs

partial def parseExprLoop (minPrec : Nat) (lhs : Expr) : Parser Expr := do
  let tok : Token ← currentToken
  -- Handle bitwise AND specially (amp token is ambiguous with address-of)
  -- At expression level after a primary, amp must be infix bitwise AND
  if tok.kind == .amp then
    let bitwiseAndPrec : Nat := 7
    if bitwiseAndPrec < minPrec then
      pure lhs
    else
      let _ ← advance
      let rhs : Expr ← parseExpr (bitwiseAndPrec + 1)
      let combined : Expr := .binOp .bitAnd lhs rhs (Expr.loc lhs)
      parseExprLoop minPrec combined
  else
  match infixInfo tok.kind with
  | none => pure lhs
  | some (prec, rightAssoc, op) =>
      if prec < minPrec then
        pure lhs
      else
        let _ ← advance
        match op with
        | .ternary =>
            -- Parse: cond ? then : else
            let thenExpr : Expr ← parseExpr 0
            let _ ← expectKind .colon "':' in ternary"
            let elseExpr : Expr ← parseExpr prec  -- right-assoc
            let combined : Expr := .ternary lhs thenExpr elseExpr (Expr.loc lhs)
            parseExprLoop minPrec combined
        | .commaOp =>
            let rhs : Expr ← parseExpr (prec + 1)
            let combined : Expr := .comma lhs rhs (Expr.loc lhs)
            parseExprLoop minPrec combined
        | _ =>
            let rhsMinPrec : Nat := if rightAssoc then prec else prec + 1
            let rhs : Expr ← parseExpr rhsMinPrec
            let loc : Loc := Expr.loc lhs
            let combined : Expr :=
              match op with
              | .assign => .assign lhs rhs loc
              | .compAssign binOp => .binOp binOp lhs rhs loc
              | .bin binOp => .binOp binOp lhs rhs loc
              | .ternary => .intLit 0 loc   -- unreachable
              | .commaOp => .intLit 0 loc   -- unreachable
            parseExprLoop minPrec combined

partial def parsePrimary : Parser Expr := do
  let unary : Expr ← parseUnary
  parsePostfix unary

partial def parseInitListElems (acc : List Expr) : Parser (List Expr) := do
  let tok ← currentToken
  if tok.kind == .rbrace then pure acc.reverse
  else
    let tok2 ← currentToken
    if tok2.kind == .dot then
      let _ ← advance; let _ ← advance
      let _ ← consumeIfKind .assign
    else if tok2.kind == .lbracket then
      let _ ← advance
      let _ ← parseExpr 0
      let _ ← expectKind .rbracket "']'"
      let _ ← consumeIfKind .assign
    else pure ()
    let elem ← parseExpr 1
    let _ ← consumeIfKind .comma
    parseInitListElems (elem :: acc)

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
  | .tilde =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .bitNot operand tok.loc)
  | .plusPlus =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .preInc operand tok.loc)
  | .minusMinus =>
      let _ ← advance
      let operand : Expr ← parseUnary
      pure (.unOp .preDec operand tok.loc)
  | .kw_sizeof =>
      let _ ← advance
      let _ ← expectKind .lparen "'(' after sizeof"
      -- Try to parse as sizeof(type), fall back to sizeof(expr)
      let _saved ← get
      let _nextTok ← currentToken
      let mightBeType ← isTypeStart
      if mightBeType then
        let ty : CType ← parseType
        let ty ← parsePointerSuffix ty
        let _ ← expectKind .rparen "')' after sizeof(type)"
        pure (.sizeOf ty tok.loc)
      else
        -- sizeof(expr) — parse expression, treat as sizeof(int) for now
        let _ ← parseExpr 0
        let _ ← expectKind .rparen "')' after sizeof(expr)"
        pure (.sizeOf .int tok.loc)  -- approximate: treat as sizeof(int)
  | .lparen =>
      -- Could be: (expr), (type)expr (cast), or (type){init} (compound literal)
      -- Try cast: check if next tokens form a type
      let saved ← get
      let isCast ← do
        let _ ← advance  -- consume (
        let nextTok : Token ← currentToken
        let couldBeType ← isTypeStart
        if couldBeType then
          -- Looks like a cast: (type)expr or (type *)expr
          match nextTok.kind with
          | .ident name =>
              -- Check if it's a known typedef — then it IS a cast
              let st ← get
              pure (name == "size_t" || st.typedefNames.contains name)
          | .kw_struct | .kw_union | .kw_enum => pure true
          | _ => pure true
        else
          pure false
      set saved  -- restore state
      if isCast then
        let _ ← advance  -- consume (
        let castTy : CType ← parseType
        let castTy ← parsePointerSuffix castTy
        let _ ← expectKind .rparen "')' after cast type"
        -- Check for compound literal: (type){...}
        let nextT ← currentToken
        if nextT.kind == .lbrace then
          -- Compound literal — parse as initList
          let _ ← advance  -- consume {
          let elems ← parseInitListElems []
          let _ ← expectKind .rbrace "'}' in compound literal"
          pure (.cast castTy (.initList elems tok.loc) tok.loc)
        else
          let operand : Expr ← parseUnary
          pure (.cast castTy operand tok.loc)
      else
        parseAtom
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
  | .stringLit value =>
      let _ ← advance
      pure (.strLit value tok.loc)
  | .floatLit value =>
      let _ ← advance
      pure (.floatLit value tok.loc)
  | .kw_NULL =>
      let _ ← advance
      pure (.nullLit tok.loc)
  | .ident name =>
      let _ ← advance
      pure (.var name tok.loc)
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
    let first : Expr ← parseExpr 1  -- above comma precedence
    parseCallArgsRest [first]

partial def parseCallArgsRest (revArgs : List Expr) : Parser (List Expr) := do
  let hasComma : Bool ← consumeIfKind .comma
  if hasComma then
    let nextArg : Expr ← parseExpr 1  -- above comma precedence
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
          -- Function pointer call
          let node : Expr := .callFnPtr base args callLoc
          parsePostfix node
  | .plusPlus =>
      let _ ← advance
      let node : Expr := .unOp .postInc base (Expr.loc base)
      parsePostfix node
  | .minusMinus =>
      let _ ← advance
      let node : Expr := .unOp .postDec base (Expr.loc base)
      parsePostfix node
  | _ => pure base

end

partial def parseDeclarator (baseTy : CType) : Parser (String × CType × Loc) := do
  let tyWithPointers : CType ← parsePointerSuffix baseTy
  let (name, nameLoc) ← expectIdent
  let finalTy : CType ← parseArraySuffix tyWithPointers
  pure (name, finalTy, nameLoc)

partial def parseMoreDeclarators (baseTy : CType) : Parser (List Stmt) := do
  let hasComma ← consumeIfKind .comma
  if !hasComma then pure []
  else
    let startTok ← currentToken
    let (name, declTy, _) ← parseDeclarator baseTy
    let hasInit ← consumeIfKind .assign
    let initExpr ← if hasInit then do let e ← parseExpr 1; pure (some e) else pure none
    let decl := Stmt.varDecl name declTy initExpr startTok.loc
    let rest ← parseMoreDeclarators baseTy
    pure (decl :: rest)

partial def parseVarDeclCore (expectSemi : Bool) : Parser Stmt := do
  let startTok : Token ← currentToken
  let baseTy : CType ← parseType
  let (name, declTy, _nameLoc) ← parseDeclarator baseTy
  let hasInit : Bool ← consumeIfKind .assign
  let initExpr : Option Expr ←
    if hasInit then
      let initTok ← currentToken
      if initTok.kind == .lbrace then
        -- Brace initializer: int x[] = {1, 2, 3};
        let _ ← advance  -- consume {
        let elems ← parseInitListElems []
        let _ ← expectKind .rbrace "'}' in initializer list"
        pure (some (.initList elems initTok.loc))
      else
        let e : Expr ← parseExpr 0
        pure (some e)
    else
      pure none
  -- Handle multi-declaration: int a = 1, b, c = 3;
  let tok' ← currentToken
  if tok'.kind == .comma then
    -- Multi-decl: collect rest
    let first := Stmt.varDecl name declTy initExpr startTok.loc
    let rest ← parseMoreDeclarators baseTy
    if expectSemi then let _ ← expectKind .semi "';'" else pure ()
    -- Wrap in block
    pure (.block (first :: rest) startTok.loc)
  else
    if expectSemi then let _ ← expectKind .semi "';'" else pure ()
    pure (.varDecl name declTy initExpr startTok.loc)

partial def parseFieldDecl : Parser (String × CType) := do
  let baseTy : CType ← parseType
  let (name, fieldTy, _nameLoc) ← parseDeclarator baseTy
  let _ ← expectKind .semi "';'"
  pure (name, fieldTy)

partial def skipToColon (depth : Nat := 0) : Parser Unit := do
  let tok ← currentToken
  match tok.kind with
  | .colon => if depth == 0 then pure () else do let _ ← advance; skipToColon depth
  | .lparen => let _ ← advance; skipToColon (depth + 1)
  | .rparen => let _ ← advance; skipToColon (if depth > 0 then depth - 1 else 0)
  | .eof => pure ()
  | _ => let _ ← advance; skipToColon depth

partial def skipToEnumSep : Parser Unit := do
  let tok ← currentToken
  match tok.kind with
  | .comma | .rbrace => pure ()  -- don't consume; let caller handle
  | .eof => pure ()
  | _ => let _ ← advance; skipToEnumSep

partial def skipBraceContent (depth : Nat) : Parser Unit := do
  if depth == 0 then pure ()
  else
    let tok ← currentToken
    match tok.kind with
    | .lbrace => let _ ← advance; skipBraceContent (depth + 1)
    | .rbrace => let _ ← advance; skipBraceContent (depth - 1)
    | .eof => pure ()
    | _ => let _ ← advance; skipBraceContent depth

partial def skipBracketContent (depth : Nat) : Parser Unit := do
  if depth == 0 then pure ()
  else
    let tok ← currentToken
    match tok.kind with
    | .lbracket => let _ ← advance; skipBracketContent (depth + 1)
    | .rbracket => let _ ← advance; skipBracketContent (depth - 1)
    | .eof => pure ()
    | _ => let _ ← advance; skipBracketContent depth

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
  -- Save position, try field parsing, fallback to skip
  let saved ← get
  let fields ← do
    let result := (parseStructFields []).run saved
    match result with
    | (.ok fs, st') =>
        set st'
        pure fs
    | (.error _, _) =>
        -- Restore and skip entire body
        set saved
        skipBraceContent 1
        pure []
  -- If fields were parsed, consume the closing }
  let tok ← currentToken
  if tok.kind == .rbrace then let _ ← advance else pure ()
  let _ ← expectKind .semi "';'"
  pure { name := name, fields := fields, loc := startTok.loc }

partial def parseParam : Parser Param := do
  let baseTy : CType ← parseType
  let tyWithPointers : CType ← parsePointerSuffix baseTy
  -- Handle const after pointer (e.g., `const char *const p`)
  let tok ← currentToken
  let finalTy ←
    if tok.kind == .kw_const then
      let _ ← advance
      pure (.const_ tyWithPointers)
    else
      pure tyWithPointers
  let (name, _nameLoc) ← expectIdent
  -- Handle array suffix in params (e.g., `int arr[]`)
  let paramTy ← do
    let t ← currentToken
    if t.kind == .lbracket then
      let _ ← advance
      let nextT ← currentToken
      match nextT.kind with
      | .rbracket =>
          let _ ← advance
          pure (.pointer finalTy)  -- T[] decays to T*
      | .intLit n =>
          let _ ← advance
          let _ ← expectKind .rbracket "']'"
          pure (.array finalTy n.toNat)
      | _ =>
          let _ ← expectKind .rbracket "']'"
          pure (.pointer finalTy)
    else
      pure finalTy
  pure { name := name, ty := paramTy }

partial def parseParamsRest (revAcc : List Param) : Parser (List Param) := do
  let hasComma : Bool ← consumeIfKind .comma
  if hasComma then
    -- Check for ... (varargs)
    let tok ← currentToken
    if tok.kind == .ellipsis then
      let _ ← advance
      let _ ← expectKind .rparen "')' after '...'"
      modify fun st => { st with lastParamsVariadic := true }
      pure revAcc.reverse
    else
      let nextParam : Param ← parseParam
      parseParamsRest (nextParam :: revAcc)
  else
    let _ ← expectKind .rparen "')'"
    pure revAcc.reverse

partial def parseParams : Parser (List Param) := do
  modify fun st => { st with lastParamsVariadic := false }
  let tok : Token ← currentToken
  match tok.kind with
  | .rparen =>
      let _ ← advance
      pure []
  | .ellipsis =>
      let _ ← advance
      let _ ← expectKind .rparen "')' after '...'"
      modify fun st => { st with lastParamsVariadic := true }
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
  else
    let typeStart ← isTypeStart
    if typeStart then
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
  | .kw_switch => parseSwitchStmt
  | .kw_do => parseDoWhileStmt
  | .kw_break =>
      let _ ← advance
      let _ ← expectKind .semi "';' after break"
      pure (.break_ tok.loc)
  | .kw_continue =>
      let _ ← advance
      let _ ← expectKind .semi "';' after continue"
      pure (.continue_ tok.loc)
  | .kw_goto =>
      let _ ← advance
      let (labelName, _) ← expectIdent
      let _ ← expectKind .semi "';' after goto"
      pure (.goto_ labelName tok.loc)
  | .semi =>
      let _ ← advance
      pure (.emptyStmt tok.loc)
  | .ident _ =>
      -- Could be: label (ident:), typedef-based var decl, or expression stmt
      let nextTok ← peekTokenAt 1
      if nextTok.kind == .colon then
        -- Label: `name:`
        let (labelName, _) ← expectIdent
        let _ ← expectKind .colon "':' after label"
        let body ← parseStmt
        pure (.label_ labelName body tok.loc)
      else
        let ts ← isTypeStart
        if ts then parseVarDeclCore true
        else parseExprStmt
  | _ => do
      let ts ← isTypeStart
      if ts then parseVarDeclCore true
      else parseExprStmt

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

partial def parseSwitchStmt : Parser Stmt := do
  let switchTok : Token ← expectKind .kw_switch "'switch'"
  let _ ← expectKind .lparen "'('"
  let scrutinee : Expr ← parseExpr 0
  let _ ← expectKind .rparen "')'"
  let _ ← expectKind .lbrace "'{'"
  let cases ← parseSwitchCases []
  pure (.switch_ scrutinee cases switchTok.loc)

partial def parseSwitchCases (acc : List (Option Int × List Stmt × Loc))
    : Parser (List (Option Int × List Stmt × Loc)) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .rbrace =>
      let _ ← advance
      pure acc.reverse
  | .kw_case =>
      let _ ← advance
      let valTok : Token ← currentToken
      let caseVal : Int ←
        match valTok.kind with
        | .intLit v =>
            let _ ← advance
            pure v
        | .charLit v =>
            let _ ← advance
            pure (Int.ofNat v.toNat)
        | .minus =>
            let _ ← advance
            let numTok : Token ← currentToken
            match numTok.kind with
            | .intLit v =>
                let _ ← advance
                pure (-v)
            | _ => pure 0  -- approximate
        | _ =>
            -- Complex expression — skip to : at depth 0
            skipToColon
            pure 0
      let _ ← expectKind .colon "':' after case value"
      let body ← parseCaseBody []
      parseSwitchCases ((some caseVal, body, tok.loc) :: acc)
  | .kw_default =>
      let _ ← advance
      let _ ← expectKind .colon "':' after default"
      let body ← parseCaseBody []
      parseSwitchCases ((none, body, tok.loc) :: acc)
  | .eof => throw s!"Unexpected EOF in switch at {tok.loc.line}:{tok.loc.col}"
  | _ => throw s!"Expected case/default/}} in switch at {tok.loc.line}:{tok.loc.col}"

partial def parseCaseBody (acc : List Stmt) : Parser (List Stmt) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .kw_case | .kw_default | .rbrace => pure acc.reverse
  | _ =>
      let stmt ← parseStmt
      parseCaseBody (stmt :: acc)

partial def parseDoWhileStmt : Parser Stmt := do
  let doTok : Token ← expectKind .kw_do "'do'"
  let body : List Stmt ← parseStmtBodyList
  let _ ← expectKind .kw_while "'while' after do body"
  let _ ← expectKind .lparen "'('"
  let cond : Expr ← parseExpr 0
  let _ ← expectKind .rparen "')'"
  let _ ← expectKind .semi "';' after do-while"
  pure (.doWhile body cond doTok.loc)

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

partial def skipParenContent (depth : Nat) : Parser Unit := do
  if depth == 0 then pure ()
  else
    let tok ← currentToken
    match tok.kind with
    | .lparen => let _ ← advance; skipParenContent (depth + 1)
    | .rparen => let _ ← advance; skipParenContent (depth - 1)
    | .eof => pure ()
    | _ => let _ ← advance; skipParenContent depth

partial def skipToSemicolon : Parser Unit := do
  let tok ← currentToken
  if tok.kind == .semi then
    let _ ← advance
    pure ()
  else if tok.kind == .eof then
    pure ()
  else
    let _ ← advance
    skipToSemicolon

/-- Skip tokens until we reach a top-level boundary: semicolon at depth 0, or past a `}` at depth 0. -/
partial def skipToTopLevel (braceDepth : Nat := 0) : Parser Unit := do
  let tok ← currentToken
  match tok.kind with
  | .eof => pure ()
  | .semi =>
      let _ ← advance
      if braceDepth == 0 then pure ()
      else skipToTopLevel braceDepth
  | .lbrace => let _ ← advance; skipToTopLevel (braceDepth + 1)
  | .rbrace =>
      let _ ← advance
      if braceDepth <= 1 then
        -- Consume optional trailing semicolon
        let next ← currentToken
        if next.kind == .semi then let _ ← advance; pure () else pure ()
      else skipToTopLevel (braceDepth - 1)
  | _ => let _ ← advance; skipToTopLevel braceDepth



partial def parseFunDefOrProto : Parser (Option FunDef) := do
  let startTok : Token ← currentToken
  let retBase : CType ← parseType
  let retTy : CType ← parsePointerSuffix retBase
  -- Handle parenthesized names: `type (*name)(...)` or `type (name)(...)`
  let tok0 ← currentToken
  let name ← if tok0.kind == .lparen then do
      let tok1 ← peekTokenAt 1
      match tok1.kind with
      | .star =>
          -- Function pointer: type (*name)(params)
          let _ ← advance  -- (
          let _ ← advance  -- *
          let (n, _) ← expectIdent
          let _ ← expectKind .rparen "')'"
          pure n
      | .ident _ =>
          -- Parenthesized name: type (name)(params)
          let _ ← advance  -- (
          let (n, _) ← expectIdent
          let _ ← expectKind .rparen "')'"
          pure n
      | _ =>
          let (n, _) ← expectIdent
          pure n
    else do
      let (n, _) ← expectIdent
      pure n
  -- Check if this is a function declaration or a global variable
  let tok ← currentToken
  if tok.kind == .lparen then
    let _ ← advance  -- consume (
    let params : List Param ← parseParams
    -- Check: prototype (;) or definition ({)?
    let tok2 ← currentToken
    if tok2.kind == .semi then
      let _ ← advance  -- consume ; — this is a prototype, store as extern decl
      let st ← get
      let ext : ExternDecl := {
        name := name, ret := retTy, params := params,
        isVariadic := st.lastParamsVariadic, loc := startTok.loc
      }
      modify fun s => { s with pendingExterns := ext :: s.pendingExterns }
      pure none
    else
      let body : List Stmt ← parseBracedStmtList
      pure (some { name := name, ret := retTy, params := params, body := body, loc := startTok.loc })
  else if tok.kind == .semi then
    -- Global variable declaration: `type name;`
    let _ ← advance
    modify fun st => { st with pendingGlobals := {
      name := name, ty := retTy, init := none,
      isExtern := false, isStatic := false, loc := startTok.loc
    } :: st.pendingGlobals }
    pure none
  else if tok.kind == .assign then
    -- Global variable with initializer: `type name = expr;` or `= { ... };`
    let _ ← advance
    let initTok ← currentToken
    if initTok.kind == .lbrace then
      -- Brace initializer: skip entire { ... };
      let _ ← advance
      skipBraceContent 1
      let _ ← expectKind .semi "';'"
      modify fun st => { st with pendingGlobals := {
        name := name, ty := retTy, init := none,
        isExtern := false, isStatic := false, loc := startTok.loc
      } :: st.pendingGlobals }
    else
      -- Parse the initializer expression
      let initExpr ← parseExpr
      let _ ← expectKind .semi "';'"
      modify fun st => { st with pendingGlobals := {
        name := name, ty := retTy, init := some initExpr,
        isExtern := false, isStatic := false, loc := startTok.loc
      } :: st.pendingGlobals }
    pure none
  else if tok.kind == .lbracket then
    -- Global array: `type name[size]` optionally followed by `= { ... };` or `;`
    let _ ← advance
    -- Skip to `]` — consume the array dimension expression
    skipBracketContent 1
    let tok2 ← currentToken
    if tok2.kind == .assign then
      let _ ← advance
      let initTok ← currentToken
      if initTok.kind == .lbrace then
        let _ ← advance
        skipBraceContent 1
        let _ ← expectKind .semi "';'"
      else
        let _ ← skipToSemicolon
    else
      let _ ← expectKind .semi "';'"
    pure none
  else
    -- Try as function definition anyway
    let _ ← expectKind .lparen "'(' or ';'"
    let params : List Param ← parseParams
    let body : List Stmt ← parseBracedStmtList
    pure (some { name := name, ret := retTy, params := params, body := body, loc := startTok.loc })

/-- Try to parse a function def/proto; return Except to allow error recovery. -/
partial def parseFunDefOrProtoSafe : Parser (Except String (Option FunDef)) := do
  let saved ← get
  let result ← (do let r ← parseFunDefOrProto; pure (Except.ok r))
    <|> (do
      set saved
      pure (Except.error "parse failed"))
  pure result

def isStructDefStart : Parser Bool := do
  let t0 : Token ← peekTokenAt 0
  let t1 : Token ← peekTokenAt 1
  let t2 : Token ← peekTokenAt 2
  pure (
    match t0.kind, t1.kind, t2.kind with
    | .kw_struct, .ident _, .lbrace => true
    | _, _, _ => false
  )

def isUnionDefStart : Parser Bool := do
  let t0 : Token ← peekTokenAt 0
  let t1 : Token ← peekTokenAt 1
  let t2 : Token ← peekTokenAt 2
  pure (
    match t0.kind, t1.kind, t2.kind with
    | .kw_union, .ident _, .lbrace => true
    | _, _, _ => false
  )

partial def parseUnionDef : Parser UnionDef := do
  let startTok : Token ← expectKind .kw_union "'union'"
  let (name, _) ← expectIdent
  let _ ← expectKind .lbrace "'{'"
  let fields ← parseStructFields []
  let _ ← expectKind .rbrace "'}'"
  let _ ← expectKind .semi "';'"
  pure { name := name, fields := fields, loc := startTok.loc }

partial def parseEnumValues (acc : List (String × Option Int))
    : Parser (List (String × Option Int)) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .rbrace => pure acc.reverse
  | _ =>
      let (name, _) ← expectIdent
      let hasValue ← consumeIfKind .assign
      let value : Option Int ←
        if hasValue then
          let valTok ← currentToken
          match valTok.kind with
          | .intLit v =>
              let _ ← advance
              pure (some v)
          | .minus =>
              let _ ← advance
              let numTok ← currentToken
              match numTok.kind with
              | .intLit v => let _ ← advance; pure (some (-v))
              | _ =>
                  -- Complex expression — skip to , or }
                  skipToEnumSep
                  pure none
          | _ =>
              -- Complex expression — skip to , or }
              skipToEnumSep
              pure none
        else
          pure none
      -- Optional comma
      let _ ← consumeIfKind .comma
      parseEnumValues ((name, value) :: acc)

partial def parseEnumDef : Parser EnumDef := do
  let startTok : Token ← expectKind .kw_enum "'enum'"
  let (name, _) ← expectIdent
  let _ ← expectKind .lbrace "'{'"
  let values ← parseEnumValues []
  let _ ← expectKind .rbrace "'}'"
  let _ ← expectKind .semi "';'"
  pure { name := name, values := values, loc := startTok.loc }

partial def parseTypedefDecl : Parser TypedefDecl := do
  let startTok : Token ← expectKind .kw_typedef "'typedef'"
  -- Check for typedef struct/union { ... } name;
  let tok ← currentToken
  if tok.kind == .kw_struct || tok.kind == .kw_union || tok.kind == .kw_enum then
    let _ ← advance  -- consume struct/union
    let tok2 ← currentToken
    -- Could be: struct Name { ... } Alias; or struct { ... } Alias; or struct Name Alias;
    let tagName ← if tok2.kind != .lbrace then do
        let (n, _) ← expectIdent; pure (some n)
      else pure none
    let tok3 ← currentToken
    if tok3.kind == .lbrace then
      -- Skip the body { ... }
      let _ ← advance
      skipBraceContent 1
      let ty := if tok.kind == .kw_struct then CType.struct_ (tagName.getD "_anon")
        else if tok.kind == .kw_union then CType.union_ (tagName.getD "_anon")
        else CType.enum_ (tagName.getD "_anon")
      let finalTy ← parsePointerSuffix ty
      let (name, _) ← expectIdent
      let _ ← expectKind .semi "';'"
      modify fun st => { st with typedefNames := name :: st.typedefNames }
      pure { name := name, target := finalTy, loc := startTok.loc }
    else
      let ty := if tok.kind == .kw_struct then CType.struct_ (tagName.getD "_anon")
        else if tok.kind == .kw_union then CType.union_ (tagName.getD "_anon")
        else CType.enum_ (tagName.getD "_anon")
      let finalTy ← parsePointerSuffix ty
      let (name, _) ← expectIdent
      let _ ← expectKind .semi "';'"
      modify fun st => { st with typedefNames := name :: st.typedefNames }
      pure { name := name, target := finalTy, loc := startTok.loc }
  else
  let baseTy ← parseType
  let ty ← parsePointerSuffix baseTy
  -- Check for function pointer typedef: typedef int (*name)(params);
  let tok' ← currentToken
  if tok'.kind == .lparen then
    let nextTok ← peekTokenAt 1
    if nextTok.kind == .star then
      -- Function pointer typedef
      let _ ← advance  -- (
      let _ ← advance  -- *
      let (name, _) ← expectIdent
      let _ ← expectKind .rparen "')'"
      -- Skip the parameter list
      let _ ← expectKind .lparen "'('"
      skipParenContent 1
      let _ ← expectKind .semi "';'"
      modify fun st => { st with typedefNames := name :: st.typedefNames }
      pure { name := name, target := (.funcPtr ty []), loc := startTok.loc }
    else
      -- Parenthesized name? fall through to normal
      let (name, _) ← expectIdent
      let finalTy ← parseArraySuffix ty
      let _ ← expectKind .semi "';'"
      modify fun st => { st with typedefNames := name :: st.typedefNames }
      pure { name := name, target := finalTy, loc := startTok.loc }
  else
    let (name, _) ← expectIdent
    -- Handle array suffix
    let finalTy ← parseArraySuffix ty
    let _ ← expectKind .semi "';'"
    -- Register this typedef name so it can be used as a type later
    modify fun st => { st with typedefNames := name :: st.typedefNames }
    pure { name := name, target := finalTy, loc := startTok.loc }

structure TopLevel where
  structs   : List StructDef
  unions    : List UnionDef
  enums     : List EnumDef
  typedefs  : List TypedefDecl
  globals   : List GlobalDecl
  externs   : List ExternDecl
  functions : List FunDef

partial def parseTopLevelItem (tl : TopLevel) : Parser (Option TopLevel) := do
  let tok : Token ← currentToken
  match tok.kind with
  | .eof => pure none
  | .kw_typedef =>
      let td ← parseTypedefDecl
      pure (some { tl with typedefs := td :: tl.typedefs })
  | .kw_enum =>
      let ed ← parseEnumDef
      pure (some { tl with enums := ed :: tl.enums })
  | _ =>
      let unionStart ← isUnionDefStart
      if unionStart then
        let ud ← parseUnionDef
        pure (some { tl with unions := ud :: tl.unions })
      else
        let isForwardDecl ← do
          let t0 ← peekTokenAt 0; let t1 ← peekTokenAt 1; let t2 ← peekTokenAt 2
          pure ((t0.kind == .kw_struct || t0.kind == .kw_union) &&
                (match t1.kind with | .ident _ => true | _ => false) &&
                t2.kind == .semi)
        if isForwardDecl then
          let _ ← advance; let _ ← advance; let _ ← advance
          pure (some tl)
        else
        let structStart ← isStructDefStart
        if structStart then
          let sdef ← parseStructDef
          pure (some { tl with structs := sdef :: tl.structs })
        else
          let _ ← if tok.kind == .kw_static then advance *> pure () else pure ()
          let _ ← if tok.kind == .kw_extern then advance *> pure () else pure ()
          let _ ← if tok.kind == .kw_inline then advance *> pure () else pure ()
          -- Try to parse function/global; on failure, skip to next top-level item
          let saved ← get
          match ← parseFunDefOrProtoSafe with
          | .ok (some fdef) =>
              let st ← get
              let newGlobals := st.pendingGlobals
              let newExterns := st.pendingExterns
              modify fun s => { s with pendingGlobals := [], pendingExterns := [] }
              pure (some { tl with functions := fdef :: tl.functions,
                                    globals := newGlobals ++ tl.globals,
                                    externs := newExterns ++ tl.externs })
          | .ok none =>
              let st ← get
              let newGlobals := st.pendingGlobals
              let newExterns := st.pendingExterns
              modify fun s => { s with pendingGlobals := [], pendingExterns := [] }
              pure (some { tl with globals := newGlobals ++ tl.globals,
                                    externs := newExterns ++ tl.externs })
          | .error _ =>
              set saved
              modify fun s => { s with pendingGlobals := [], pendingExterns := [] }
              skipToTopLevel
              pure (some tl)

partial def parseTopLevelLoop (tl : TopLevel) : Parser Program := do
  match ← parseTopLevelItem tl with
  | none =>
      pure { structs := tl.structs.reverse, unions := tl.unions.reverse,
             enums := tl.enums.reverse, typedefs := tl.typedefs.reverse,
             globals := tl.globals.reverse, externs := tl.externs.reverse,
             functions := tl.functions.reverse }
  | some tl' => parseTopLevelLoop tl'

def parseProgramTokens : Parser Program :=
  let emptyTL : TopLevel := {
    structs := [], unions := [], enums := [], typedefs := [],
    globals := [], externs := [], functions := []
  }
  parseTopLevelLoop emptyTL

def parseProgram (source : String) : Except String Program := do
  let toks : List Token ← tokenize source
  runParser parseProgramTokens toks

end CCC.Parse
