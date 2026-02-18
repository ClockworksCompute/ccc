import CCC.Parse.Token

namespace CCC.Parse

open CCC.Syntax

def mkLoc (line : Nat) (col : Nat) : Loc :=
  { line := line, col := col }

def mkToken (kind : TokenKind) (line : Nat) (col : Nat) (text : String) : Token :=
  { kind := kind, loc := mkLoc line col, text := text }

def stepLoc (line : Nat) (col : Nat) (c : Char) : Nat × Nat :=
  if c = '\n' then
    (line + 1, 1)
  else
    (line, col + 1)

def isDigit (c : Char) : Bool :=
  let n : Nat := c.toNat
  let lo : Nat := '0'.toNat
  let hi : Nat := '9'.toNat
  lo ≤ n && n ≤ hi

def isLower (c : Char) : Bool :=
  let n : Nat := c.toNat
  let lo : Nat := 'a'.toNat
  let hi : Nat := 'z'.toNat
  lo ≤ n && n ≤ hi

def isUpper (c : Char) : Bool :=
  let n : Nat := c.toNat
  let lo : Nat := 'A'.toNat
  let hi : Nat := 'Z'.toNat
  lo ≤ n && n ≤ hi

def isAlpha (c : Char) : Bool :=
  isLower c || isUpper c

def isIdentStart (c : Char) : Bool :=
  isAlpha c || c = '_'

def isIdentContinue (c : Char) : Bool :=
  isIdentStart c || isDigit c

def isWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

def keywordKind? (name : String) : Option TokenKind :=
  match name with
  | "int" => some .kw_int
  | "char" => some .kw_char
  | "long" => some .kw_long
  | "unsigned" => some .kw_unsigned
  | "void" => some .kw_void
  | "bool" => some .kw_bool
  | "struct" => some .kw_struct
  | "if" => some .kw_if
  | "else" => some .kw_else
  | "while" => some .kw_while
  | "for" => some .kw_for
  | "return" => some .kw_return
  | "sizeof" => some .kw_sizeof
  -- malloc/free/memcpy are regular identifiers, not keywords
  -- The verifier detects them by name in call expressions
  -- Phase 2 keywords
  | "switch" => some .kw_switch
  | "case" => some .kw_case
  | "default" => some .kw_default
  | "break" => some .kw_break
  | "continue" => some .kw_continue
  | "do" => some .kw_do
  | "goto" => some .kw_goto
  | "enum" => some .kw_enum
  | "union" => some .kw_union
  | "typedef" => some .kw_typedef
  | "extern" => some .kw_extern
  | "static" => some .kw_static
  | "inline" => some .kw_inline
  | "register" => some .kw_register
  | "const" => some .kw_const
  | "volatile" => some .kw_volatile
  | "restrict" => some .kw_restrict
  | "float" => some .kw_float
  | "double" => some .kw_double
  | "short" => some .kw_short
  | "signed" => some .kw_signed
  | "NULL" => some .kw_NULL
  | _ => none

private def isHexDigit (c : Char) : Bool :=
  isDigit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

private def hexCharVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

partial def takeHexDigits (chars : Array Char) (i : Nat) (col : Nat) (acc : List Char)
    : List Char × Nat × Nat :=
  match chars[i]? with
  | some c =>
      if isHexDigit c then
        takeHexDigits chars (i + 1) (col + 1) (c :: acc)
      else
        (acc.reverse, i, col)
  | none => (acc.reverse, i, col)

def hexDigitsToNat (digits : List Char) : Nat :=
  digits.foldl (fun acc d => acc * 16 + hexCharVal d) 0

def consumeIntSuffix (chars : Array Char) (i : Nat) (col : Nat) : Nat × Nat :=
  let consume1 (i : Nat) (col : Nat) : Nat × Nat :=
    match chars[i]? with
    | some 'u' | some 'U' => (i + 1, col + 1)
    | some 'l' | some 'L' =>
        match chars[i + 1]? with
        | some 'l' | some 'L' => (i + 2, col + 2)
        | _ => (i + 1, col + 1)
    | _ => (i, col)
  let (i1, c1) := consume1 i col
  if i1 > i then
    -- Try another suffix (e.g. UL, LU, ULL, LLU)
    consume1 i1 c1
  else (i, col)

def digitsToNat (digits : List Char) : Nat :=
  digits.foldl
    (fun (acc : Nat) (d : Char) =>
      let v : Nat := d.toNat - '0'.toNat
      acc * 10 + v)
    0

partial def takeDigits (chars : Array Char) (i : Nat) (col : Nat) (acc : List Char)
    : List Char × Nat × Nat :=
  match chars[i]? with
  | some c =>
      if isDigit c then
        takeDigits chars (i + 1) (col + 1) (c :: acc)
      else
        (acc.reverse, i, col)
  | none => (acc.reverse, i, col)

partial def takeIdent (chars : Array Char) (i : Nat) (col : Nat) (acc : List Char)
    : List Char × Nat × Nat :=
  match chars[i]? with
  | some c =>
      if isIdentContinue c then
        takeIdent chars (i + 1) (col + 1) (c :: acc)
      else
        (acc.reverse, i, col)
  | none => (acc.reverse, i, col)

partial def skipLineComment (chars : Array Char) (i : Nat) (line : Nat) (col : Nat)
    : Nat × Nat × Nat :=
  match chars[i]? with
  | none => (i, line, col)
  | some c =>
      let (line', col') := stepLoc line col c
      if c = '\n' then
        (i + 1, line', col')
      else
        skipLineComment chars (i + 1) line' col'

partial def skipBlockComment (chars : Array Char) (i : Nat) (line : Nat) (col : Nat)
    (startLine : Nat) (startCol : Nat) : Except String (Nat × Nat × Nat) := do
  match chars[i]? with
  | none =>
      throw s!"Unterminated block comment starting at {startLine}:{startCol}"
  | some c =>
      if c = '*' then
        match chars[i + 1]? with
        | some '/' =>
            let (line1, col1) := stepLoc line col '*'
            let (line2, col2) := stepLoc line1 col1 '/'
            pure (i + 2, line2, col2)
        | _ =>
            let (line', col') := stepLoc line col c
            skipBlockComment chars (i + 1) line' col' startLine startCol
      else
        let (line', col') := stepLoc line col c
        skipBlockComment chars (i + 1) line' col' startLine startCol

partial def readStringLiteral (chars : Array Char) (i : Nat) (line : Nat) (col : Nat)
    (startLine : Nat) (startCol : Nat) (acc : List Char)
    : Except String (List Char × Nat × Nat × Nat) := do
  match chars[i]? with
  | none =>
      throw s!"Unterminated string literal at {startLine}:{startCol}"
  | some c =>
      if c = '"' then
        let (line', col') := stepLoc line col '"'
        pure (acc.reverse, i + 1, line', col')
      else if c = '\n' then
        throw s!"Unterminated string literal at {startLine}:{startCol}"
      else if c = '\\' then
        -- Escape sequence
        match chars[i + 1]? with
        | some escChar =>
            let resolved : Char :=
              if escChar = 'n' then '\n'
              else if escChar = 't' then '\t'
              else if escChar = '0' then (Char.ofNat 0)
              else if escChar = '\\' then '\\'
              else if escChar = '"' then '"'
              else if escChar = '\'' then '\''
              else escChar
            let (l1, c1) := stepLoc line col '\\'
            let (l2, c2) := stepLoc l1 c1 escChar
            readStringLiteral chars (i + 2) l2 c2 startLine startCol (resolved :: acc)
        | none => throw s!"Unterminated escape in string literal at {startLine}:{startCol}"
      else
        let (line', col') := stepLoc line col c
        readStringLiteral chars (i + 1) line' col' startLine startCol (c :: acc)

partial def tokenizeLoop (chars : Array Char) (i : Nat) (line : Nat) (col : Nat)
    (acc : List Token) : Except String (List Token) := do
  match chars[i]? with
  | none =>
      let eofTok : Token := mkToken .eof line col ""
      pure ((eofTok :: acc).reverse)
  | some c =>
      if isWhitespace c then
        let (line', col') := stepLoc line col c
        tokenizeLoop chars (i + 1) line' col' acc
      else if c = '/' then
        match chars[i + 1]? with
        | some '/' =>
            let (line1, col1) := stepLoc line col '/'
            let (line2, col2) := stepLoc line1 col1 '/'
            let (i', line', col') := skipLineComment chars (i + 2) line2 col2
            tokenizeLoop chars i' line' col' acc
        | some '*' =>
            let (line1, col1) := stepLoc line col '/'
            let (line2, col2) := stepLoc line1 col1 '*'
            let (i', line', col') ← skipBlockComment chars (i + 2) line2 col2 line col
            tokenizeLoop chars i' line' col' acc
        | some '=' =>
            let tok : Token := mkToken .slashAssign line col "/="
            let (l1, c1) := stepLoc line col '/'
            let (l2, c2) := stepLoc l1 c1 '='
            tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .slash line col "/"
            let (line', col') := stepLoc line col '/'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '0' && (chars[i + 1]? == some 'x' || chars[i + 1]? == some 'X') then
        -- Hex literal
        let (hexDigits, i', col') := takeHexDigits chars (i + 2) (col + 2) []
        let hexVal := hexDigitsToNat hexDigits
        let text := "0x" ++ String.ofList hexDigits
        let (i', col') := consumeIntSuffix chars i' col'
        let tok : Token := mkToken (.intLit (Int.ofNat hexVal)) line col text
        tokenizeLoop chars i' line col' (tok :: acc)
      else if isDigit c then
        let (digits, i', col') := takeDigits chars i col []
        -- Check for float literal (digits followed by '.')
        match chars[i']? with
        | some '.' =>
            let (fracDigits, i'', col'') := takeDigits chars (i' + 1) (col' + 1) []
            let intPart := digitsToNat digits
            let fracPart := digitsToNat fracDigits
            let fracLen := fracDigits.length
            let divisor := Nat.pow 10 fracLen
            let floatVal : Float := Float.ofInt (Int.ofNat intPart) +
              Float.ofInt (Int.ofNat fracPart) / Float.ofInt (Int.ofNat divisor)
            let text : String := String.ofList digits ++ "." ++ String.ofList fracDigits
            -- Consume optional float suffix F/f/L/l
            let (i'', col'') := match chars[i'']? with
              | some 'f' | some 'F' | some 'l' | some 'L' => (i'' + 1, col'' + 1)
              | _ => (i'', col'')
            let tok : Token := mkToken (.floatLit floatVal) line col text
            tokenizeLoop chars i'' line col'' (tok :: acc)
        | _ =>
            let text : String := String.ofList digits
            let value : Int := Int.ofNat (digitsToNat digits)
            -- Consume optional integer suffixes: u/U, l/L, ll/LL, ul/UL, etc.
            let (i', col') := consumeIntSuffix chars i' col'
            let tok : Token := mkToken (.intLit value) line col text
            tokenizeLoop chars i' line col' (tok :: acc)
      else if isIdentStart c then
        let (charsIdent, i', col') := takeIdent chars i col []
        let name : String := String.ofList charsIdent
        let kind : TokenKind :=
          match keywordKind? name with
          | some kw => kw
          | none => .ident name
        let tok : Token := mkToken kind line col name
        tokenizeLoop chars i' line col' (tok :: acc)
      else if c = '\'' then
        match chars[i + 1]? with
        | some '\\' =>
            -- Escape sequence in char literal
            match chars[i + 2]?, chars[i + 3]? with
            | some escChar, some '\'' =>
                let resolved : Char :=
                  if escChar = 'n' then '\n'
                  else if escChar = 't' then '\t'
                  else if escChar = '0' then (Char.ofNat 0)
                  else if escChar = '\\' then '\\'
                  else if escChar = '\'' then '\''
                  else escChar
                let text : String := String.ofList ['\'', '\\', escChar, '\'']
                let tok : Token := mkToken (.charLit resolved) line col text
                let (l1, c1) := stepLoc line col '\''
                let (l2, c2) := stepLoc l1 c1 '\\'
                let (l3, c3) := stepLoc l2 c2 escChar
                let (l4, c4) := stepLoc l3 c3 '\''
                tokenizeLoop chars (i + 4) l4 c4 (tok :: acc)
            | _, _ => throw s!"Invalid escape in character literal at {line}:{col}"
        | some valueChar =>
            match chars[i + 2]? with
            | some '\'' =>
                if valueChar = '\n' then
                  throw s!"Invalid character literal at {line}:{col}"
                else
                  let text : String := String.ofList ['\'', valueChar, '\'']
                  let tok : Token := mkToken (.charLit valueChar) line col text
                  let (line1, col1) := stepLoc line col '\''
                  let (line2, col2) := stepLoc line1 col1 valueChar
                  let (line3, col3) := stepLoc line2 col2 '\''
                  tokenizeLoop chars (i + 3) line3 col3 (tok :: acc)
            | _ => throw s!"Invalid character literal at {line}:{col}"
        | _ =>
            throw s!"Invalid character literal at {line}:{col}"
      else if c = '"' then
        let (line1, col1) := stepLoc line col '"'
        let (content, i', line', col') ←
          readStringLiteral chars (i + 1) line1 col1 line col []
        let value : String := String.ofList content
        let text : String := String.ofList (('"' :: content) ++ ['"'])
        let tok : Token := mkToken (.stringLit value) line col text
        tokenizeLoop chars i' line' col' (tok :: acc)
      else if c = '-' then
        match chars[i + 1]? with
        | some '>' =>
            let tok : Token := mkToken .arrow line col "->"
            let (line1, col1) := stepLoc line col '-'
            let (line2, col2) := stepLoc line1 col1 '>'
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | some '-' =>
            let tok : Token := mkToken .minusMinus line col "--"
            let (line1, col1) := stepLoc line col '-'
            let (line2, col2) := stepLoc line1 col1 '-'
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | some '=' =>
            let tok : Token := mkToken .minusAssign line col "-="
            let (line1, col1) := stepLoc line col '-'
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .minus line col "-"
            let (line', col') := stepLoc line col '-'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '&' then
        match chars[i + 1]? with
        | some '&' =>
            let tok : Token := mkToken .logAnd line col "&&"
            let (line1, col1) := stepLoc line col '&'
            let (line2, col2) := stepLoc line1 col1 '&'
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | some '=' =>
            let tok : Token := mkToken .ampAssign line col "&="
            let (line1, col1) := stepLoc line col '&'
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .amp line col "&"
            let (line', col') := stepLoc line col '&'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '|' then
        match chars[i + 1]? with
        | some '|' =>
            let tok : Token := mkToken .logOr line col "||"
            let (line1, col1) := stepLoc line col '|'
            let (line2, col2) := stepLoc line1 col1 '|'
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | some '=' =>
            let tok : Token := mkToken .pipeAssign line col "|="
            let (line1, col1) := stepLoc line col '|'
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .pipe line col "|"
            let (line', col') := stepLoc line col '|'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '=' then
        match chars[i + 1]? with
        | some '=' =>
            let tok : Token := mkToken .eq line col "=="
            let (line1, col1) := stepLoc line col '='
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .assign line col "="
            let (line', col') := stepLoc line col '='
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '!' then
        match chars[i + 1]? with
        | some '=' =>
            let tok : Token := mkToken .ne line col "!="
            let (line1, col1) := stepLoc line col '!'
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .bang line col "!"
            let (line', col') := stepLoc line col '!'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '<' then
        match chars[i + 1]? with
        | some '<' =>
            match chars[i + 2]? with
            | some '=' =>
                let tok : Token := mkToken .shlAssign line col "<<="
                let (l1, c1) := stepLoc line col '<'
                let (l2, c2) := stepLoc l1 c1 '<'
                let (l3, c3) := stepLoc l2 c2 '='
                tokenizeLoop chars (i + 3) l3 c3 (tok :: acc)
            | _ =>
                let tok : Token := mkToken .shl line col "<<"
                let (l1, c1) := stepLoc line col '<'
                let (l2, c2) := stepLoc l1 c1 '<'
                tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
        | some '=' =>
            let tok : Token := mkToken .le line col "<="
            let (line1, col1) := stepLoc line col '<'
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .lt line col "<"
            let (line', col') := stepLoc line col '<'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if c = '>' then
        match chars[i + 1]? with
        | some '>' =>
            match chars[i + 2]? with
            | some '=' =>
                let tok : Token := mkToken .shrAssign line col ">>="
                let (l1, c1) := stepLoc line col '>'
                let (l2, c2) := stepLoc l1 c1 '>'
                let (l3, c3) := stepLoc l2 c2 '='
                tokenizeLoop chars (i + 3) l3 c3 (tok :: acc)
            | _ =>
                let tok : Token := mkToken .shr line col ">>"
                let (l1, c1) := stepLoc line col '>'
                let (l2, c2) := stepLoc l1 c1 '>'
                tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
        | some '=' =>
            let tok : Token := mkToken .ge line col ">="
            let (line1, col1) := stepLoc line col '>'
            let (line2, col2) := stepLoc line1 col1 '='
            tokenizeLoop chars (i + 2) line2 col2 (tok :: acc)
        | _ =>
            let tok : Token := mkToken .gt line col ">"
            let (line', col') := stepLoc line col '>'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else
        let simple : Option (TokenKind × String × Char) :=
          if c = '(' then some (.lparen, "(", '(')
          else if c = ')' then some (.rparen, ")", ')')
          else if c = '{' then some (.lbrace, "{", '{')
          else if c = '}' then some (.rbrace, "}", '}')
          else if c = '[' then some (.lbracket, "[", '[')
          else if c = ']' then some (.rbracket, "]", ']')
          else if c = ';' then some (.semi, ";", ';')
          else if c = ',' then some (.comma, ",", ',')
          else if c = '.' then
              match chars[i + 1]?, chars[i + 2]? with
              | some '.', some '.' =>
                  none  -- handled below for ellipsis
              | _, _ => some (.dot, ".", '.')
          else if c = '~' then some (.tilde, "~", '~')
          else if c = '?' then some (.question, "?", '?')
          else if c = ':' then some (.colon, ":", ':')
          else none
        match simple with
        | some (kind, text, consumed) =>
            let tok : Token := mkToken kind line col text
            let (line', col') := stepLoc line col consumed
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
        | none =>
            -- Multi-char operators that need lookahead
            if c = '+' then
              match chars[i + 1]? with
              | some '+' =>
                  let tok : Token := mkToken .plusPlus line col "++"
                  let (l1, c1) := stepLoc line col '+'
                  let (l2, c2) := stepLoc l1 c1 '+'
                  tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
              | some '=' =>
                  let tok : Token := mkToken .plusAssign line col "+="
                  let (l1, c1) := stepLoc line col '+'
                  let (l2, c2) := stepLoc l1 c1 '='
                  tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
              | _ =>
                  let tok : Token := mkToken .plus line col "+"
                  let (line', col') := stepLoc line col '+'
                  tokenizeLoop chars (i + 1) line' col' (tok :: acc)
            else if c = '*' then
              match chars[i + 1]? with
              | some '=' =>
                  let tok : Token := mkToken .starAssign line col "*="
                  let (l1, c1) := stepLoc line col '*'
                  let (l2, c2) := stepLoc l1 c1 '='
                  tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
              | _ =>
                  let tok : Token := mkToken .star line col "*"
                  let (line', col') := stepLoc line col '*'
                  tokenizeLoop chars (i + 1) line' col' (tok :: acc)
            else if c = '%' then
              match chars[i + 1]? with
              | some '=' =>
                  let tok : Token := mkToken .percentAssign line col "%="
                  let (l1, c1) := stepLoc line col '%'
                  let (l2, c2) := stepLoc l1 c1 '='
                  tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
              | _ =>
                  let tok : Token := mkToken .percent line col "%"
                  let (line', col') := stepLoc line col '%'
                  tokenizeLoop chars (i + 1) line' col' (tok :: acc)
            else if c = '^' then
              match chars[i + 1]? with
              | some '=' =>
                  let tok : Token := mkToken .caretAssign line col "^="
                  let (l1, c1) := stepLoc line col '^'
                  let (l2, c2) := stepLoc l1 c1 '='
                  tokenizeLoop chars (i + 2) l2 c2 (tok :: acc)
              | _ =>
                  let tok : Token := mkToken .caret line col "^"
                  let (line', col') := stepLoc line col '^'
                  tokenizeLoop chars (i + 1) line' col' (tok :: acc)
            else if c = '.' then
              -- Must be ellipsis (simple dot handled above)
              match chars[i + 1]?, chars[i + 2]? with
              | some '.', some '.' =>
                  let tok : Token := mkToken .ellipsis line col "..."
                  let (l1, c1) := stepLoc line col '.'
                  let (l2, c2) := stepLoc l1 c1 '.'
                  let (l3, c3) := stepLoc l2 c2 '.'
                  tokenizeLoop chars (i + 3) l3 c3 (tok :: acc)
              | _, _ =>
                  let tok : Token := mkToken .dot line col "."
                  let (line', col') := stepLoc line col '.'
                  tokenizeLoop chars (i + 1) line' col' (tok :: acc)
            else if c == '#' then
              -- Skip preprocessor artifacts (e.g., # stringification remnants)
              -- Skip to end of line
              let rec skipLine (i : Nat) (col : Nat) : Nat × Nat :=
                match chars[i]? with
                | some '\n' => (i, col)
                | some _ => skipLine (i + 1) (col + 1)
                | none => (i, col)
              let (i', col') := skipLine (i + 1) (col + 1)
              tokenizeLoop chars i' line col' acc
            else
              -- Skip unknown characters with a warning (robust for real-world C)
              tokenizeLoop chars (i + 1) line (col + 1) acc

/-- Merge adjacent string literals (C string concatenation).
    Tail-recursive via accumulator to avoid stack overflow on large token lists. -/
partial def mergeAdjacentStrings (tokens : List Token) : List Token :=
  go tokens []
where
  go : List Token → List Token → List Token
    | [], acc => acc.reverse
    | [t], acc => (t :: acc).reverse
    | t1 :: t2 :: rest, acc =>
        match t1.kind, t2.kind with
        | .stringLit s1, .stringLit s2 =>
            go ({ t1 with kind := .stringLit (s1 ++ s2) } :: rest) acc
        | _, _ => go (t2 :: rest) (t1 :: acc)

partial def tokenize (source : String) : Except String (List Token) := do
  let chars : Array Char := source.toList.toArray
  let tokens ← tokenizeLoop chars 0 1 1 []
  pure (mergeAdjacentStrings tokens)

end CCC.Parse
