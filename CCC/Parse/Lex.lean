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
  | "malloc" => some .kw_malloc
  | "free" => some .kw_free
  | "memcpy" => some .kw_memcpy
  | _ => none

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
        | _ =>
            let tok : Token := mkToken .slash line col "/"
            let (line', col') := stepLoc line col '/'
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
      else if isDigit c then
        let (digits, i', col') := takeDigits chars i col []
        let text : String := String.ofList digits
        let value : Int := Int.ofNat (digitsToNat digits)
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
        match chars[i + 1]?, chars[i + 2]? with
        | some valueChar, some '\'' =>
            if valueChar = '\n' then
              throw s!"Invalid character literal at {line}:{col}"
            else
              let text : String := String.ofList ['\'', valueChar, '\'']
              let tok : Token := mkToken (.charLit valueChar) line col text
              let (line1, col1) := stepLoc line col '\''
              let (line2, col2) := stepLoc line1 col1 valueChar
              let (line3, col3) := stepLoc line2 col2 '\''
              tokenizeLoop chars (i + 3) line3 col3 (tok :: acc)
        | _, _ =>
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
        | _ =>
            throw s!"Unexpected character '|' at {line}:{col}"
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
          else if c = '.' then some (.dot, ".", '.')
          else if c = '*' then some (.star, "*", '*')
          else if c = '+' then some (.plus, "+", '+')
          else if c = '%' then some (.percent, "%", '%')
          else none
        match simple with
        | some (kind, text, consumed) =>
            let tok : Token := mkToken kind line col text
            let (line', col') := stepLoc line col consumed
            tokenizeLoop chars (i + 1) line' col' (tok :: acc)
        | none =>
            throw s!"Unexpected character '{c}' at {line}:{col}"

partial def tokenize (source : String) : Except String (List Token) := do
  let chars : Array Char := source.toList.toArray
  tokenizeLoop chars 0 1 1 []

end CCC.Parse
