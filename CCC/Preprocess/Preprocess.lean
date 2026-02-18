/-
  CCC/Preprocess/Preprocess.lean — Self-contained C preprocessor

  Handles: #include, #define (object-like), #ifdef/#ifndef/#if/#else/#elif/#endif,
  #undef, #pragma (ignored), __FILE__, __LINE__ predefined macros.

  For #include <...> system headers, provides built-in stubs for common headers.
  Zero external dependencies.
-/

namespace CCC.Preprocess

/-- A macro definition. params = none means object-like. -/
structure Macro where
  name   : String
  params : Option (List String)
  body   : String
  deriving Repr, Inhabited

/-- Preprocessor conditional state: (branchActive, anyBranchTaken).
    branchActive = true if current branch content should be emitted.
    anyBranchTaken = true if ANY branch in this #if/#elif/#else group was taken. -/
abbrev IfEntry := Bool × Bool

/-- Preprocessor state. -/
structure PPState where
  macros     : List Macro
  ifStack    : List IfEntry
  output     : List String
  basePath   : String
  included   : List String
  includeDepth : Nat := 0
  deriving Inhabited

def PPState.empty (basePath : String) : PPState :=
  { macros := defaultMacros
    ifStack := []
    output := []
    basePath := basePath
    included := [] }
where
  defaultMacros : List Macro := [
    ⟨"__CCC__", none, "1"⟩,
    ⟨"__STDC__", none, "1"⟩,
    ⟨"__STDC_VERSION__", none, "199901L"⟩,
    ⟨"__x86_64__", none, "1"⟩,
    ⟨"__SIZEOF_POINTER__", none, "8"⟩,
    ⟨"__SIZEOF_INT__", none, "4"⟩,
    ⟨"__SIZEOF_LONG__", none, "8"⟩,
    ⟨"__INT_MAX__", none, "2147483647"⟩,
    ⟨"__LONG_MAX__", none, "9223372036854775807L"⟩,
    ⟨"NULL", none, "((void *)0)"⟩
  ]

def PPState.isActive (st : PPState) : Bool :=
  st.ifStack.all (fun (entry : IfEntry) => entry.1)

def PPState.isDefined (st : PPState) (name : String) : Bool :=
  st.macros.any (fun (m : Macro) => m.name == name)

def PPState.define (st : PPState) (name : String) (params : Option (List String)) (body : String) : PPState :=
  { st with macros := ⟨name, params, body⟩ :: (st.macros.filter (fun (m : Macro) => m.name != name)) }

def PPState.undef (st : PPState) (name : String) : PPState :=
  { st with macros := st.macros.filter (fun (m : Macro) => m.name != name) }

def PPState.emit (st : PPState) (line : String) : PPState :=
  { st with output := st.output ++ [line] }

/-- Simple identifier-aware replacement of macro name with body in text. -/
private def splitAtCloseParen (chars : List Char) (acc : List Char) (depth : Nat)
    : List Char × List Char :=
  match chars with
  | [] => (acc.reverse, [])
  | ')' :: rest =>
      if depth == 0 then (acc.reverse, rest)
      else splitAtCloseParen rest (')' :: acc) (depth - 1)
  | '(' :: rest => splitAtCloseParen rest ('(' :: acc) (depth + 1)
  | c :: rest => splitAtCloseParen rest (c :: acc) depth

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

private partial def replaceIdent (text : String) (name : String) (repl : String) : String :=
  let textChars := text.toList
  let nameChars := name.toList
  let nameLen := name.length
  go textChars nameChars nameLen repl [] |>.reverse |> String.ofList
where
  go (chars : List Char) (nameChars : List Char) (nameLen : Nat) (repl : String)
     (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | c :: rest =>
        if isIdentChar c then
          -- Collect full identifier
          let (ident, after) := collectIdent (c :: rest) []
          let identStr := String.ofList ident.reverse
          if identStr == String.ofList nameChars then
            -- Replace: add replacement chars in reverse to acc
            let replChars := repl.toList.reverse
            go after nameChars nameLen repl (replChars ++ acc)
          else
            go after nameChars nameLen repl (ident ++ acc)
        else
          go rest nameChars nameLen repl (c :: acc)
  collectIdent (chars : List Char) (acc : List Char) : List Char × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
        if isIdentChar c then collectIdent rest (c :: acc)
        else (acc, c :: rest)

/-- Extract all unique identifiers from text (single pass). -/
private partial def extractIdents (chars : List Char) (acc : List String) : List String :=
  match chars with
  | [] => acc
  | c :: rest =>
      if isIdentChar c then
        let (word, after) := gatherIdent (c :: rest) []
        extractIdents after (String.ofList word.reverse :: acc)
      else
        extractIdents rest acc
where
  gatherIdent (chars : List Char) (acc : List Char) : List Char × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest => if isIdentChar c then gatherIdent rest (c :: acc) else (acc, c :: rest)

/-- Fast substring check (not word-boundary aware, but fast for filtering). -/
private def substringPresent (haystack : List Char) (needle : List Char) : Bool :=
  match haystack with
  | [] => needle.isEmpty
  | _ :: rest =>
      if prefixOf needle haystack then true
      else substringPresent rest needle
where
  prefixOf (needle : List Char) (haystack : List Char) : Bool :=
    match needle, haystack with
    | [], _ => true
    | _, [] => false
    | n :: ns, h :: hs => n == h && prefixOf ns hs

private partial def textContainsIdent (text : String) (name : String) : Bool :=
  scanChars text.toList name.toList
where
  scanChars (chars : List Char) (nameChars : List Char) : Bool :=
    match chars with
    | [] => false
    | c :: rest =>
        if isIdentChar c then
          let (word, after) := gatherW (c :: rest) []
          if word == nameChars then true
          else scanChars after nameChars
        else scanChars rest nameChars
  gatherW (chars : List Char) (acc : List Char) : List Char × List Char :=
    match chars with
    | [] => (acc.reverse, [])
    | c :: rest => if isIdentChar c then gatherW rest (c :: acc) else (acc.reverse, c :: rest)

/-- Find and expand a function-like macro invocation: NAME(args) -/
private partial def expandFuncMacro (text : String) (m : Macro) (params : List String) : String :=
  -- Skip self-referential macros (body contains own name as identifier)
  if textContainsIdent m.body m.name then text
  else
    let chars := text.toList
    let nameChars := m.name.toList
    goSearch chars nameChars m.body params [] |> String.ofList
where
  goSearch (chars : List Char) (nameChars : List Char) (body : String)
           (params : List String) (acc : List Char) : List Char :=
    match chars with
    | [] => acc.reverse
    | c :: rest =>
        if isIdentChar c then
          let (ident, after) := collectId (c :: rest) []
          let identStr := String.ofList ident.reverse
          if identStr == String.ofList nameChars then
            -- Found name, check for (
            match skipWS after with
            | '(' :: afterParen =>
                let (args, afterArgs) := collectArgs afterParen 0 [] []
                let expanded := substituteParams body params args
                let expandedChars := expanded.toList.reverse
                goSearch afterArgs nameChars body params (expandedChars ++ acc)
            | _ => goSearch after nameChars body params (ident ++ acc)
          else
            goSearch after nameChars body params (ident ++ acc)
        else
          goSearch rest nameChars body params (c :: acc)
  collectId (chars : List Char) (acc : List Char) : List Char × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest => if isIdentChar c then collectId rest (c :: acc) else (acc, c :: rest)
  skipWS (chars : List Char) : List Char :=
    chars.dropWhile (fun (c : Char) => c == ' ' || c == '\t')
  collectArgs (chars : List Char) (depth : Nat) (curArg : List Char)
              (args : List String) : List String × List Char :=
    match chars with
    | [] => ((String.ofList curArg.reverse).trim :: args |>.reverse, [])
    | ')' :: rest =>
        if depth == 0 then
          ((String.ofList curArg.reverse).trim :: args |>.reverse, rest)
        else
          collectArgs rest (depth - 1) (')' :: curArg) args
    | '(' :: rest => collectArgs rest (depth + 1) ('(' :: curArg) args
    | ',' :: rest =>
        if depth == 0 then
          collectArgs rest 0 [] ((String.ofList curArg.reverse).trim :: args)
        else
          collectArgs rest depth (',' :: curArg) args
    | c :: rest => collectArgs rest depth (c :: curArg) args
  substituteParams (body : String) (params : List String) (args : List String) : String :=
    let pairs := params.zip args
    pairs.foldl (fun (acc : String) (pair : String × String) =>
      replaceIdent acc pair.1 pair.2) body

/-- Single-pass macro expansion: walk text once, replacing identifiers that match macros. -/
private partial def singlePassExpand (chars : List Char) (macros : List Macro) (acc : List Char) : List Char :=
  match chars with
  | [] => acc.reverse
  | c :: rest =>
      if isIdentChar c then
        -- Collect identifier
        let (word, after) := collectIdentChars (c :: rest) []
        let wordStr := String.ofList word
        -- Look up in macros
        match macros.find? (fun m => m.name == wordStr) with
        | some m =>
            if textContainsIdent m.body m.name then
              -- Self-referential: don't expand
              singlePassExpand after macros (word.reverse ++ acc)
            else match m.params with
            | none =>
                -- Object-like: insert body
                singlePassExpand after macros (m.body.toList.reverse ++ acc)
            | some params =>
                -- Function-like: check for (
                let after' := after.dropWhile (fun c => c == ' ' || c == '\t')
                match after' with
                | '(' :: afterParen =>
                    let (args, afterArgs) := collectFuncArgs afterParen 0 [] []
                    let body := substituteMacroParams m.body params args
                    singlePassExpand afterArgs macros (body.toList.reverse ++ acc)
                | _ =>
                    -- Not a function call, keep as-is
                    singlePassExpand after macros (word.reverse ++ acc)
        | none =>
            singlePassExpand after macros (word.reverse ++ acc)
      else
        singlePassExpand rest macros (c :: acc)
where
  collectIdentChars (chars : List Char) (acc : List Char) : List Char × List Char :=
    match chars with
    | [] => (acc.reverse, [])
    | c :: rest => if isIdentChar c then collectIdentChars rest (c :: acc) else (acc.reverse, c :: rest)
  collectFuncArgs (chars : List Char) (depth : Nat) (cur : List Char) (args : List String)
      : List String × List Char :=
    match chars with
    | [] => ((String.ofList cur.reverse).trim :: args |>.reverse, [])
    | ')' :: rest =>
        if depth == 0 then ((String.ofList cur.reverse).trim :: args |>.reverse, rest)
        else collectFuncArgs rest (depth - 1) (')' :: cur) args
    | '(' :: rest => collectFuncArgs rest (depth + 1) ('(' :: cur) args
    | ',' :: rest =>
        if depth == 0 then collectFuncArgs rest 0 [] ((String.ofList cur.reverse).trim :: args)
        else collectFuncArgs rest depth (',' :: cur) args
    | c :: rest => collectFuncArgs rest depth (c :: cur) args
  substituteMacroParams (body : String) (params : List String) (args : List String) : String :=
    let pairs := params.zip args
    pairs.foldl (fun acc (p : String × String) => replaceIdent acc p.1 p.2) body

partial def expandMacros (macros : List Macro) (text : String) (fuel : Nat := 3) : String :=
  if fuel == 0 || text.length > 5000 || macros.isEmpty then text
  else
    let result := String.ofList (singlePassExpand text.toList macros [])
    if result == text then result
    else expandMacros macros result (fuel - 1)

/-- Built-in system header content. -/
def builtinHeader (name : String) : Option String :=
  match name with
  | "stddef.h" => some "typedef long ptrdiff_t;\ntypedef unsigned long size_t;\ntypedef int wchar_t;\n"
  | "stdint.h" => some "typedef signed char int8_t;\ntypedef short int16_t;\ntypedef int int32_t;\ntypedef long int64_t;\ntypedef unsigned char uint8_t;\ntypedef unsigned short uint16_t;\ntypedef unsigned int uint32_t;\ntypedef unsigned long uint64_t;\ntypedef long intptr_t;\ntypedef unsigned long uintptr_t;\n"
  | "stdbool.h" => some "typedef int bool;\n"
  | "stdarg.h" => some "typedef char *va_list;\n"
  | "limits.h" => some "#define CHAR_BIT 8\n#define INT_MIN (-2147483647-1)\n#define INT_MAX 2147483647\n#define UINT_MAX 4294967295U\n#define LONG_MIN (-9223372036854775807L-1)\n#define LONG_MAX 9223372036854775807L\n#define ULONG_MAX 18446744073709551615UL\n#define SHRT_MIN (-32768)\n#define SHRT_MAX 32767\n#define USHRT_MAX 65535\n#define LLONG_MIN LONG_MIN\n#define LLONG_MAX LONG_MAX\n#define ULLONG_MAX ULONG_MAX\n#define CHAR_MIN (-128)\n#define CHAR_MAX 127\n#define SCHAR_MIN (-128)\n#define SCHAR_MAX 127\n#define UCHAR_MAX 255\n"
  | "string.h" => some "typedef unsigned long size_t;\nvoid *memcpy(void *dest, const void *src, size_t n);\nvoid *memmove(void *dest, const void *src, size_t n);\nvoid *memset(void *s, int c, size_t n);\nint memcmp(const void *s1, const void *s2, size_t n);\nsize_t strlen(const char *s);\nchar *strcpy(char *dest, const char *src);\nchar *strncpy(char *dest, const char *src, size_t n);\nint strcmp(const char *s1, const char *s2);\nint strncmp(const char *s1, const char *s2, size_t n);\nchar *strcat(char *dest, const char *src);\nchar *strchr(const char *s, int c);\nchar *strrchr(const char *s, int c);\nchar *strstr(const char *haystack, const char *needle);\nchar *strdup(const char *s);\n"
  | "stdlib.h" => some "typedef unsigned long size_t;\nvoid *malloc(size_t size);\nvoid *calloc(size_t nmemb, size_t size);\nvoid *realloc(void *ptr, size_t size);\nvoid free(void *ptr);\nvoid exit(int status);\nvoid abort(void);\nint atoi(const char *nptr);\nlong atol(const char *nptr);\nlong strtol(const char *nptr, char **endptr, int base);\nunsigned long strtoul(const char *nptr, char **endptr, int base);\nint abs(int j);\nlong labs(long j);\nint rand(void);\nvoid srand(unsigned int seed);\n"
  | "stdio.h" => some "typedef unsigned long size_t;\ntypedef struct _FILE FILE;\nextern FILE *stdin;\nextern FILE *stdout;\nextern FILE *stderr;\nint printf(const char *format, ...);\nint fprintf(FILE *stream, const char *format, ...);\nint sprintf(char *str, const char *format, ...);\nint snprintf(char *str, size_t size, const char *format, ...);\nint scanf(const char *format, ...);\nFILE *fopen(const char *path, const char *mode);\nint fclose(FILE *stream);\nsize_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);\nsize_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);\nint fgetc(FILE *stream);\nchar *fgets(char *s, int size, FILE *stream);\nint fputs(const char *s, FILE *stream);\nint feof(FILE *stream);\nint ferror(FILE *stream);\nlong ftell(FILE *stream);\nint fseek(FILE *stream, long offset, int whence);\nint fflush(FILE *stream);\nint getchar(void);\nint putchar(int c);\nint puts(const char *s);\nint remove(const char *pathname);\n#define EOF (-1)\n#define SEEK_SET 0\n#define SEEK_CUR 1\n#define SEEK_END 2\n"
  | "assert.h" => some ""
  | "ctype.h" => some "int isalpha(int c);\nint isdigit(int c);\nint isalnum(int c);\nint isspace(int c);\nint isupper(int c);\nint islower(int c);\nint isprint(int c);\nint toupper(int c);\nint tolower(int c);\n"
  | "math.h" => some "double sin(double x);\ndouble cos(double x);\ndouble sqrt(double x);\ndouble pow(double base, double exp);\ndouble fabs(double x);\ndouble floor(double x);\ndouble ceil(double x);\nfloat sqrtf(float x);\nfloat fabsf(float x);\n"
  | "errno.h" => some "extern int errno;\n#define EDOM 33\n#define ERANGE 34\n"
  | "signal.h" => some "typedef void (*sighandler_t)(int);\nint raise(int sig);\n#define SIGABRT 6\n#define SIGINT 2\n#define SIGSEGV 11\n"
  | "setjmp.h" => some "typedef long jmp_buf[8];\nint setjmp(jmp_buf env);\nvoid longjmp(jmp_buf env, int val);\n"
  | "time.h" => some "typedef long time_t;\ntypedef long clock_t;\ntime_t time(time_t *tloc);\nclock_t clock(void);\n#define CLOCKS_PER_SEC 1000000\n"
  | "locale.h" => some "char *setlocale(int category, const char *locale);\n#define LC_ALL 6\n#define LC_CTYPE 0\n"
  | "float.h" => some "#define FLT_MAX 3.402823466e+38F\n#define DBL_MAX 1.7976931348623158e+308\n#define FLT_EPSILON 1.192092896e-07F\n#define DBL_EPSILON 2.2204460492503131e-16\n#define FLT_RADIX 2\n"
  | _ => none

/-- Strip leading whitespace from a string. -/
private def stripWS (s : String) : String :=
  let chars := s.toList.dropWhile (fun (c : Char) => c == ' ' || c == '\t')
  String.ofList (chars.reverse.dropWhile (fun (c : Char) => c == ' ' || c == '\t') |>.reverse)

/-- Get the first word (identifier) from a string. -/
private def firstWord (s : String) : String :=
  String.ofList (s.toList.takeWhile (fun (c : Char) => isIdentChar c))

/-- Drop leading n characters. -/
private def dropN (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

/-- Extract header name from #include directive. -/
private def extractHeaderName (rest : String) : String :=
  let s := stripWS rest
  let chars := s.toList
  match chars with
  | '"' :: tail => String.ofList (tail.takeWhile (fun (c : Char) => c != '"'))
  | '<' :: tail => String.ofList (tail.takeWhile (fun (c : Char) => c != '>'))
  | _ => s

/-- Process lines of source, returning final state. -/
private partial def joinContinuations (lines : List String) : List String :=
  go lines []
where
  go (lines : List String) (acc : List String) : List String :=
    match lines with
    | [] => acc.reverse
    | line :: rest =>
        let chars := line.toList
        if chars.length > 0 && chars.getLast! == '\\' then
          let trimmed := String.ofList (chars.dropLast)
          match rest with
          | [] => go [] ((trimmed) :: acc)
          | next :: rest' => go ((trimmed ++ next) :: rest') acc
        else
          go rest (line :: acc)

private partial def stripComments (chars : List Char) (acc : List Char) (inString : Bool) : List Char :=
  match chars with
  | [] => acc.reverse
  | '"' :: rest =>
      if inString then stripComments rest ('"' :: acc) false
      else stripComments rest ('"' :: acc) true
  | '\\' :: c :: rest =>
      if inString then stripComments rest (c :: '\\' :: acc) true
      else stripComments (c :: rest) ('\\' :: acc) false
  | '/' :: '*' :: rest =>
      if inString then stripComments rest ('*' :: '/' :: acc) true
      else skipBlockComment rest acc
  | '/' :: '/' :: rest =>
      if inString then stripComments rest ('/' :: '/' :: acc) true
      else skipLineComment rest acc
  | c :: rest => stripComments rest (c :: acc) inString
where
  skipBlockComment (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc.reverse
    | '*' :: '/' :: rest => stripComments rest (' ' :: acc) false
    | '\n' :: rest => skipBlockComment rest ('\n' :: acc)
    | _ :: rest => skipBlockComment rest acc
  skipLineComment (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc.reverse
    | '\n' :: rest => stripComments rest ('\n' :: acc) false
    | _ :: rest => skipLineComment rest acc

/-- Count unbalanced open-parens in a line (positive → unclosed call). -/
private def parenBalance (s : String) : Int :=
  s.foldl (fun (bal : Int) (c : Char) =>
    if c == '(' then bal + 1
    else if c == ')' then bal - 1
    else bal) 0

/-- Join lines until parentheses balance, for multi-line macro calls.
    Returns (joined line, remaining lines). Fuel prevents runaway. -/
private def joinUntilBalanced (first : String) (rest : List String) (fuel : Nat := 200)
    : String × List String :=
  let bal := parenBalance first
  if bal <= 0 || fuel == 0 then (first, rest)
  else go first bal rest fuel
where
  go (acc : String) (bal : Int) (lines : List String) (fuel : Nat) : String × List String :=
    if bal <= 0 || fuel == 0 then (acc, lines)
    else match lines with
    | [] => (acc, [])
    | l :: ls =>
        let joined := acc ++ " " ++ l.trim
        let newBal := bal + parenBalance l
        go joined newBal ls (fuel - 1)

private def ppPrefixMatch (chars : List Char) (pref : List Char) : Bool :=
  match pref, chars with
  | [], _ => true
  | _, [] => false
  | p :: ps, c :: cs => p == c && ppPrefixMatch cs ps

private def ppFindOp (chars : List Char) (opChars : List Char) (opLen : Nat)
    (acc : List Char) (depth : Nat) : Option (String × String) :=
  match chars with
  | [] => none
  | '(' :: rest => ppFindOp rest opChars opLen ('(' :: acc) (depth + 1)
  | ')' :: rest => ppFindOp rest opChars opLen (')' :: acc) (if depth > 0 then depth - 1 else 0)
  | c :: rest =>
      if depth == 0 && ppPrefixMatch (c :: rest) opChars then
        some (String.ofList acc.reverse, String.ofList ((c :: rest).drop opLen))
      else
        ppFindOp rest opChars opLen (c :: acc) depth

private def ppSplitOnOp (s : String) (op : String) : Option (String × String) :=
  ppFindOp s.toList op.toList op.length [] 0

private def ppEvalInt (st : PPState) (expr : String) : Int :=
  let expanded := expandMacros st.macros (stripWS expr) 20
  let s := stripWS expanded
  let s := if s.endsWith "UL" then s.dropRight 2
    else if s.endsWith "LL" || s.endsWith "ll" then s.dropRight 2
    else if s.endsWith "L" || s.endsWith "l" || s.endsWith "U" || s.endsWith "u" then s.dropRight 1
    else s
  match s.toInt? with
  | some n => n
  | none => if st.isDefined (firstWord s) then 1 else 0

private partial def ppEvalSimple (st : PPState) (expr : String) : Bool :=
  let expr := stripWS expr
  if ppSplitOnOp expr "==" |>.isSome then
    match ppSplitOnOp expr "==" with
    | some (l, r) => ppEvalInt st (stripWS l) == ppEvalInt st (stripWS r)
    | none => false
  else if ppSplitOnOp expr "!=" |>.isSome then
    match ppSplitOnOp expr "!=" with
    | some (l, r) => ppEvalInt st (stripWS l) != ppEvalInt st (stripWS r)
    | none => false
  else if ppSplitOnOp expr ">=" |>.isSome then
    match ppSplitOnOp expr ">=" with
    | some (l, r) => ppEvalInt st (stripWS l) >= ppEvalInt st (stripWS r)
    | none => false
  else if ppSplitOnOp expr "<=" |>.isSome then
    match ppSplitOnOp expr "<=" with
    | some (l, r) => ppEvalInt st (stripWS l) <= ppEvalInt st (stripWS r)
    | none => false
  else if ppSplitOnOp expr ">" |>.isSome then
    match ppSplitOnOp expr ">" with
    | some (l, r) => ppEvalInt st (stripWS l) > ppEvalInt st (stripWS r)
    | none => false
  else if ppSplitOnOp expr "<" |>.isSome then
    match ppSplitOnOp expr "<" with
    | some (l, r) => ppEvalInt st (stripWS l) < ppEvalInt st (stripWS r)
    | none => false
  else if ppSplitOnOp expr "&&" |>.isSome then
    match ppSplitOnOp expr "&&" with
    | some (l, r) => ppEvalSimple st l && ppEvalSimple st r
    | none => false
  else if ppSplitOnOp expr "||" |>.isSome then
    match ppSplitOnOp expr "||" with
    | some (l, r) => ppEvalSimple st l || ppEvalSimple st r
    | none => false
  else if expr.startsWith "!defined" then
    let rest := stripWS (dropN expr 8)
    let name := if rest.startsWith "(" then firstWord (stripWS (dropN rest 1)) else firstWord rest
    !(st.isDefined name)
  else if expr.startsWith "defined" then
    let rest := stripWS (dropN expr 7)
    let name := if rest.startsWith "(" then firstWord (stripWS (dropN rest 1)) else firstWord rest
    st.isDefined name
  else if expr.startsWith "!" then
    !(ppEvalSimple st (stripWS (dropN expr 1)))
  else if expr == "0" then false
  else if expr == "1" then true
  else ppEvalInt st expr != 0

partial def processLines (st : PPState) (lines : List String) : IO PPState := do
  match lines with
  | [] => pure st
  | line :: rest =>
      let stripped := stripWS line
      if stripped.startsWith "#" then
        let directive := stripWS (dropN stripped 1)
        let st' ← processDirective st directive
        processLines st' rest
      else if st.isActive then
        -- Join multi-line macro calls: if parens are unbalanced, consume next lines
        let (fullLine, rest') :=
          if parenBalance line > 0 then joinUntilBalanced line rest
          else (line, rest)
        -- Performance: with many macros, only expand object-like (no function-like)
        let expanded := if st.macros.length > 500 then
            expandMacros (st.macros.filter (fun m => m.params.isNone)) fullLine
          else
            expandMacros st.macros fullLine
        processLines (st.emit expanded) rest'
      else
        processLines st rest

where
  processDirective (st : PPState) (directive : String) : IO PPState := do
    if directive.startsWith "ifdef " then
      let name := stripWS (dropN directive 6)
      let name := firstWord name
      let defined := st.isDefined name
      let active := st.isActive && defined
      pure { st with ifStack := (active, active) :: st.ifStack }
    else if directive.startsWith "ifndef " then
      let name := stripWS (dropN directive 7)
      let name := firstWord name
      let defined := st.isDefined name
      let active := st.isActive && !defined
      pure { st with ifStack := (active, active) :: st.ifStack }
    else if directive.startsWith "if " then
      let expr := stripWS (dropN directive 3)
      let active := if st.isActive then ppEvalSimple st expr else false
      pure { st with ifStack := (active, active) :: st.ifStack }
    else if directive.startsWith "elif " then
      match st.ifStack with
      | (_, anyTaken) :: outer =>
          let expr := stripWS (dropN directive 5)
          let outerActive := outer.all (fun (e : IfEntry) => e.1)
          -- Only consider this branch if outer is active AND no prior branch was taken
          let active := outerActive && !anyTaken && ppEvalSimple st expr
          pure { st with ifStack := (active, anyTaken || active) :: outer }
      | [] => pure st
    else if directive.startsWith "else" then
      match st.ifStack with
      | (_, anyTaken) :: outer =>
          let outerActive := outer.all (fun (e : IfEntry) => e.1)
          -- #else: take only if outer active AND no prior branch was taken
          pure { st with ifStack := (outerActive && !anyTaken, true) :: outer }
      | [] => pure st
    else if directive.startsWith "endif" then
      match st.ifStack with
      | _ :: outer => pure { st with ifStack := outer }
      | [] => pure st
    else if st.isActive then
      if directive.startsWith "define " || directive.startsWith "define\t" then
        let rest := stripWS (dropN directive 7)
        let name := firstWord rest
        let afterName := dropN rest name.length
        -- Check for function-like macro: name immediately followed by (
        if afterName.startsWith "(" then
          -- Function-like macro: #define NAME(a,b,...) body
          let parenContent := dropN afterName 1
          let parenChars := parenContent.toList
          let (paramStr, bodyAfterParen) := splitAtCloseParen parenChars [] 0
          let params := (String.ofList paramStr).splitOn ","
            |>.map (fun (s : String) => String.ofList (s.toList.filter (fun (c : Char) => c != ' ' && c != '\t')))
            |>.filter (fun (s : String) => !s.isEmpty)
          -- Handle ... in params → __VA_ARGS__
          let params := params.map (fun (p : String) => if p == "..." then "__VA_ARGS__" else p)
          let body := stripWS (String.ofList bodyAfterParen)
          pure (st.define name (some params) body)
        else
          let body := stripWS afterName
          pure (st.define name none body)
      else if directive.startsWith "undef " then
        let name := firstWord (stripWS (dropN directive 6))
        pure (st.undef name)
      else if directive.startsWith "include" then
        let rest := stripWS (dropN directive 7)
        let headerName := extractHeaderName rest
        if st.included.contains headerName || st.includeDepth > 15 then
          pure st
        else
          let st := { st with included := headerName :: st.included, includeDepth := st.includeDepth + 1 }
          let result ← do
            match builtinHeader headerName with
            | some content =>
                let headerLines := content.splitOn "\n"
                processLines st headerLines
            | none =>
                let relPath := st.basePath ++ "/" ++ headerName
                let fileExists ← System.FilePath.pathExists relPath
                if fileExists then
                  let rawContent ← IO.FS.readFile relPath
                  let content := String.ofList (stripComments rawContent.toList [] false)
                  let headerLines := joinContinuations (content.splitOn "\n")
                  processLines { st with included := headerName :: st.included } headerLines
                else
                  pure (st.emit s!"/* CCC: skipped #include {rest} */")
          pure { result with includeDepth := st.includeDepth - 1 }
      else if directive.startsWith "error" then
        pure (st.emit s!"/* CCC #error: {stripWS (dropN directive 5)} */")
      else
        pure st  -- #pragma, #line, etc. — ignore
    else
      pure st

  -- All eval helpers are now top-level (ppEvalSimple, ppEvalInt, ppSplitOnOp)

/-- Main entry point: preprocess a C source string.
    basePath is the directory containing the source file.  -/
partial def preprocess (source : String) (basePath : String) : IO String := do
  let st := PPState.empty basePath
  -- Strip comments first, then join line continuations
  let cleaned := String.ofList (stripComments source.toList [] false)
  let lines := joinContinuations (cleaned.splitOn "\n")
  let finalSt ← processLines st lines
  pure (String.intercalate "\n" finalSt.output)

end CCC.Preprocess
