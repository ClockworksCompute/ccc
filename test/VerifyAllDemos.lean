import CCC

open CCC
open CCC.Syntax
open CCC.Syntax.Build

namespace VerifyAllDemos

-- ─────────────────────────────────────────────────────────────
-- Demo 1: heartbleed_mini.c (REJECT)
-- ─────────────────────────────────────────────────────────────

def heartbeatRequest : StructDef :=
  structDef "HeartbeatRequest"
    [("payload_length", .int), ("payload", .array .char 64)]

def heartbeatResponse : StructDef :=
  structDef "HeartbeatResponse"
    [("payload_length", .int), ("payload", .array .char 64)]

def processHeartbeatMini : FunDef :=
  funDef "process_heartbeat" .int
    [ param "request" (.pointer (.struct_ "HeartbeatRequest"))
    , param "response" (.pointer (.struct_ "HeartbeatResponse"))
    ]
    [ exprStmt
        (assign
          (arrow (var "response") "payload_length")
          (arrow (var "request") "payload_length"))
    , exprStmt
        (memcpy
          (arrow (var "response") "payload")
          (arrow (var "request") "payload")
          (arrow (var "request") "payload_length"))
    , retVal (intLit 0)
    ]

def heartbleedMiniAST : Program :=
  program [heartbeatRequest, heartbeatResponse] [processHeartbeatMini]

-- ─────────────────────────────────────────────────────────────
-- Demo 2: heartbleed_fixed.c (ACCEPT)
-- ─────────────────────────────────────────────────────────────

def processHeartbeatFixed : FunDef :=
  funDef "process_heartbeat" .int
    [ param "request" (.pointer (.struct_ "HeartbeatRequest"))
    , param "response" (.pointer (.struct_ "HeartbeatResponse"))
    ]
    [ ifElse
        (or_
          (lt (arrow (var "request") "payload_length") (intLit 0))
          (gt (arrow (var "request") "payload_length") (intLit 64)))
        [retVal (intLit (-1))]
        []
    , exprStmt
        (assign
          (arrow (var "response") "payload_length")
          (arrow (var "request") "payload_length"))
    , exprStmt
        (memcpy
          (arrow (var "response") "payload")
          (arrow (var "request") "payload")
          (arrow (var "request") "payload_length"))
    , retVal (intLit 0)
    ]

def heartbleedFixedAST : Program :=
  program [heartbeatRequest, heartbeatResponse] [processHeartbeatFixed]

-- ─────────────────────────────────────────────────────────────
-- Demo 3: buffer_overflow.c (REJECT)
-- ─────────────────────────────────────────────────────────────

def bufferOverflowMain : FunDef :=
  funDef "main" .int []
    [ varDecl "scores" (.array .int 5)
    , exprStmt (assign (index (var "scores") (intLit 0)) (intLit 95))
    , exprStmt (assign (index (var "scores") (intLit 1)) (intLit 87))
    , exprStmt (assign (index (var "scores") (intLit 2)) (intLit 92))
    , exprStmt (assign (index (var "scores") (intLit 3)) (intLit 78))
    , exprStmt (assign (index (var "scores") (intLit 4)) (intLit 88))
    , exprStmt (assign (index (var "scores") (intLit 5)) (intLit 100))
    , varInit "sum" .int (intLit 0)
    , varInit "i" .int (intLit 0)
    , while_ (lt (var "i") (intLit 5))
        [ exprStmt
            (assign (var "sum")
              (add (var "sum") (index (var "scores") (var "i"))))
        , exprStmt (assign (var "i") (add (var "i") (intLit 1)))
        ]
    , retVal (var "sum")
    ]

def bufferOverflowAST : Program :=
  program [] [bufferOverflowMain]

-- ─────────────────────────────────────────────────────────────
-- Demo 4: use_after_free.c (REJECT)
-- ─────────────────────────────────────────────────────────────

def userStruct : StructDef :=
  structDef "User" [("id", .int), ("permissions", .int)]

def useAfterFreeMain : FunDef :=
  funDef "main" .int []
    [ varInit "alice" (.pointer (.struct_ "User"))
        (malloc (sizeOf (.struct_ "User")))
    , ifElse (eq (var "alice") (intLit 0)) [retVal (intLit (-1))] []
    , exprStmt (assign (arrow (var "alice") "id") (intLit 42))
    , exprStmt (assign (arrow (var "alice") "permissions") (intLit 1))
    , exprStmt (free (var "alice"))
    , varInit "id" .int (arrow (var "alice") "id")
    , retVal (var "id")
    ]

def useAfterFreeAST : Program :=
  program [userStruct] [useAfterFreeMain]

-- ─────────────────────────────────────────────────────────────
-- Demo 5: double_free.c (REJECT)
-- ─────────────────────────────────────────────────────────────

def doubleFreeMain : FunDef :=
  funDef "main" .int []
    [ varInit "data" (.pointer .int)
        (malloc (mul (intLit 10) (sizeOf .int)))
    , ifElse (eq (var "data") (intLit 0)) [retVal (intLit (-1))] []
    , exprStmt (assign (index (var "data") (intLit 0)) (intLit 42))
    , exprStmt (assign (index (var "data") (intLit 9)) (intLit 99))
    , exprStmt (free (var "data"))
    , exprStmt (free (var "data"))
    , retVal (intLit 0)
    ]

def doubleFreeAST : Program :=
  program [] [doubleFreeMain]

-- ─────────────────────────────────────────────────────────────
-- Demo 6: null_deref.c (REJECT)
-- ─────────────────────────────────────────────────────────────

def configStruct : StructDef :=
  structDef "Config"
    [("max_connections", .int), ("timeout_ms", .int), ("buffer_size", .int)]

def nullDerefMain : FunDef :=
  funDef "main" .int []
    [ varInit "config" (.pointer (.struct_ "Config"))
        (malloc (sizeOf (.struct_ "Config")))
    , exprStmt (assign (arrow (var "config") "max_connections") (intLit 100))
    , retVal (arrow (var "config") "max_connections")
    ]

def nullDerefAST : Program :=
  program [configStruct] [nullDerefMain]

-- ─────────────────────────────────────────────────────────────
-- Demo 7: safe_server.c (ACCEPT)
-- ─────────────────────────────────────────────────────────────

def messageStruct : StructDef :=
  structDef "Message"
    [("type", .int), ("length", .int), ("data", .array .char 256)]

def responseStruct : StructDef :=
  structDef "Response"
    [("status", .int), ("length", .int), ("data", .array .char 256)]

def handleMessage : FunDef :=
  funDef "handle_message" .int
    [ param "msg" (.pointer (.struct_ "Message"))
    , param "resp" (.pointer (.struct_ "Response"))
    ]
    [ ifElse
        (or_
          (lt (arrow (var "msg") "length") (intLit 0))
          (gt (arrow (var "msg") "length") (intLit 256)))
        [ exprStmt (assign (arrow (var "resp") "status") (intLit (-1)))
        , exprStmt (assign (arrow (var "resp") "length") (intLit 0))
        , retVal (intLit (-1))
        ]
        []
    , exprStmt (assign (arrow (var "resp") "status") (intLit 0))
    , exprStmt (assign (arrow (var "resp") "length") (arrow (var "msg") "length"))
    , exprStmt
        (memcpy
          (arrow (var "resp") "data")
          (arrow (var "msg") "data")
          (arrow (var "msg") "length"))
    , retVal (intLit 0)
    ]

def countBytes : FunDef :=
  funDef "count_bytes" .int
    [param "buf" (.pointer .char), param "size" .int, param "target" .char]
    [ varInit "count" .int (intLit 0)
    , varInit "i" .int (intLit 0)
    , while_ (lt (var "i") (var "size"))
        [ ifElse
            (eq (index (var "buf") (var "i")) (var "target"))
            [exprStmt (assign (var "count") (add (var "count") (intLit 1)))]
            []
        , exprStmt (assign (var "i") (add (var "i") (intLit 1)))
        ]
    , retVal (var "count")
    ]

def safeServerMain : FunDef :=
  funDef "main" .int []
    [ varDecl "msg" (.struct_ "Message")
    , varDecl "resp" (.struct_ "Response")
    , exprStmt (assign (member (var "msg") "type") (intLit 1))
    , exprStmt (assign (member (var "msg") "length") (intLit 5))
    , exprStmt (assign (index (member (var "msg") "data") (intLit 0)) (intLit 72))
    , exprStmt (assign (index (member (var "msg") "data") (intLit 1)) (intLit 101))
    , exprStmt (assign (index (member (var "msg") "data") (intLit 2)) (intLit 108))
    , exprStmt (assign (index (member (var "msg") "data") (intLit 3)) (intLit 108))
    , exprStmt (assign (index (member (var "msg") "data") (intLit 4)) (intLit 111))
    , varInit "result" .int
        (call "handle_message" [addrOf (var "msg"), addrOf (var "resp")])
    , ifElse (ne (var "result") (intLit 0)) [retVal (intLit 1)] []
    , varInit "counters" (.pointer .int)
        (malloc (mul (intLit 4) (sizeOf .int)))
    , ifElse (eq (var "counters") (intLit 0)) [retVal (intLit 1)] []
    , exprStmt
        (assign
          (index (var "counters") (intLit 0))
          (call "count_bytes"
            [member (var "resp") "data", member (var "resp") "length", intLit 108]))
    , exprStmt (assign (index (var "counters") (intLit 1)) (member (var "resp") "length"))
    , exprStmt (assign (index (var "counters") (intLit 2)) (member (var "resp") "status"))
    , exprStmt (assign (index (var "counters") (intLit 3)) (intLit 0))
    , exprStmt (free (var "counters"))
    , retVal (intLit 0)
    ]

def safeServerAST : Program :=
  program [messageStruct, responseStruct] [handleMessage, countBytes, safeServerMain]

-- ─────────────────────────────────────────────────────────────
-- Runner
-- ─────────────────────────────────────────────────────────────

def runOne (name : String) (prog : Program) (shouldAccept : Bool) : IO Unit := do
  match CCC.verifyProgram prog with
  | .ok _ =>
      if shouldAccept then
        IO.println s!"✓ {name}: ACCEPTED"
      else
        IO.println s!"✗ {name}: expected reject, got accept"
        IO.Process.exit 1
  | .error violations =>
      if shouldAccept then
        IO.println s!"✗ {name}: expected accept, got reject"
        for v in violations do
          IO.println s!"  violation: {v.message}"
        IO.Process.exit 1
      else
        IO.println s!"✓ {name}: REJECTED"

def main : IO Unit := do
  let tests : List (String × Program × Bool) :=
    [ ("heartbleed_mini", heartbleedMiniAST, false)
    , ("heartbleed_fixed", heartbleedFixedAST, true)
    , ("buffer_overflow", bufferOverflowAST, false)
    , ("use_after_free", useAfterFreeAST, false)
    , ("double_free", doubleFreeAST, false)
    , ("null_deref", nullDerefAST, false)
    , ("safe_server", safeServerAST, true)
    ]
  for (name, prog, shouldAccept) in tests do
    runOne name prog shouldAccept
  IO.println "All 7 demos verified correctly."

end VerifyAllDemos

def main : IO Unit :=
  VerifyAllDemos.main
