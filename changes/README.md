# CCC Schema Change Protocol

## When to use

If a feature agent or backend agent discovers that a shared type
(AST constructors, IR types, PtrState types) needs modification,
they MUST NOT modify shared files directly.

Instead:

1. Create `ccc/changes/SCHEMA-CHANGE-NNN.md` with:
   - What type needs changing
   - Current shape vs needed shape
   - Which feature/backend needs it
   - Proposed constructor signature

2. Do NOT modify any file outside your `Features/X/` or `Backend/X/` directory.

3. The orchestrator (or integration agent) will:
   - Review the change request
   - Apply it to the shared files
   - Update ALL match sites
   - Merge to trunk

## File naming

```
SCHEMA-CHANGE-001.md
SCHEMA-CHANGE-002.md
...
```

## Expected frequency

1-3 changes over the entire CCC20 sprint.

## Shared files (FROZEN after CCC08)

These files are frozen after EPIC-CCC08 completes:
- `CCC/Syntax/AST.lean` — all Expr/Stmt/CType constructors
- `CCC/Syntax/PtrState.lean` — all evidence/verification types
- `CCC/IR/IR.lean` — all IR instruction types
- `CCC/Verify/BoundsCheck.lean` — match sites
- `CCC/Verify/PointerSafety.lean` — match sites
- `CCC/Verify/NullCheck.lean` — match sites
- `CCC/Verify/BranchAnalysis.lean` — match sites
- `CCC/Verify/SymbolCheck.lean` — match sites
- `CCC/Verify/Verify.lean` — match sites
- `CCC/Verify/TypeSize.lean` — match sites
- `CCC/Emit/EmitX86.lean` — match sites
- `CCC/Parse/Parse.lean` — match sites

Feature agents work ONLY in `CCC/Features/X/`.
Backend agents work ONLY in `CCC/Backend/X/`.
