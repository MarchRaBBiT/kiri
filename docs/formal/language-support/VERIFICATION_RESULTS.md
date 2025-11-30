# Language Support Architecture - Formal Verification Results

## Summary

| Plan                                    | Alloy                              | TLA+                       | Status              |
| --------------------------------------- | ---------------------------------- | -------------------------- | ------------------- |
| **Plan A**: Central Registry            | ✅ All 4 assertions pass           | ⏸️ Type annotations needed | Recommended         |
| **Plan B**: Hierarchical Backend + Pool | ✅ All 4 assertions pass           | ⏸️ Type annotations needed | Recommended for LSP |
| **Plan C**: Capability Composition      | ⚠️ 1 violation (NoOrphanProviders) | ⏸️ Type annotations needed | Needs fix           |

## Alloy Verification Details

### Plan A: Central Registry + Thin Abstraction

```
00. run   showValidRegistry        SAT (valid instance found)
01. run   showFileLocking          SAT (valid instance found)
02. check NoConflictingAnalyzers   UNSAT (✅ no counterexample)
03. check DeterministicLookup      UNSAT (✅ no counterexample)
04. check LockConsistency          UNSAT (✅ no counterexample)
05. check NoDeadlock               UNSAT (✅ no counterexample)
```

**Key Properties Verified:**

- Each language has at most one registered analyzer
- Registry lookup is deterministic
- File locks require language match
- No deadlock with file-level locking

### Plan B: Hierarchical Backend + Pool

```
00. run   showPooledSystem         SAT (valid instance found)
01. run   showMultiplePools        SAT (valid instance found)
02. check PoolNeverOverflows       UNSAT (✅ no counterexample)
03. check AvailableClientsNoLocks  UNSAT (✅ no counterexample)
04. check FileLockConsistent       UNSAT (✅ no counterexample)
05. check ConcurrentProcessing     UNSAT (✅ no counterexample)
```

**Key Properties Verified:**

- Pool size never exceeds maximum
- Available clients don't hold locks
- File lock consistency (in_use state + language match)
- Concurrent processing possible for different languages

### Plan C: Capability Composition

```
00. run   showComposedAnalyzer     SAT (valid instance found)
01. run   showMultipleAnalyzers    SAT (valid instance found)
02. check MinimumCapabilityGuaranteed  UNSAT (✅ no counterexample)
03. check CapabilityTraceability   UNSAT (✅ no counterexample)
04. check FileLockConsistent       UNSAT (✅ no counterexample)
05. check CapabilityCompleteness   UNSAT (✅ no counterexample)
06. check NoOrphanProviders        SAT (❌ counterexample found!)
```

**Issue Found:**
`NoOrphanProviders` violation - Providers can exist without being attached to any analyzer. This indicates a lifecycle management gap.

**Fix Required:**
Add a constraint: every provider must be referenced by at least one analyzer, OR track provider lifecycle separately.

## TLA+ Verification Status

TLA+ specifications were created for all 3 plans but require Apalache-specific type annotations:

- `PlanA_CentralRegistry.tla` - Locking protocol model
- `PlanB_Pool.tla` - Pool-based client management
- `PlanC_Capability.tla` - Capability composition protocol

**To run TLA+ verification:**

```bash
# Add type annotations (@type) to CONSTANTS and VARIABLES
# Then run:
apalache-mc check --features=no-rows docs/formal/language-support/PlanA_CentralRegistry.tla
```

## Recommendations

### Primary: Plan A + Pool Helpers

Based on verification results:

1. **Use Plan A** (Central Registry) as the core architecture
   - All structural properties verified
   - Simple and deterministic

2. **Incorporate Plan B's pooling** for LSP backends (Dart)
   - Pool management is formally verified
   - Supports concurrent analysis

3. **Fix Plan C's orphan issue** if using capability composition
   - Add explicit lifecycle management
   - Track provider → analyzer dependencies

### Implementation Priority

1. Refactor `codeintel.ts` using Central Registry pattern
2. Keep existing `dart/` pooled architecture
3. Add `LanguageAnalyzer` interface with:
   - `language: Language`
   - `backend: BackendType`
   - `capabilities: Set<Capability>`
4. Implement file-level locking for mutual exclusion

## Files

- `PlanA_CentralRegistry.als` - Alloy spec (verified ✅)
- `PlanB_HierarchicalBackend.als` - Alloy spec (verified ✅)
- `PlanC_CapabilityComposition.als` - Alloy spec (1 issue ⚠️)
- `PlanA_CentralRegistry.tla` - TLA+ spec (needs type annotations)
- `PlanB_Pool.tla` - TLA+ spec (needs type annotations)
- `PlanC_Capability.tla` - TLA+ spec (needs type annotations)
